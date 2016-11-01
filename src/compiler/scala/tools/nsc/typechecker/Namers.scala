/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package typechecker

import scala.annotation.tailrec
import scala.collection.mutable
import symtab.Flags._
import scala.language.postfixOps
import scala.reflect.internal.util.ListOfNil

/** This trait declares methods to create symbols and to enter them into scopes.
 *
 *  @author Martin Odersky
 *  @version 1.0
 */
trait Namers extends MethodSynthesis {
  self: Analyzer =>

  import global._
  import definitions._

  var _lockedCount = 0
  def lockedCount = this._lockedCount

  /** Replaces any Idents for which cond is true with fresh TypeTrees().
   *  Does the same for any trees containing EmptyTrees.
   */
  private class TypeTreeSubstituter(cond: Name => Boolean) extends Transformer {
    override def transform(tree: Tree): Tree = tree match {
      case Ident(name) if cond(name) => TypeTree()
      case _                         => super.transform(tree)
    }
    def apply(tree: Tree) = {
      val r = transform(tree)
      if (r exists { case tt: TypeTree => tt.isEmpty case _ => false })
        TypeTree()
      else r
    }
  }

  private def isTemplateContext(ctx: Context): Boolean = ctx.tree match {
    case Template(_, _, _) => true
    case Import(_, _)      => isTemplateContext(ctx.outer)
    case _                 => false
  }

  private class NormalNamer(context: Context) extends Namer(context)
  def newNamer(context: Context): Namer = new NormalNamer(context)

  abstract class Namer(val context: Context) extends MethodSynth with NamerContextErrors { thisNamer =>
    // overridden by the presentation compiler
    def saveDefaultGetter(meth: Symbol, default: Symbol) { }

    import NamerErrorGen._
    val typer = newTyper(context)

    private lazy val innerNamer =
      if (isTemplateContext(context)) createInnerNamer() else this

    // Cached as a val because `settings.isScala212` parses the Scala version each time...
    // Not in Namers because then we need to go to outer first to check this.
    // I do think it's ok to check every time we create a Namer instance (so, not a lazy val).
    private[this] val isScala212 = settings.isScala212

    def createNamer(tree: Tree): Namer = {
      val sym = tree match {
        case ModuleDef(_, _, _) => tree.symbol.moduleClass
        case _                  => tree.symbol
      }
      def isConstrParam(vd: ValDef) = {
        (sym hasFlag PARAM | PRESUPER) &&
        !vd.mods.isJavaDefined &&
        sym.owner.isConstructor
      }
      val ownerCtx = tree match {
        case vd: ValDef if isConstrParam(vd) =>
          context.makeConstructorContext
        case _ =>
          context
      }
      newNamer(ownerCtx.makeNewScope(tree, sym))
    }
    def createInnerNamer() = {
      newNamer(context.make(context.tree, owner, newScope))
    }
    def createPrimaryConstructorParameterNamer: Namer = { //todo: can we merge this with SCCmode?
      val classContext = context.enclClass
      val outerContext = classContext.outer.outer
      val paramContext = outerContext.makeNewScope(outerContext.tree, outerContext.owner)

      owner.unsafeTypeParams foreach (paramContext.scope enter _)
      newNamer(paramContext)
    }

    def enclosingNamerWithScope(scope: Scope) = {
      var cx = context
      while (cx != NoContext && cx.scope != scope) cx = cx.outer
      if (cx == NoContext || cx == context) thisNamer
      else newNamer(cx)
    }

    def enterValueParams(vparamss: List[List[ValDef]]): List[List[Symbol]] = {
      mmap(vparamss) { param =>
        val sym = assignSymbol(param, param.name, mask = ValueParameterFlags)
        setPrivateWithin(param, sym)
        enterInScope(sym)
        sym setInfo monoTypeCompleter(param)
      }
    }

    protected def owner       = context.owner
    def contextFile = context.unit.source.file
    def typeErrorHandler[T](tree: Tree, alt: T): PartialFunction[Throwable, T] = {
      case ex: TypeError =>
        // H@ need to ensure that we handle only cyclic references
        TypeSigError(tree, ex)
        alt
    }

    // All lazy vals need accessors, including those owned by terms (e.g., in method) or private[this] in a class
    def deriveAccessors(vd: ValDef) = (vd.mods.isLazy || owner.isTrait || (owner.isClass && deriveAccessorsInClass(vd)))

    private def deriveAccessorsInClass(vd: ValDef) =
      !vd.mods.isPrivateLocal && // note, private[this] lazy vals do get accessors -- see outer disjunction of deriveAccessors
      !(vd.name startsWith nme.OUTER) && // outer accessors are added later, in explicitouter
      !isEnumConstant(vd)                // enums can only occur in classes, so only check here


    /** Determines whether this field holds an enum constant.
      * To qualify, the following conditions must be met:
      *  - The field's class has the ENUM flag set
      *  - The field's class extends java.lang.Enum
      *  - The field has the ENUM flag set
      *  - The field is static
      *  - The field is stable
      */
    def isEnumConstant(vd: ValDef) = {
      val ownerHasEnumFlag =
        // Necessary to check because scalac puts Java's static members into the companion object
        // while Scala's enum constants live directly in the class.
        // We don't check for clazz.superClass == JavaEnumClass, because this causes a illegal
        // cyclic reference error. See the commit message for details.
        if (context.unit.isJava) owner.companionClass.hasJavaEnumFlag else owner.hasJavaEnumFlag
      vd.mods.hasAllFlags(JAVA_ENUM | STABLE | STATIC) && ownerHasEnumFlag
    }

    def setPrivateWithin[T <: Symbol](tree: Tree, sym: T, mods: Modifiers): T =
      if (sym.isPrivateLocal || !mods.hasAccessBoundary) sym
      else sym setPrivateWithin typer.qualifyingClass(tree, mods.privateWithin, packageOK = true)

    def setPrivateWithin(tree: MemberDef, sym: Symbol): Symbol =
      setPrivateWithin(tree, sym, tree.mods)

    def inConstructorFlag: Long = {
      val termOwnedContexts: List[Context] =
        context.enclosingContextChain.takeWhile(c => c.owner.isTerm && !c.owner.isAnonymousFunction)
      val constructorNonSuffix = termOwnedContexts exists (c => c.owner.isConstructor && !c.inConstructorSuffix)
      val earlyInit            = termOwnedContexts exists (_.owner.isEarlyInitialized)
      if (constructorNonSuffix || earlyInit) INCONSTRUCTOR else 0L
    }

    def moduleClassFlags(moduleFlags: Long) =
      (moduleFlags & ModuleToClassFlags) | inConstructorFlag

    def updatePosFlags(sym: Symbol, pos: Position, flags: Long): Symbol = {
      debuglog("[overwrite] " + sym)
      val newFlags = (sym.flags & LOCKED) | flags
      // !!! needed for: pos/t5954d; the uniques type cache will happily serve up the same TypeRef
      // over this mutated symbol, and we witness a stale cache for `parents`.
      invalidateCaches(sym.rawInfo, sym :: sym.moduleClass :: Nil)
      sym reset NoType setFlag newFlags setPos pos
      sym.moduleClass andAlso (updatePosFlags(_, pos, moduleClassFlags(flags)))

      if (sym.isTopLevel) {
        companionSymbolOf(sym, context) andAlso { companion =>
          val assignNoType = companion.rawInfo match {
            case _: SymLoader => true
            case tp           => tp.isComplete && (runId(sym.validTo) != currentRunId)
          }
          // pre-set linked symbol to NoType, in case it is not loaded together with this symbol.
          if (assignNoType)
            companion setInfo NoType
        }
      }
      sym
    }
    def namerOf(sym: Symbol): Namer = {
      val usePrimary = sym.isTerm && (
           (sym.isParamAccessor)
        || (sym.isParameter && sym.owner.isPrimaryConstructor)
      )

      if (usePrimary) createPrimaryConstructorParameterNamer
      else innerNamer
    }

    // FIXME - this logic needs to be thoroughly explained
    // and justified.  I know it's wrong with respect to package
    // objects, but I think it's also wrong in other ways.
    protected def conflict(newS: Symbol, oldS: Symbol) = (
       (   !oldS.isSourceMethod
        || nme.isSetterName(newS.name)
        || newS.isTopLevel
       ) &&
      !(   // @M: allow repeated use of `_` for higher-order type params
           (newS.owner.isTypeParameter || newS.owner.isAbstractType)
           // FIXME: name comparisons not successful, are these underscores
           // sometimes nme.WILDCARD and sometimes tpnme.WILDCARD?
        && (newS.name string_== nme.WILDCARD)
       )
    )

    private def allowsOverload(sym: Symbol) = (
      sym.isSourceMethod && sym.owner.isClass && !sym.isTopLevel
    )

    private def inCurrentScope(m: Symbol): Boolean = {
      if (owner.isClass) owner == m.owner
      else m.owner.isClass && context.scope == m.owner.info.decls
    }

    /** Enter symbol into context's scope and return symbol itself */
    def enterInScope(sym: Symbol): Symbol = enterInScope(sym, context.scope)

    /** Enter symbol into given scope and return symbol itself */
    def enterInScope(sym: Symbol, scope: Scope): Symbol = {
      // FIXME - this is broken in a number of ways.
      //
      // 1) If "sym" allows overloading, that is not itself sufficient to skip
      // the check, because "prev.sym" also must allow overloading.
      //
      // 2) There is nothing which reconciles a package's scope with
      // the package object's scope.  This is the source of many bugs
      // with e.g. defining a case class in a package object.  When
      // compiling against classes, the class symbol is created in the
      // package and in the package object, and the conflict is undetected.
      // There is also a non-deterministic outcome for situations like
      // an object with the same name as a method in the package object.

      // allow for overloaded methods
      if (!allowsOverload(sym)) {
        val prev = scope.lookupEntry(sym.name)
        if ((prev ne null) && prev.owner == scope && conflict(sym, prev.sym)) {
          if (sym.isSynthetic || prev.sym.isSynthetic) {
            handleSyntheticNameConflict(sym, prev.sym)
            handleSyntheticNameConflict(prev.sym, sym)
          }
          DoubleDefError(sym, prev.sym)
          sym setInfo ErrorType
          scope unlink prev.sym // let them co-exist...
          // FIXME: The comment "let them co-exist" is confusing given that the
          // line it comments unlinks one of them.  What does it intend?
        }
      }
      scope enter sym
    }

    /** Logic to handle name conflicts of synthetically generated symbols
     *  We handle right now: t6227
     */
    def handleSyntheticNameConflict(sym1: Symbol, sym2: Symbol) = {
      if (sym1.isImplicit && sym1.isMethod && sym2.isModule && sym2.companionClass.isCaseClass)
        validate(sym2.companionClass)
    }

    def enterSym(tree: Tree): Context = pluginsEnterSym(this, tree)

    /** Default implementation of `enterSym`.
     *  Can be overridden by analyzer plugins (see AnalyzerPlugins.pluginsEnterSym for more details)
     */
    def standardEnterSym(tree: Tree): Context = {
      def dispatch() = {
        var returnContext = this.context
        tree match {
          case tree @ PackageDef(_, _)                       => enterPackage(tree)
          case tree @ ClassDef(_, _, _, _)                   => enterClassDef(tree)
          case tree @ ModuleDef(_, _, _)                     => enterModuleDef(tree)
          case tree @ ValDef(_, _, _, _)                     => enterValDef(tree)
          case tree @ DefDef(_, _, _, _, _, _)               => enterDefDef(tree)
          case tree @ TypeDef(_, _, _, _)                    => enterTypeDef(tree)
          case DocDef(_, defn)                               => enterSym(defn)
          case tree @ Import(_, _)                           =>
            assignSymbol(tree)
            returnContext = context.make(tree)
          case _ =>
        }
        returnContext
      }
      tree.symbol match {
        case NoSymbol => try dispatch() catch typeErrorHandler(tree, this.context)
        case sym      => enterExistingSym(sym, tree)
      }
    }

    /** Creates a new symbol and assigns it to the tree, returning the symbol
     */
    def assignSymbol(tree: Tree): Symbol =
      logAssignSymbol(tree, tree match {
        case PackageDef(pid, _) => createPackageSymbol(tree.pos, pid)
        case imp: Import        => createImportSymbol(imp)
        case mdef: MemberDef    => createMemberSymbol(mdef, mdef.name, -1L)
        case _                  => abort("Unexpected tree: " + tree)
      })
    def assignSymbol(tree: MemberDef, name: Name, mask: Long): Symbol =
      logAssignSymbol(tree, createMemberSymbol(tree, name, mask))

    def assignAndEnterSymbol(tree: MemberDef): Symbol = {
      val sym = assignSymbol(tree, tree.name, -1L)
      setPrivateWithin(tree, sym)
      enterInScope(sym)
    }
    def assignAndEnterFinishedSymbol(tree: MemberDef): Symbol = {
      val sym = assignAndEnterSymbol(tree)
      sym setInfo completerOf(tree)
      // log("[+info] " + sym.fullLocationString)
      sym
    }

    def createMethod(accessQual: MemberDef, name: TermName, pos: Position, flags: Long): MethodSymbol = {
      val sym = owner.newMethod(name, pos, flags)
      setPrivateWithin(accessQual, sym)
      sym
    }

    private def logAssignSymbol(tree: Tree, sym: Symbol): Symbol = {
      if (isPastTyper) sym.name.toTermName match {
        case nme.IMPORT | nme.OUTER | nme.ANON_CLASS_NAME | nme.ANON_FUN_NAME | nme.CONSTRUCTOR => ()
        case _                                                                                  =>
          tree match {
            case md: DefDef => log("[+symbol] " + sym.debugLocationString)
            case _          =>
          }
      }
      tree.symbol = sym
      sym
    }

    /** Create a new symbol at the context owner based on the given tree.
     *  A different name can be given.  If the modifier flags should not be
     *  be transferred to the symbol as they are, supply a mask containing
     *  the flags to keep.
     */
    def createMemberSymbol(tree: MemberDef, name: Name, mask: Long): Symbol = {
      val pos         = tree.pos
      val isParameter = tree.mods.isParameter
      val flags       = tree.mods.flags & mask

      tree match {
        case TypeDef(_, _, _, _) if isParameter     => owner.newTypeParameter(name.toTypeName, pos, flags)
        case TypeDef(_, _, _, _)                    => owner.newTypeSymbol(name.toTypeName, pos, flags)
        case DefDef(_, nme.CONSTRUCTOR, _, _, _, _) => owner.newConstructor(pos, flags)
        case DefDef(_, _, _, _, _, _)               => owner.newMethod(name.toTermName, pos, flags)
        case ClassDef(_, _, _, _)                   => owner.newClassSymbol(name.toTypeName, pos, flags)
        case ModuleDef(_, _, _)                     => owner.newModule(name.toTermName, pos, flags)
        case PackageDef(pid, _)                     => createPackageSymbol(pos, pid)
        case ValDef(_, _, _, _)                     =>
          if (isParameter) owner.newValueParameter(name.toTermName, pos, flags)
          else owner.newValue(name.toTermName, pos, flags)
      }
    }

    def createImportSymbol(tree: Import) =
      NoSymbol.newImport(tree.pos) setInfo (namerOf(tree.symbol) importTypeCompleter tree)

    /** All PackageClassInfoTypes come from here. */
    def createPackageSymbol(pos: Position, pid: RefTree): Symbol = {
      val pkgOwner = pid match {
        case Ident(_)                 => if (owner.isEmptyPackageClass) rootMirror.RootClass else owner
        case Select(qual: RefTree, _) => createPackageSymbol(pos, qual).moduleClass
      }
      val existing = pkgOwner.info.decls.lookup(pid.name)

      if (existing.hasPackageFlag && pkgOwner == existing.owner)
        existing
      else {
        val pkg          = pkgOwner.newPackage(pid.name.toTermName, pos)
        val pkgClass     = pkg.moduleClass
        val pkgClassInfo = new PackageClassInfoType(newPackageScope(pkgClass), pkgClass)

        pkgClass setInfo pkgClassInfo
        pkg setInfo pkgClass.tpe
        enterInScope(pkg, pkgOwner.info.decls)
      }
    }

    private def enterClassSymbol(tree: ClassDef, clazz: ClassSymbol): Symbol = {
      if (clazz.sourceFile != null && clazz.sourceFile != contextFile)
        devWarning(s"Source file mismatch in $clazz: ${clazz.sourceFile} vs. $contextFile")

      clazz.associatedFile = contextFile
      if (clazz.sourceFile != null) {
        assert(currentRun.canRedefine(clazz) || clazz.sourceFile == currentRun.symSource(clazz), clazz.sourceFile)
        currentRun.symSource(clazz) = clazz.sourceFile
      }
      registerTopLevelSym(clazz)
      assert(clazz.name.toString.indexOf('(') < 0, clazz.name)  // )
      clazz
    }

    def enterClassSymbol(tree: ClassDef): Symbol = {
      val existing = context.scope.lookup(tree.name)
      val isRedefinition = (
           existing.isType
        && existing.isTopLevel
        && context.scope == existing.owner.info.decls
        && currentRun.canRedefine(existing)
      )
      val clazz: Symbol = {
        if (isRedefinition) {
          updatePosFlags(existing, tree.pos, tree.mods.flags)
          setPrivateWithin(tree, existing)
          clearRenamedCaseAccessors(existing)
          existing
        }
        else assignAndEnterSymbol(tree) setFlag inConstructorFlag
      }
      clazz match {
        case csym: ClassSymbol if csym.isTopLevel => enterClassSymbol(tree, csym)
        case _                                    => clazz
      }
    }

    /** Given a ClassDef or ModuleDef, verifies there isn't a companion which
     *  has been defined in a separate file.
     */
    def validateCompanionDefs(tree: ImplDef) {
      val sym    = tree.symbol orElse { return }
      val ctx    = if (context.owner.isPackageObjectClass) context.outer else context
      val module = if (sym.isModule) sym else ctx.scope lookupModule tree.name
      val clazz  = if (sym.isClass) sym else ctx.scope lookupClass tree.name
      val fails  = (
           module.isModule
        && clazz.isClass
        && !module.isSynthetic
        && !clazz.isSynthetic
        && (clazz.sourceFile ne null)
        && (module.sourceFile ne null)
        && !(module isCoDefinedWith clazz)
        && module.exists
        && clazz.exists
        && (currentRun.compiles(clazz) == currentRun.compiles(module))
      )
      if (fails) {
        reporter.error(tree.pos, (
            s"Companions '$clazz' and '$module' must be defined in same file:\n"
          + s"  Found in ${clazz.sourceFile.canonicalPath} and ${module.sourceFile.canonicalPath}")
        )
      }
    }

    def enterModuleDef(tree: ModuleDef) = {
      val sym = enterModuleSymbol(tree)
      sym.moduleClass setInfo namerOf(sym).moduleClassTypeCompleter(tree)
      sym setInfo completerOf(tree)
      validateCompanionDefs(tree)
      sym
    }

    /** Enter a module symbol.
     */
    def enterModuleSymbol(tree : ModuleDef): Symbol = {
      var m: Symbol = context.scope lookupModule tree.name
      val moduleFlags = tree.mods.flags | MODULE
      if (m.isModule && !m.hasPackageFlag && inCurrentScope(m) && (currentRun.canRedefine(m) || m.isSynthetic)) {
        // This code accounts for the way the package objects found in the classpath are opened up
        // early by the completer of the package itself. If the `packageobjects` phase then finds
        // the same package object in sources, we have to clean the slate and remove package object
        // members from the package class.
        //
        // TODO SI-4695 Pursue the approach in https://github.com/scala/scala/pull/2789 that avoids
        //      opening up the package object on the classpath at all if one exists in source.
        if (m.isPackageObject) {
          val packageScope = m.enclosingPackageClass.rawInfo.decls
          packageScope.foreach(mem => if (mem.owner != m.enclosingPackageClass) packageScope unlink mem)
        }
        updatePosFlags(m, tree.pos, moduleFlags)
        setPrivateWithin(tree, m)
        m.moduleClass andAlso (setPrivateWithin(tree, _))
        context.unit.synthetics -= m
        tree.symbol = m
      }
      else {
        m = assignAndEnterSymbol(tree)
        m.moduleClass setFlag moduleClassFlags(moduleFlags)
        setPrivateWithin(tree, m.moduleClass)
      }
      if (m.isTopLevel && !m.hasPackageFlag) {
        m.moduleClass.associatedFile = contextFile
        currentRun.symSource(m) = m.moduleClass.sourceFile
        registerTopLevelSym(m)
      }
      m
    }

    def enterSyms(trees: List[Tree]): Namer = {
      trees.foldLeft(this: Namer) { (namer, t) =>
        val ctx = namer enterSym t
        // for Import trees, enterSym returns a changed context, so we need a new namer
        if (ctx eq namer.context) namer
        else newNamer(ctx)
      }
    }
    def applicableTypeParams(owner: Symbol): List[Symbol] =
      if (owner.isTerm || owner.isPackageClass) Nil
      else applicableTypeParams(owner.owner) ::: owner.typeParams

    /** If no companion object for clazz exists yet, create one by applying `creator` to
     *  class definition tree.
     *  @return the companion object symbol.
     */
    def ensureCompanionObject(cdef: ClassDef, creator: ClassDef => Tree = companionModuleDef(_)): Symbol =
      pluginsEnsureCompanionObject(this, cdef, creator)

    /** Default implementation of `ensureCompanionObject`.
     *  Can be overridden by analyzer plugins (see AnalyzerPlugins.pluginsEnsureCompanionObject for more details)
     */
    def standardEnsureCompanionObject(cdef: ClassDef, creator: ClassDef => Tree = companionModuleDef(_)): Symbol = {
      val m = companionSymbolOf(cdef.symbol, context)
      // @luc: not sure why "currentRun.compiles(m)" is needed, things breaks
      // otherwise. documentation welcome.
      //
      // @PP: I tried to reverse engineer said documentation.  The only tests
      // which fail are buildmanager tests, as follows.  Given A.scala:
      //   case class Foo()
      // If you recompile A.scala, the Changes Map is
      //   Map(class Foo -> Nil, object Foo -> Nil)
      // But if you remove the 'currentRun.compiles(m)' condition, it is
      //   Map(class Foo -> Nil)
      // What exactly this implies and whether this is a sensible way to
      // enforce it, I don't know.
      //
      // @martin: currentRun.compiles is needed because we might have a stale
      // companion object from another run in scope. In that case we should still
      // overwrite the object. I.e.
      // Compile run #1: object Foo { ... }
      // Compile run #2: case class Foo ...
      // The object Foo is still in scope, but because it is not compiled in current run
      // it should be ditched and a new one created.
      if (m != NoSymbol && currentRun.compiles(m)) m
      else enterSyntheticSym(atPos(cdef.pos.focus)(creator(cdef)))
    }

    private def checkSelectors(tree: Import): Unit = {
      import DuplicatesErrorKinds._
      val Import(expr, selectors) = tree
      val base = expr.tpe

      def checkNotRedundant(pos: Position, from: Name, to0: Name) {
        def check(to: Name) = {
          val e = context.scope.lookupEntry(to)

          if (e != null && e.owner == context.scope && e.sym.exists)
            typer.permanentlyHiddenWarning(pos, to0, e.sym)
          else if (context ne context.enclClass) {
            val defSym = context.prefix.member(to) filter (
              sym => sym.exists && context.isAccessible(sym, context.prefix, superAccess = false))

            defSym andAlso (typer.permanentlyHiddenWarning(pos, to0, _))
          }
        }
        if (!tree.symbol.isSynthetic && expr.symbol != null && !expr.symbol.isInterpreterWrapper) {
          if (base.member(from) != NoSymbol)
            check(to0)
          if (base.member(from.toTypeName) != NoSymbol)
            check(to0.toTypeName)
        }
      }
      def checkSelector(s: ImportSelector) = {
        val ImportSelector(from, fromPos, to, _) = s
        def isValid(original: Name) =
          original.bothNames forall (x => (base nonLocalMember x) == NoSymbol)

        if (from != nme.WILDCARD && base != ErrorType) {
          if (isValid(from)) {
            // for Java code importing Scala objects
            if (!nme.isModuleName(from) || isValid(from.dropModule)) {
              typer.TyperErrorGen.NotAMemberError(tree, expr, from)
            }
          }
          // Setting the position at the import means that if there is
          // more than one hidden name, the second will not be warned.
          // So it is the position of the actual hidden name.
          //
          // Note: java imports have precedence over definitions in the same package
          //       so don't warn for them. There is a corresponding special treatment
          //       in the shadowing rules in typedIdent to (SI-7232). In any case,
          //       we shouldn't be emitting warnings for .java source files.
          if (!context.unit.isJava)
            checkNotRedundant(tree.pos withPoint fromPos, from, to)
        }
      }

      def noDuplicates(names: List[Name], check: DuplicatesErrorKinds.Value) {
        def loop(xs: List[Name]): Unit = xs match {
          case Nil      => ()
          case hd :: tl =>
            if (hd == nme.WILDCARD || !(tl contains hd)) loop(tl)
            else DuplicatesError(tree, hd, check)
        }
        loop(names filterNot (x => x == null || x == nme.WILDCARD))
      }
      selectors foreach checkSelector

      // checks on the whole set
      noDuplicates(selectors map (_.name), RenamedTwice)
      noDuplicates(selectors map (_.rename), AppearsTwice)
    }

    def enterCopyMethod(copyDef: DefDef): Symbol = {
      val sym      = copyDef.symbol
      val lazyType = completerOf(copyDef)

      /* Assign the types of the class parameters to the parameters of the
       * copy method. See comment in `Unapplies.caseClassCopyMeth` */
      def assignParamTypes() {
        val clazz = sym.owner
        val constructorType = clazz.primaryConstructor.tpe
        val subst = new SubstSymMap(clazz.typeParams, copyDef.tparams map (_.symbol))
        val classParamss = constructorType.paramss

        map2(copyDef.vparamss, classParamss)((copyParams, classParams) =>
          map2(copyParams, classParams)((copyP, classP) =>
            copyP.tpt setType subst(classP.tpe)
          )
        )
      }

      sym setInfo {
        mkTypeCompleter(copyDef) { sym =>
          assignParamTypes()
          lazyType complete sym
        }
      }
    }

    def completerOf(tree: MemberDef): TypeCompleter = {
      val mono = namerOf(tree.symbol) monoTypeCompleter tree
      val tparams = treeInfo.typeParameters(tree)
      if (tparams.isEmpty) mono
      else {
        /* @M! TypeDef's type params are handled differently, e.g., in `type T[A[x <: B], B]`, A and B are entered
         * first as both are in scope in the definition of x. x is only in scope in `A[x <: B]`.
         * No symbols are created for the abstract type's params at this point, i.e. the following assertion holds:
         *     !tree.symbol.isAbstractType || { tparams.forall(_.symbol == NoSymbol)
         * (tested with the above example, `trait C { type T[A[X <: B], B] }`). See also comment in PolyTypeCompleter.
         */
        if (!tree.symbol.isAbstractType) //@M TODO: change to isTypeMember ?
          createNamer(tree) enterSyms tparams

        new PolyTypeCompleter(tparams, mono, context) //@M
      }
    }

    def enterValDef(tree: ValDef): Unit = {
      val isScala = !context.unit.isJava
      if (isScala) {
        if (nme.isSetterName(tree.name)) ValOrVarWithSetterSuffixError(tree)
        if (tree.mods.isPrivateLocal && tree.mods.isCaseAccessor) PrivateThisCaseClassParameterError(tree)
      }

      if (isScala && deriveAccessors(tree)) enterGetterSetter(tree)
      else assignAndEnterFinishedSymbol(tree)

      if (isEnumConstant(tree)) {
        tree.symbol setInfo ConstantType(Constant(tree.symbol))
        tree.symbol.owner.linkedClassOfClass addChild tree.symbol
      }
    }

    def enterPackage(tree: PackageDef) {
      val sym = assignSymbol(tree)
      newNamer(context.make(tree, sym.moduleClass, sym.info.decls)) enterSyms tree.stats
    }
    def enterTypeDef(tree: TypeDef) = assignAndEnterFinishedSymbol(tree)

    def enterDefDef(tree: DefDef): Unit = tree match {
      case DefDef(_, nme.CONSTRUCTOR, _, _, _, _) =>
        assignAndEnterFinishedSymbol(tree)
      case DefDef(mods, name, tparams, _, _, _) =>
        val bridgeFlag = if (mods hasAnnotationNamed tpnme.bridgeAnnot) BRIDGE | ARTIFACT else 0
        val sym = assignAndEnterSymbol(tree) setFlag bridgeFlag

        if (name == nme.copy && sym.isSynthetic)
          enterCopyMethod(tree)
        else if (name == nme.apply && sym.hasAllFlags(SYNTHETIC | CASE))
          sym setInfo caseApplyMethodCompleter(tree, completerOf(tree).asInstanceOf[LockingTypeCompleter])
        else
          sym setInfo completerOf(tree)
    }

    def enterClassDef(tree: ClassDef) {
      val ClassDef(mods, _, _, impl) = tree
      val primaryConstructorArity = treeInfo.firstConstructorArgs(impl.body).size
      tree.symbol = enterClassSymbol(tree)
      tree.symbol setInfo completerOf(tree)

      if (mods.isCase) {
        val m = ensureCompanionObject(tree, caseModuleDef)
        m.moduleClass.updateAttachment(new ClassForCaseCompanionAttachment(tree))
      }
      val hasDefault = impl.body exists treeInfo.isConstructorWithDefault
      if (hasDefault) {
        val m = ensureCompanionObject(tree)
        m.updateAttachment(new ConstructorDefaultsAttachment(tree, null))
      }
      val owner = tree.symbol.owner
      if (settings.warnPackageObjectClasses && owner.isPackageObjectClass && !mods.isImplicit) {
        reporter.warning(tree.pos,
          "it is not recommended to define classes/objects inside of package objects.\n" +
          "If possible, define " + tree.symbol + " in " + owner.skipPackageObject + " instead."
        )
      }

      // Suggested location only.
      if (mods.isImplicit) {
        if (primaryConstructorArity == 1) {
          log("enter implicit wrapper "+tree+", owner = "+owner)
          enterImplicitWrapper(tree)
        }
        else reporter.error(tree.pos, "implicit classes must accept exactly one primary constructor parameter")
      }
      validateCompanionDefs(tree)
    }

    // Hooks which are overridden in the presentation compiler
    def enterExistingSym(sym: Symbol, tree: Tree): Context = {
      this.context
    }
    def enterIfNotThere(sym: Symbol) { }

    def enterSyntheticSym(tree: Tree): Symbol = {
      enterSym(tree)
      context.unit.synthetics(tree.symbol) = tree
      tree.symbol
    }

// --- Lazy Type Assignment --------------------------------------------------

    def findCyclicalLowerBound(tp: Type): Symbol = {
      tp match {
        case TypeBounds(lo, _) =>
          // check that lower bound is not an F-bound
          // but carefully: class Foo[T <: Bar[_ >: T]] should be allowed
          for (tp1 @ TypeRef(_, sym, _) <- lo) {
            if (settings.breakCycles) {
              if (!sym.maybeInitialize) {
                log(s"Cycle inspecting $lo for possible f-bounds: ${sym.fullLocationString}")
                return sym
              }
            }
            else sym.initialize
          }
        case _ =>
      }
      NoSymbol
    }

    def monoTypeCompleter(tree: MemberDef) = mkTypeCompleter(tree) { sym =>
      // this early test is there to avoid infinite baseTypes when
      // adding setters and getters --> bug798
      // It is a def in an attempt to provide some insulation against
      // uninitialized symbols misleading us. It is not a certainty
      // this accomplishes anything, but performance is a non-consideration
      // on these flag checks so it can't hurt.
      def needsCycleCheck = sym.isNonClassType && !sym.isParameter && !sym.isExistential

      val annotations = annotSig(tree.mods.annotations)

      val tp = typeSig(tree, annotations)

      findCyclicalLowerBound(tp) andAlso { sym =>
        if (needsCycleCheck) {
          // neg/t1224:  trait C[T] ; trait A { type T >: C[T] <: C[C[T]] }
          // To avoid an infinite loop on the above, we cannot break all cycles
          log(s"Reinitializing info of $sym to catch any genuine cycles")
          sym reset sym.info
          sym.initialize
        }
      }

      sym.setInfo(if (!sym.isJavaDefined) tp else RestrictJavaArraysMap(tp))

      if (needsCycleCheck) {
        log(s"Needs cycle check: ${sym.debugLocationString}")
        if (!typer.checkNonCyclic(tree.pos, tp))
          sym setInfo ErrorType
      }

      validate(sym)
    }

    def moduleClassTypeCompleter(tree: ModuleDef) = mkTypeCompleter(tree) { sym =>
      val moduleSymbol = tree.symbol
      assert(moduleSymbol.moduleClass == sym, moduleSymbol.moduleClass)
      moduleSymbol.info // sets moduleClass info as a side effect.
    }


    def importTypeCompleter(imp: Import) = mkTypeCompleter(imp) { sym =>
      sym setInfo importSig(imp)
    }

    import AnnotationInfo.{mkFilter => annotationFilter}

    def implicitFactoryMethodCompleter(tree: DefDef, classSym: Symbol, sigCompleter: LockingTypeCompleter) = mkTypeCompleter(tree) { methSym =>
      sigCompleter.completeImpl(methSym)

      val annotations = classSym.initialize.annotations

      methSym setAnnotations (annotations filter annotationFilter(MethodTargetClass, defaultRetention = false))
      classSym setAnnotations (annotations filter annotationFilter(ClassTargetClass, defaultRetention = true))
    }

    def caseApplyMethodCompleter(tree: DefDef, sigCompleter: LockingTypeCompleter) = mkTypeCompleter(tree) { methSym =>
      sigCompleter.completeImpl(methSym)

      // don't propagate e.g. @volatile annot to apply's argument
      def retainOnlyParamAnnots(param: Symbol) =
        param setAnnotations (param.annotations filter AnnotationInfo.mkFilter(ParamTargetClass, defaultRetention = false))

      methSym.info.paramss.foreach(_.foreach(retainOnlyParamAnnots))
    }

    // complete the type of a value definition (may have a method symbol, for those valdefs that never receive a field,
    // as specified by Field.noFieldFor)
    def valTypeCompleter(tree: ValDef) = mkTypeCompleter(tree) { fieldOrGetterSym =>
      val mods = tree.mods
      val isGetter = fieldOrGetterSym.isMethod
      val annots =
        if (mods.annotations.isEmpty) Nil
        else {
          val annotSigs = annotSig(mods.annotations)
            if (isGetter) filterAccessorAnnots(annotSigs, tree) // if this is really a getter, retain annots targeting either field/getter
            else annotSigs filter annotationFilter(FieldTargetClass, !mods.isParamAccessor)
        }

      // must use typeSig, not memberSig (TODO: when do we need to switch namers?)
      val sig = typeSig(tree, annots)

      fieldOrGetterSym setInfo (if (isGetter) NullaryMethodType(sig) else sig)

      validate(fieldOrGetterSym)
    }

    // knowing `isBean`, we could derive `isSetter` from `valDef.name`
    def accessorTypeCompleter(valDef: ValDef, missingTpt: Boolean, isBean: Boolean, isSetter: Boolean) = mkTypeCompleter(valDef) { accessorSym =>
      context.unit.synthetics get accessorSym match {
        case Some(ddef: DefDef) =>
          // `accessorSym` is the accessor for which we're completing the info (tree == ddef),
          // while `valDef` is the field definition that spawned the accessor
          // NOTE: `valTypeCompleter` handles abstract vals, trait vals and lazy vals, where the ValDef carries the getter's symbol

          // reuse work done in valTypeCompleter if we already computed the type signature of the val
          // (assuming the field and accessor symbols are distinct -- i.e., we're not in a trait)
          val valSig =
            if ((accessorSym ne valDef.symbol) && valDef.symbol.isInitialized) valDef.symbol.info
            else typeSig(valDef, Nil) // don't set annotations for the valdef -- we just want to compute the type sig (TODO: dig deeper and see if we can use memberSig)

          // patch up the accessor's tree if the valdef's tpt was not known back when the tree was synthesized
          // can't look at `valDef.tpt` here because it may have been completed by now (this is why we pass in `missingTpt`)
          // HACK: a param accessor `ddef.tpt.tpe` somehow gets out of whack with `accessorSym.info`, so always patch it back...
          //       (the tpt is typed in the wrong namer, using the class as owner instead of the outer context, which is where param accessors should be typed)
          if (missingTpt || accessorSym.isParamAccessor) {
            if (!isSetter) ddef.tpt setType valSig
            else if (ddef.vparamss.nonEmpty && ddef.vparamss.head.nonEmpty) ddef.vparamss.head.head.tpt setType valSig
            else throw new TypeError(valDef.pos, s"Internal error: could not complete parameter/return type for $ddef from $accessorSym")
          }

          val mods = valDef.mods
          val annots =
            if (mods.annotations.isEmpty) Nil
            else filterAccessorAnnots(annotSig(mods.annotations), valDef, isSetter, isBean)

          // for a setter, call memberSig to attribute the parameter (for a bean, we always use the regular method sig completer since they receive method types)
          // for a regular getter, make sure it gets a NullaryMethodType (also, no need to recompute it: we already have the valSig)
          val sig =
            if (isSetter || isBean) typeSig(ddef, annots)
            else {
              if (annots.nonEmpty) annotate(accessorSym, annots)

              NullaryMethodType(valSig)
            }

          accessorSym setInfo pluginsTypeSigAccessor(sig, typer, valDef, accessorSym)

          if (!isBean && accessorSym.isOverloaded)
            if (isSetter) ddef.rhs.setType(ErrorType)
            else GetterDefinedTwiceError(accessorSym)

          validate(accessorSym)

        case _ =>
          throw new TypeError(valDef.pos, s"Internal error: no synthetic tree found for bean accessor $accessorSym")
      }
    }

    // see scala.annotation.meta's package class for more info
    // Annotations on ValDefs can be targeted towards the following: field, getter, setter, beanGetter, beanSetter, param.
    // The defaults are:
    //   - (`val`-, `var`- or plain) constructor parameter annotations end up on the parameter, not on any other entity.
    //   - val/var member annotations solely end up on the underlying field, except in traits (@since 2.12),
    //     where there is no field, and the getter thus holds annotations targeting both getter & field.
    //     As soon as there is a field/getter (in subclasses mixing in the trait), we triage the annotations.
    //
    // TODO: these defaults can be surprising for annotations not meant for accessors/fields -- should we revisit?
    // (In order to have `@foo val X` result in the X getter being annotated with `@foo`, foo needs to be meta-annotated with @getter)
    private def filterAccessorAnnots(annotSigs: List[global.AnnotationInfo], tree: global.ValDef, isSetter: Boolean = false, isBean: Boolean = false): List[AnnotationInfo] = {
      val mods = tree.mods
      if (!isBean) {
        // neg/t3403: check that we didn't get a sneaky type alias/renamed import that we couldn't detect because we only look at names during synthesis
        // (TODO: can we look at symbols earlier?)
        if (!((mods hasAnnotationNamed tpnme.BeanPropertyAnnot) || (mods hasAnnotationNamed tpnme.BooleanBeanPropertyAnnot))
          && annotSigs.exists(ann => (ann.matches(BeanPropertyAttr)) || ann.matches(BooleanBeanPropertyAttr)))
          BeanPropertyAnnotationLimitationError(tree)
      }

      def filterAccessorAnnotations: AnnotationInfo => Boolean =
        if (isSetter || !owner.isTrait)
          annotationFilter(if (isSetter) SetterTargetClass else GetterTargetClass, defaultRetention = false)
        else (ann =>
          annotationFilter(FieldTargetClass, defaultRetention = true)(ann) ||
            annotationFilter(GetterTargetClass, defaultRetention = true)(ann))

      def filterBeanAccessorAnnotations: AnnotationInfo => Boolean =
        if (isSetter || !owner.isTrait)
          annotationFilter(if (isSetter) BeanSetterTargetClass else BeanGetterTargetClass, defaultRetention = false)
        else (ann =>
          annotationFilter(FieldTargetClass, defaultRetention = true)(ann) ||
            annotationFilter(BeanGetterTargetClass, defaultRetention = true)(ann))

      annotSigs filter (if (isBean) filterBeanAccessorAnnotations else filterAccessorAnnotations)
    }


    def selfTypeCompleter(tree: Tree) = mkTypeCompleter(tree) { sym =>
      val selftpe = typer.typedType(tree).tpe
      sym setInfo {
        if (selftpe.typeSymbol isNonBottomSubClass sym.owner) selftpe
        else intersectionType(List(sym.owner.tpe, selftpe))
      }
    }

    /** This method has a big impact on the eventual compiled code.
     *  At this point many values have the most specific possible
     *  type (e.g. in val x = 42, x's type is Int(42), not Int) but
     *  most need to be widened to avoid undesirable propagation of
     *  those singleton types.
     *
     *  However, the compilation of pattern matches into switch
     *  statements depends on constant folding, which will only take
     *  place for those values which aren't widened.  The "final"
     *  modifier is the present means of signaling that a constant
     *  value should not be widened, so it has a use even in situations
     *  whether it is otherwise redundant (such as in a singleton.)
     */
    private def widenIfNecessary(sym: Symbol, tpe: Type, pt: Type): Type = {
      val getter =
        if (sym.isValue && sym.owner.isClass && sym.isPrivate)
          sym.getterIn(sym.owner)
        else sym
      def isHidden(tp: Type): Boolean = tp match {
        case SingleType(pre, sym) =>
          (sym isLessAccessibleThan getter) || isHidden(pre)
        case ThisType(sym) =>
          sym isLessAccessibleThan getter
        case p: SimpleTypeProxy =>
          isHidden(p.underlying)
        case _ =>
          false
      }
      val shouldWiden = (
           !tpe.typeSymbolDirect.isModuleClass // Infer Foo.type instead of "object Foo"
        && (tpe.widen <:< pt)                  // Don't widen our way out of conforming to pt
        && (   sym.isVariable
            || sym.hasFlag(ACCESSOR) && !sym.hasFlag(STABLE)
            || sym.isMethod && !sym.hasFlag(ACCESSOR)
            || isHidden(tpe)
           )
      )
      dropIllegalStarTypes(
        if (shouldWiden) tpe.widen
        else if (sym.isFinal && !sym.isLazy) tpe    // "final val" allowed to retain constant type
        else tpe.deconst
      )
    }
    /** Computes the type of the body in a ValDef or DefDef, and
     *  assigns the type to the tpt's node.  Returns the type.
     */
    private def assignTypeToTree(tree: ValOrDefDef, defnTyper: Typer, pt: Type): Type = {
      val rhsTpe = tree match {
        case ddef: DefDef if tree.symbol.isTermMacro => defnTyper.computeMacroDefType(ddef, pt)
        case _ => defnTyper.computeType(tree.rhs, pt)
      }

      val defnTpe = widenIfNecessary(tree.symbol, rhsTpe, pt)
      tree.tpt defineType defnTpe setPos tree.pos.focus
      tree.tpt.tpe
    }

    // owner is the class with the self type
    def enterSelf(self: ValDef) {
      val ValDef(_, name, tpt, _) = self
      if (self eq noSelfType)
        return

      val hasName = name != nme.WILDCARD
      val hasType = !tpt.isEmpty
      if (!hasType)
        tpt defineType NoType

      val sym = (
        if (hasType || hasName) {
          owner.typeOfThis = if (hasType) selfTypeCompleter(tpt) else owner.tpe_*
          val selfSym = owner.thisSym setPos self.pos
          if (hasName) selfSym setName name else selfSym
        }
        else {
          val symName = if (name != nme.WILDCARD) name else nme.this_
          owner.newThisSym(symName, owner.pos) setInfo owner.tpe
        }
      )
      self.symbol = context.scope enter sym
    }

    private def templateSig(templ: Template): Type = {
      val clazz = context.owner
      def checkParent(tpt: Tree): Type = {
        if (tpt.tpe.isError) AnyRefTpe
        else tpt.tpe
      }

      val parents = typer.typedParentTypes(templ) map checkParent

      enterSelf(templ.self)

      val decls = newScope
      val templateNamer = newNamer(context.make(templ, clazz, decls))
      templateNamer enterSyms templ.body

      // add apply and unapply methods to companion objects of case classes,
      // unless they exist already; here, "clazz" is the module class
      if (clazz.isModuleClass) {
        clazz.attachments.get[ClassForCaseCompanionAttachment] foreach { cma =>
          val cdef = cma.caseClass
          assert(cdef.mods.isCase, "expected case class: "+ cdef)
          addApplyUnapply(cdef, templateNamer)
        }
      }

      // add the copy method to case classes; this needs to be done here, not in SyntheticMethods, because
      // the namer phase must traverse this copy method to create default getters for its parameters.
      // here, clazz is the ClassSymbol of the case class (not the module). (!clazz.hasModuleFlag) excludes
      // the moduleClass symbol of the companion object when the companion is a "case object".
      if (clazz.isCaseClass && !clazz.hasModuleFlag) {
        val modClass = companionSymbolOf(clazz, context).moduleClass
        modClass.attachments.get[ClassForCaseCompanionAttachment] foreach { cma =>
          val cdef = cma.caseClass
          def hasCopy = (decls containsName nme.copy) || parents.exists(_ member nme.copy exists)

          // SI-5956 needs (cdef.symbol == clazz): there can be multiple class symbols with the same name
          if (cdef.symbol == clazz && !hasCopy)
            addCopyMethod(cdef, templateNamer)
        }
      }

      // if default getters (for constructor defaults) need to be added to that module, here's the namer
      // to use. clazz is the ModuleClass. sourceModule works also for classes defined in methods.
      val module = clazz.sourceModule
      for (cda <- module.attachments.get[ConstructorDefaultsAttachment]) {
        debuglog(s"Storing the template namer in the ConstructorDefaultsAttachment of ${module.debugLocationString}.")
        cda.companionModuleClassNamer = templateNamer
      }
      val classTp = ClassInfoType(parents, decls, clazz)
      pluginsTypeSig(classTp, templateNamer.typer, templ, WildcardType)
    }

    private def classSig(cdef: ClassDef): Type = {
      val clazz = cdef.symbol
      val ClassDef(_, _, tparams, impl) = cdef
      val tparams0   = typer.reenterTypeParams(tparams)
      val resultType = templateSig(impl)

      val res = GenPolyType(tparams0, resultType)
      val pluginsTp = pluginsTypeSig(res, typer, cdef, WildcardType)

      // Already assign the type to the class symbol (monoTypeCompleter will do it again).
      // Allows isDerivedValueClass to look at the info.
      clazz setInfo pluginsTp
      if (clazz.isDerivedValueClass) {
        log("Ensuring companion for derived value class " + cdef.name + " at " + cdef.pos.show)
        clazz setFlag FINAL
        // Don't force the owner's info lest we create cycles as in SI-6357.
        enclosingNamerWithScope(clazz.owner.rawInfo.decls).ensureCompanionObject(cdef)
      }
      pluginsTp
    }

    private def moduleSig(mdef: ModuleDef): Type = {
      val moduleSym = mdef.symbol
      // The info of both the module and the moduleClass symbols need to be assigned. monoTypeCompleter assigns
      // the result of typeSig to the module symbol. The module class info is assigned here as a side-effect.
      val result = templateSig(mdef.impl)
      val pluginsTp = pluginsTypeSig(result, typer, mdef, WildcardType)
      // Assign the moduleClass info (templateSig returns a ClassInfoType)
      val clazz = moduleSym.moduleClass
      clazz setInfo pluginsTp
      // clazz.tpe_* returns a `ModuleTypeRef(clazz)`, a typeRef that links to the module class `clazz`
      // (clazz.info would the ClassInfoType, which is not what should be assigned to the module symbol)
      clazz.tpe_*
    }


    // make a java method type if meth.isJavaDefined
    private def methodTypeFor(meth: Symbol, vparamSymss: List[List[Symbol]], restpe: Type) = {
      def makeJavaMethodType(vparams: List[Symbol], restpe: Type) = {
        vparams foreach (p => p setInfo objToAny(p.tpe))
        JavaMethodType(vparams, restpe)
      }
      if (vparamSymss.isEmpty) NullaryMethodType(restpe)
      else if (meth.isJavaDefined) vparamSymss.foldRight(restpe)(makeJavaMethodType)
      else vparamSymss.foldRight(restpe)(MethodType(_, _))
    }


    /**
     * The method type for `ddef`.
     *
     * If a PolyType(tparams, restp) is returned, `tparams` are the external symbols (not type skolems),
     * i.e. instances of AbstractTypeSymbol. All references in `restp` to the type parameters are TypeRefs
     * to these non-skolems.
     *
     * For type-checking the rhs (in case the result type is inferred), the type skolems of the type parameters
     * are entered in scope. Equally, the parameter symbols entered into scope have types which refer to those
     * skolems: when type-checking the rhs, references to parameters need to have types that refer to the skolems.
     * In summary, typing an rhs happens with respect to the skolems.
     *
     * This means that the method's result type computed by the typer refers to skolems. In order to put it
     * into the method type (the result of methodSig), typeRefs to skolems have to be replaced by references
     * to the non-skolems.
     */
    private def methodSig(ddef: DefDef): Type = {
      val DefDef(_, _, tparams, vparamss, tpt, _) = ddef

      val meth = owner
      val methOwner = meth.owner

      /* tparams already have symbols (created in enterDefDef/completerOf), namely the skolemized ones (created
       * by the PolyTypeCompleter constructor, and assigned to tparams). reenterTypeParams enters the type skolems
       * into scope and returns the non-skolems.
       */
      val tparamSyms = typer.reenterTypeParams(tparams)
      val tparamSkolems = tparams.map(_.symbol)


      /*
       * Creates a method type using tparamSyms and vparamsSymss as argument symbols and `respte` as result type.
       * All typeRefs to type skolems are replaced by references to the corresponding non-skolem type parameter,
       * so the resulting type is a valid external method type, it does not contain (references to) skolems.
       *
       * tparamSyms are deskolemized symbols  -- TODO: check that their infos don't refer to method args?
       * vparamss refer (if they do) to skolemized tparams
       */
      def deskolemizedPolySig(vparamSymss: List[List[Symbol]], restpe: Type) =
        GenPolyType(tparamSyms, methodTypeFor(meth, vparamSymss, restpe).substSym(tparamSkolems, tparamSyms))


      if (tpt.isEmpty && meth.name == nme.CONSTRUCTOR) {
        tpt defineType context.enclClass.owner.tpe_*
        tpt setPos meth.pos.focus
      }

      /* since the skolemized tparams are in scope, the TypeRefs in types of vparamSymss refer to the type skolems
       * note that for parameters with missing types, `methodSig` reassigns types of these symbols (the parameter
       * types from the overridden method).
       */
      val vparamSymss: List[List[Symbol]] = enterValueParams(vparamss)

      val resTpGiven =
        if (tpt.isEmpty) WildcardType
        else typer.typedType(tpt).tpe


      // ignore missing types unless we can look to overridden method to recover the missing information
      val canOverride = methOwner.isClass && !meth.isConstructor
      val inferResTp  = canOverride && tpt.isEmpty
      val inferArgTp  = canOverride && settings.YmethodInfer && mexists(vparamss)(_.tpt.isEmpty)


      /*
       * Find the overridden method that matches a schematic method type,
       * which has WildcardTypes for unspecified return or parameter types.
       * For instance, in `def f[T](a: T, b) = ...`, the type schema is
       *
       *   PolyType(T, MethodType(List(a: T, b: WildcardType), WildcardType))
       *
       * where T are non-skolems.
       *
       * NOTE: mutates info of symbol of vparamss that don't specify a type
       */
      val methodSigApproxUnknownArgs: () => Type =
        if (!inferArgTp) () => deskolemizedPolySig(vparamSymss, resTpGiven)
        else () => {
          // for all params without type set WildcardType
          mforeach(vparamss)(v => if (v.tpt.isEmpty) v.symbol setInfo WildcardType)
          // must wait to call deskolemizedPolySig until we've temporarily set the WildcardType info for the vparamSymss
          // (Otherwise, valDefSig will complain about missing argument types.)
          deskolemizedPolySig(vparamSymss, resTpGiven)
        }

      // Must be lazy about the schema to avoid cycles in neg/t5093.scala
      val overridden =
        if (!canOverride) NoSymbol
        else safeNextOverriddenSymbolLazySchema(meth, methodSigApproxUnknownArgs)

      /*
       * If `meth` doesn't have an explicit return type, extract the return type from the method
       * overridden by `meth` (if there's an unique one). This type is later used as the expected
       * type for computing the type of the rhs. The resulting type references type skolems for
       * type parameters (consistent with the result of `typer.typedType(tpt).tpe`).
       *
       * If the result type is missing, assign a MethodType to `meth` that's constructed using this return type.
       * This allows omitting the result type for recursive methods.
       *
       * Missing parameter types are also recovered from the overridden method (by mutating the info of their symbols).
       * (The parser accepts missing parameter types under -Yinfer-argument-types.)
       */
      val resTpFromOverride =
        if (!(inferArgTp || inferResTp) || overridden == NoSymbol || overridden.isOverloaded) resTpGiven
        else {
          overridden.cookJavaRawInfo() // #3404 xform java rawtypes into existentials

          val (overriddenTparams, overriddenTp) =
            methOwner.thisType.memberType(overridden) match {
              case PolyType(tparams, mt) => (tparams, mt.substSym(tparams, tparamSkolems))
              case mt => (Nil, mt)
            }

          // try to derive empty parameter types from the overridden method's argument types
          if (inferArgTp) {
            val overriddenSyms = overriddenTparams ++ overridden.paramss.flatten
            val ourSyms = tparamSkolems ++ vparamSymss.flatten
            foreach2(vparamss, overridden.paramss) { foreach2(_, _) { (vparam, overriddenParam) =>
              // println(s"infer ${vparam.symbol} from ${overriddenParam}? ${vparam.tpt}")
              if (vparam.tpt.isEmpty) {
                val overriddenParamTp = overriddenParam.tpe.substSym(overriddenSyms, ourSyms)
                // println(s"inferred ${vparam.symbol} : $overriddenParamTp")
                // references to type parameters in overriddenParamTp link to the type skolems, so the
                // assigned type is consistent with the other / existing parameter types in vparamSymss.
                vparam.symbol setInfo overriddenParamTp
                vparam.tpt defineType overriddenParamTp setPos vparam.pos.focus
              }
            }}
          }

          @tailrec @inline def applyFully(tp: Type, paramss: List[List[Symbol]]): Type =
            if (paramss.isEmpty) tp match {
              case NullaryMethodType(rtpe) => rtpe
              case MethodType(Nil, rtpe)   => rtpe
              case tp                      => tp
            }
            else applyFully(tp.resultType(paramss.head.map(_.tpe)), paramss.tail)

          if (inferResTp) {
            // SI-7668 Substitute parameters from the parent method with those of the overriding method.
            val overriddenResTp = applyFully(overriddenTp, vparamSymss).substSym(overriddenTparams, tparamSkolems)

            // provisionally assign `meth` a method type with inherited result type
            // that way, we can leave out the result type even if method is recursive.
            meth setInfo deskolemizedPolySig(vparamSymss, overriddenResTp)
            overriddenResTp
          } else resTpGiven
        }

      // issue an error for missing parameter types
      // (computing resTpFromOverride may have required inferring some, meanwhile)
      mforeach(vparamss) { vparam =>
        if (vparam.tpt.isEmpty) {
          MissingParameterOrValTypeError(vparam)
          vparam.tpt defineType ErrorType
        }
      }

      // If we, or the overridden method has defaults, add getters for them
      if (mexists(vparamss)(_.symbol.hasDefault) || mexists(overridden.paramss)(_.hasDefault))
        addDefaultGetters(meth, ddef, vparamss, tparams,  overridden)

      // fast track macros, i.e. macros defined inside the compiler, are hardcoded
      // hence we make use of that and let them have whatever right-hand side they need
      // (either "macro ???" as they used to or just "???" to maximally simplify their compilation)
      if (fastTrack contains meth) meth setFlag MACRO

      // macro defs need to be typechecked in advance
      // because @macroImpl annotation only gets assigned during typechecking
      // otherwise macro defs wouldn't be able to robustly coexist with their clients
      // because a client could be typechecked before a macro def that it uses
      if (meth.isMacro) typer.computeMacroDefType(ddef, resTpFromOverride) // note: `pt` argument ignored in `computeMacroDefType`

      if (vparamSymss.lengthCompare(0) > 0) { // OPT fast path for methods of 0-1 parameter lists
        val checkDependencies = new DependentTypeChecker(context)(this)
        checkDependencies check vparamSymss
      }

      val resTp = {
        // When return type is inferred, we don't just use resTpFromOverride -- it must be packed and widened.
        // Here, C.f has type String:
        //   trait T { def f: Object }; class C extends T { def f = "" }
        // using resTpFromOverride as expected type allows for the following (C.f has type A):
        //   trait T { def f: A }; class C extends T { implicit def b2a(t: B): A = ???; def f = new B }
        val resTpComputedUnlessGiven =
          if (tpt.isEmpty) assignTypeToTree(ddef, typer, resTpFromOverride)
          else resTpGiven

        // #2382: return type of default getters are always @uncheckedVariance
        if (meth.hasDefault) resTpComputedUnlessGiven.withAnnotation(AnnotationInfo(uncheckedVarianceClass.tpe, List(), List()))
        else resTpComputedUnlessGiven
      }

      // Add a () parameter section if this overrides some method with () parameters
      val vparamSymssOrEmptyParamsFromOverride =
        if (overridden != NoSymbol && vparamSymss.isEmpty && overridden.alternatives.exists(_.info.isInstanceOf[MethodType])) ListOfNil // NOTEL must check `.info.isInstanceOf[MethodType]`, not `.isMethod`!
        else vparamSymss

      val methSig = deskolemizedPolySig(vparamSymssOrEmptyParamsFromOverride, resTp)
      pluginsTypeSig(methSig, typer, ddef, resTpGiven)
    }

    /**
     * For every default argument, insert a method computing that default
     *
     * Also adds the "override" and "defaultparam" (for inherited defaults) flags
     * Typer is too late, if an inherited default is used before the method is
     * typechecked, the corresponding param would not yet have the "defaultparam"
     * flag.
     */
    private def addDefaultGetters(meth: Symbol, ddef: DefDef, vparamss: List[List[ValDef]], tparams: List[TypeDef], overridden: Symbol) {
      val DefDef(_, _, rtparams0, rvparamss0, _, _) = resetAttrs(ddef.duplicate)
      // having defs here is important to make sure that there's no sneaky tree sharing
      // in methods with multiple default parameters
      def rtparams = rtparams0.map(_.duplicate)
      def rvparamss = rvparamss0.map(_.map(_.duplicate))
      val methOwner  = meth.owner
      val isConstr   = meth.isConstructor
      val overrides  = overridden != NoSymbol && !overridden.isOverloaded
      // value parameters of the base class (whose defaults might be overridden)
      var baseParamss = (vparamss, overridden.tpe.paramss) match {
        // match empty and missing parameter list
        case (Nil, ListOfNil) => Nil
        case (ListOfNil, Nil) => ListOfNil
        case (_, paramss)     => paramss
      }
      assert(
        !overrides || vparamss.length == baseParamss.length,
        "" + meth.fullName + ", "+ overridden.fullName
      )

      // cache the namer used for entering the default getter symbols
      var ownerNamer: Option[Namer] = None
      var moduleNamer: Option[(ClassDef, Namer)] = None
      var posCounter = 1

      // For each value parameter, create the getter method if it has a
      // default argument. previous denotes the parameter lists which
      // are on the left side of the current one. These get added to the
      // default getter. Example:
      //
      //   def foo(a: Int)(b: Int = a)      becomes
      //   foo$default$1(a: Int) = a
      //
      vparamss.foldLeft(Nil: List[List[ValDef]]) { (previous, vparams) =>
        assert(!overrides || vparams.length == baseParamss.head.length, ""+ meth.fullName + ", "+ overridden.fullName)
        val rvparams = rvparamss(previous.length)
        var baseParams = if (overrides) baseParamss.head else Nil
        map2(vparams, rvparams)((vparam, rvparam) => {
          val sym = vparam.symbol
          // true if the corresponding parameter of the base class has a default argument
          val baseHasDefault = overrides && baseParams.head.hasDefault
          if (sym.hasDefault) {
            // Create a "default getter", i.e. a DefDef that will calculate vparam.rhs
            // for those who are going to call meth without providing an argument corresponding to vparam.
            // After the getter is created, a corresponding synthetic symbol is created and entered into the parent namer.
            //
            // In the ideal world, this DefDef would be a simple one-liner that just returns vparam.rhs,
            // but in scalac things are complicated in two different ways.
            //
            // 1) Because the underlying language is quite sophisticated, we must allow for those sophistications in our getter.
            //    Namely: a) our getter has to copy type parameters from the associated method (or the associated class
            //    if meth is a constructor), because vparam.rhs might refer to one of them, b) our getter has to copy
            //    preceding value parameter lists from the associated method, because again vparam.rhs might refer to one of them.
            //
            // 2) Because we have already assigned symbols to type and value parameters that we have to copy, we must jump through
            //    hoops in order to destroy them and allow subsequent naming create new symbols for our getter. Previously this
            //    was done in an overly brutal way akin to resetAllAttrs, but now we utilize a resetLocalAttrs-based approach.
            //    Still far from ideal, but at least enables things like run/macro-default-params that were previously impossible.

            val oflag = if (baseHasDefault) OVERRIDE else 0
            val name = nme.defaultGetterName(meth.name, posCounter)

            var defTparams = rtparams
            val defVparamss = mmap(rvparamss.take(previous.length)){ rvp =>
              copyValDef(rvp)(mods = rvp.mods &~ DEFAULTPARAM, rhs = EmptyTree)
            }

            val parentNamer = if (isConstr) {
              val (cdef, nmr) = moduleNamer.getOrElse {
                val module = companionSymbolOf(methOwner, context)
                module.initialize // call type completer (typedTemplate), adds the
                                  // module's templateNamer to classAndNamerOfModule
                module.attachments.get[ConstructorDefaultsAttachment] match {
                  // by martin: the null case can happen in IDE; this is really an ugly hack on top of an ugly hack but it seems to work
                  case Some(cda) =>
                    if (cda.companionModuleClassNamer == null) {
                      devWarning(s"SI-6576 The companion module namer for $meth was unexpectedly null")
                      return
                    }
                    val p = (cda.classWithDefault, cda.companionModuleClassNamer)
                    moduleNamer = Some(p)
                    p
                  case _ =>
                    return // fix #3649 (prevent crash in erroneous source code)
                }
              }
              val ClassDef(_, _, rtparams, _) = resetAttrs(cdef.duplicate)
              defTparams = rtparams.map(rt => copyTypeDef(rt)(mods = rt.mods &~ (COVARIANT | CONTRAVARIANT)))
              nmr
            }
            else ownerNamer getOrElse {
              val ctx = context.nextEnclosing(c => c.scope.toList.contains(meth))
              assert(ctx != NoContext, meth)
              val nmr = newNamer(ctx)
              ownerNamer = Some(nmr)
              nmr
            }

            val defTpt =
              // don't mess with tpt's of case copy default getters, because assigning something other than TypeTree()
              // will break the carefully orchestrated naming/typing logic that involves enterCopyMethod and caseClassCopyMeth
              if (meth.isCaseCopy) TypeTree()
              else {
                // If the parameter type mentions any type parameter of the method, let the compiler infer the
                // return type of the default getter => allow "def foo[T](x: T = 1)" to compile.
                // This is better than always using Wildcard for inferring the result type, for example in
                //    def f(i: Int, m: Int => Int = identity _) = m(i)
                // if we use Wildcard as expected, we get "Nothing => Nothing", and the default is not usable.
                // TODO: this is a very brittle approach; I sincerely hope that Denys's research into hygiene
                //       will open the doors to a much better way of doing this kind of stuff
                val tparamNames = defTparams map { case TypeDef(_, name, _, _) => name }
                val eraseAllMentionsOfTparams = new TypeTreeSubstituter(tparamNames contains _)
                eraseAllMentionsOfTparams(rvparam.tpt match {
                  // default getter for by-name params
                  case AppliedTypeTree(_, List(arg)) if sym.hasFlag(BYNAMEPARAM) => arg
                  case t => t
                })
              }
            val defRhs = rvparam.rhs

            val defaultTree = atPos(vparam.pos.focus) {
              DefDef(Modifiers(paramFlagsToDefaultGetter(meth.flags), ddef.mods.privateWithin) | oflag, name, defTparams, defVparamss, defTpt, defRhs)
            }
            if (!isConstr)
              methOwner.resetFlag(INTERFACE) // there's a concrete member now
            val default = parentNamer.enterSyntheticSym(defaultTree)
            if (default.owner.isTerm)
              saveDefaultGetter(meth, default)
          }
          else if (baseHasDefault) {
            // the parameter does not have a default itself, but the
            // corresponding parameter in the base class does.
            sym.setFlag(DEFAULTPARAM)
          }
          posCounter += 1
          if (overrides) baseParams = baseParams.tail
        })
        if (overrides) baseParamss = baseParamss.tail
        previous :+ vparams
      }
    }

    private def valDefSig(vdef: ValDef) = {
      val ValDef(_, _, tpt, rhs) = vdef
      val result =
        if (tpt.isEmpty) {
          if (rhs.isEmpty) {
            MissingParameterOrValTypeError(tpt)
            ErrorType
          } else {
            // enterGetterSetter assigns the getter's symbol to a ValDef when there's no underlying field
            // (a deferred val or most vals defined in a trait -- see Field.noFieldFor)
            val isGetter = vdef.symbol hasFlag ACCESSOR

            val pt = {
              val valOwner = owner.owner
              // there's no overriding outside of classes, and we didn't use to do this in 2.11, so provide opt-out

              if (!isScala212 || !valOwner.isClass) WildcardType
              else {
                // normalize to getter so that we correctly consider a val overriding a def
                // (a val's name ends in a " ", so can't compare to def)
                val overridingSym = if (isGetter) vdef.symbol else vdef.symbol.getterIn(valOwner)

                // We're called from an accessorTypeCompleter, which is completing the info for the accessor's symbol,
                // which may or may not be `vdef.symbol` (see isGetter above)
                val overridden = safeNextOverriddenSymbol(overridingSym)

                if (overridden == NoSymbol || overridden.isOverloaded) WildcardType
                else valOwner.thisType.memberType(overridden).resultType
              }
            }

            def patchSymInfo(tp: Type): Unit =
              if (pt ne WildcardType) // no patching up to do if we didn't infer a prototype
                vdef.symbol setInfo (if (isGetter) NullaryMethodType(tp) else tp)

            patchSymInfo(pt)

            // derives the val's result type from type checking its rhs under the expected type `pt`
            // vdef.tpt is mutated, and `vdef.tpt.tpe` is `assignTypeToTree`'s result
            val tptFromRhsUnderPt = assignTypeToTree(vdef, typer, pt)

            // need to re-align with assignTypeToTree, as the type we're returning from valDefSig (tptFromRhsUnderPt)
            // may actually go to the accessor, not the valdef (and if assignTypeToTree returns a subtype of `pt`,
            // we would be out of synch between field and its accessors), and thus the type completer won't
            // fix the symbol's info for us -- we set it to tmpInfo above, which may need to be improved to tptFromRhsUnderPt
            if (!isGetter) patchSymInfo(tptFromRhsUnderPt)

            tptFromRhsUnderPt
          }
        } else typer.typedType(tpt).tpe

//      println(s"val: $result / ${vdef.tpt.tpe} / ")

      pluginsTypeSig(result, typer, vdef, if (tpt.isEmpty) WildcardType else result)
    }

    // Pretend we're an erroneous symbol, for now, so that we match while finding the overridden symbol,
    // but are not considered during implicit search.
    private def safeNextOverriddenSymbol(sym: Symbol, schema: Type = ErrorType): Symbol = {
      val savedInfo = sym.rawInfo
      val savedFlags = sym.rawflags
      try {
        sym setInfo schema
        sym.nextOverriddenSymbol
      } finally {
        sym setInfo savedInfo // setInfo resets the LOCKED flag, so restore saved flags as well
        sym.rawflags = savedFlags
      }
    }

    private def safeNextOverriddenSymbolLazySchema(sym: Symbol, schema: () => Type): Symbol =
      safeNextOverriddenSymbol(sym, new LazyType { override def complete(sym: Symbol): Unit = sym setInfo schema() })


    //@M! an abstract type definition (abstract type member/type parameter)
    // may take type parameters, which are in scope in its bounds
    private def typeDefSig(tdef: TypeDef) = {
      val TypeDef(_, _, tparams, rhs) = tdef
      // log("typeDefSig(" + tpsym + ", " + tparams + ")")
      val tparamSyms = typer.reenterTypeParams(tparams) //@M make tparams available in scope (just for this abstypedef)
      val tp = typer.typedType(rhs).tpe match {
        case TypeBounds(lt, rt) if (lt.isError || rt.isError) =>
          TypeBounds.empty
        case tp @ TypeBounds(lt, rt) if (tdef.symbol hasFlag JAVA) =>
          TypeBounds(lt, objToAny(rt))
        case tp =>
          tp
      }
      // see neg/bug1275, #3419
      // used to do a rudimentary kind check here to ensure overriding in refinements
      // doesn't change a type member's arity (number of type parameters), e.g.
      //
      //    trait T { type X[A] }
      //    type S = T { type X }
      //    val x: S
      //
      // X in x.X[A] will get rebound to the X in the refinement, which
      // does not take any type parameters. This mismatch does not crash
      // the compiler (anymore), but leads to weird type errors, as
      // x.X[A] will become NoType internally. It's not obvious the
      // error refers to the X in the refinement and not the original X.
      //
      // However, separate compilation requires the symbol info to be
      // loaded to do this check, but loading the info will probably
      // lead to spurious cyclic errors.  So omit the check.
      val res = GenPolyType(tparamSyms, tp)
      pluginsTypeSig(res, typer, tdef, WildcardType)
    }

    private def importSig(imp: Import) = {
      val Import(expr, selectors) = imp
      val expr1 = typer.typedQualifier(expr)

      if (expr1.symbol != null && expr1.symbol.isRootPackage)
        RootImportError(imp)

      if (expr1.isErrorTyped)
        ErrorType
      else {
        expr1 match {
          case This(_) =>
            // SI-8207 okay, typedIdent expands Ident(self) to C.this which doesn't satisfy the next case
            // TODO should we change `typedIdent` not to expand to the `Ident` to a `This`?
          case _ if treeInfo.isStableIdentifierPattern(expr1) =>
          case _ =>
            typer.TyperErrorGen.UnstableTreeError(expr1)
        }

        val newImport = treeCopy.Import(imp, expr1, selectors).asInstanceOf[Import]
        checkSelectors(newImport)
        context.unit.transformed(imp) = newImport
        // copy symbol and type attributes back into old expression
        // so that the structure builder will find it.
        expr setSymbol expr1.symbol setType expr1.tpe
        ImportType(expr1)
      }
    }


    /** Given a case class
     *   case class C[Ts] (ps: Us)
     *  Add the following methods to toScope:
     *  1. if case class is not abstract, add
     *   <synthetic> <case> def apply[Ts](ps: Us): C[Ts] = new C[Ts](ps)
     *  2. add a method
     *   <synthetic> <case> def unapply[Ts](x: C[Ts]) = <ret-val>
     *  where <ret-val> is the caseClassUnapplyReturnValue of class C (see UnApplies.scala)
     *
     * @param cdef is the class definition of the case class
     * @param namer is the namer of the module class (the comp. obj)
     */
    def addApplyUnapply(cdef: ClassDef, namer: Namer) {
      if (!cdef.symbol.hasAbstractFlag)
        namer.enterSyntheticSym(caseModuleApplyMeth(cdef))

      val primaryConstructorArity = treeInfo.firstConstructorArgs(cdef.impl.body).size
      if (primaryConstructorArity <= MaxTupleArity)
        namer.enterSyntheticSym(caseModuleUnapplyMeth(cdef))
    }

    def addCopyMethod(cdef: ClassDef, namer: Namer) {
      caseClassCopyMeth(cdef) foreach namer.enterSyntheticSym
    }

    /**
     * TypeSig is invoked by monoTypeCompleters. It returns the type of a definition which
     * is then assigned to the corresponding symbol (typeSig itself does not need to assign
     * the type to the symbol, but it can if necessary).
     */
    def typeSig(tree: Tree, annotSigs: List[AnnotationInfo]): Type = {
      if (annotSigs.nonEmpty) annotate(tree.symbol, annotSigs)

      try tree match {
        case member: MemberDef => createNamer(tree).memberSig(member)
        case imp: Import       => importSig(imp)
      } catch typeErrorHandler(tree, ErrorType)
    }

    /* For definitions, transform Annotation trees to AnnotationInfos, assign
     * them to the sym's annotations. Type annotations: see Typer.typedAnnotated
     * We have to parse definition annotations here (not in the typer when traversing
     * the MemberDef tree): the typer looks at annotations of certain symbols; if
     * they were added only in typer, depending on the compilation order, they may
     * or may not be visible.
     */
    def annotSig(annotations: List[Tree]): List[AnnotationInfo] =
      annotations filterNot (_ eq null) map { ann =>
        val ctx = typer.context
        // need to be lazy, #1782. enteringTyper to allow inferView in annotation args, SI-5892.
        AnnotationInfo lazily {
          enteringTyper {
            newTyper(ctx.makeNonSilent(ann)) typedAnnotation ann
          }
        }
      }

    private def annotate(sym: Symbol, annotSigs: List[AnnotationInfo]): Unit = {
      sym setAnnotations annotSigs

      // TODO: meta-annotations to indicate where module annotations should go (module vs moduleClass)
      if (sym.isModule) sym.moduleClass setAnnotations annotSigs
      else if (sym.isTypeSkolem) sym.deSkolemize setAnnotations annotSigs
    }

    // TODO OPT: move to method on MemberDef?
    private def memberSig(member: MemberDef) =
      member match {
        case ddef: DefDef    => methodSig(ddef)
        case vdef: ValDef    => valDefSig(vdef)
        case tdef: TypeDef   => typeDefSig(tdef)
        case cdef: ClassDef  => classSig(cdef)
        case mdef: ModuleDef => moduleSig(mdef)
        // skip PackageDef
      }

    def includeParent(tpe: Type, parent: Symbol): Type = tpe match {
      case PolyType(tparams, restpe) =>
        PolyType(tparams, includeParent(restpe, parent))
      case ClassInfoType(parents, decls, clazz) =>
        if (parents exists (_.typeSymbol == parent)) tpe
        else ClassInfoType(parents :+ parent.tpe, decls, clazz)
      case _ =>
        tpe
    }

    class LogTransitions[S](onEnter: S => String, onExit: S => String) {
      val enabled = settings.debug.value
      @inline final def apply[T](entity: S)(body: => T): T = {
        if (enabled) log(onEnter(entity))
        try body
        finally if (enabled) log(onExit(entity))
      }
    }
    private val logDefinition = new LogTransitions[Symbol](
      sym => "[define] >> " + sym.flagString + " " + sym.fullLocationString,
      sym => "[define] << " + sym
    )

    /** Convert Java generic array type T[] to (T with Object)[]
     *  (this is necessary because such arrays have a representation which is incompatible
     *   with arrays of primitive types.)
     *
     *  @note the comparison to Object only works for abstract types bounded by classes that are strict subclasses of Object
     *  if the bound is exactly Object, it will have been converted to Any, and the comparison will fail
     *
     *  see also sigToType
     */
    private object RestrictJavaArraysMap extends TypeMap {
      def apply(tp: Type): Type = tp match {
        case TypeRef(pre, ArrayClass, List(elemtp))
        if elemtp.typeSymbol.isAbstractType && !(elemtp <:< ObjectTpe) =>
          TypeRef(pre, ArrayClass, List(intersectionType(List(elemtp, ObjectTpe))))
        case _ =>
          mapOver(tp)
      }
    }

    /** Check that symbol's definition is well-formed. This means:
     *   - no conflicting modifiers
     *   - `abstract` modifier only for classes
     *   - `override` modifier never for classes
     *   - `def` modifier never for parameters of case classes
     *   - declarations only in mixins or abstract classes (when not @native)
     */
    def validate(sym: Symbol) {
      import SymValidateErrors._
      def fail(kind: SymValidateErrors.Value) = SymbolValidationError(sym, kind)

      def checkNoConflict(flag1: Int, flag2: Int) = {
        if (sym hasAllFlags flag1.toLong | flag2)
          IllegalModifierCombination(sym, flag1, flag2)
      }
      if (sym.isImplicit) {
        if (sym.isConstructor)
          fail(ImplicitConstr)
        if (!(sym.isTerm || (sym.isClass && !sym.isTrait)))
          fail(ImplicitNotTermOrClass)
        if (sym.isTopLevel)
          fail(ImplicitAtToplevel)
      }
      if (sym.isClass) {
        checkNoConflict(IMPLICIT, CASE)
        if (sym.isAnyOverride && !sym.hasFlag(TRAIT))
          fail(OverrideClass)
      } else {
        if (sym.isSealed)
          fail(SealedNonClass)
        if (sym.hasFlag(ABSTRACT))
          fail(AbstractNonClass)
      }

      if (sym.isConstructor && sym.isAnyOverride)
        fail(OverrideConstr)
      if (sym.isAbstractOverride) {
          if (!sym.owner.isTrait)
            fail(AbstractOverride)
          if(sym.isType)
            fail(AbstractOverrideOnTypeMember)
      }
      if (sym.isLazy && sym.hasFlag(PRESUPER))
        fail(LazyAndEarlyInit)
      if (sym.info.typeSymbol == FunctionClass(0) && sym.isValueParameter && sym.owner.isCaseClass)
        fail(ByNameParameter)
      if (sym.isTrait && sym.isFinal && !sym.isSubClass(AnyValClass))
        checkNoConflict(ABSTRACT, FINAL)

      if (sym.isDeferred) {
        def checkWithDeferred(flag: Int) = {
          if (sym hasFlag flag)
            AbstractMemberWithModiferError(sym, flag)
        }
        // Is this symbol type always allowed the deferred flag?
        def symbolAllowsDeferred = (
             sym.isValueParameter
          || sym.isTypeParameterOrSkolem
          || (sym.isAbstractType && sym.owner.isClass)
          || context.tree.isInstanceOf[ExistentialTypeTree]
        )
        // Does the symbol owner require no undefined members?
        def ownerRequiresConcrete = (
             !sym.owner.isClass
          ||  sym.owner.isModuleClass
          ||  sym.owner.isAnonymousClass
        )
        if (sym hasAnnotation NativeAttr)
          sym resetFlag DEFERRED
        else {
          if (!symbolAllowsDeferred && ownerRequiresConcrete) fail(AbstractVar)

          checkWithDeferred(PRIVATE)
          checkWithDeferred(FINAL)
        }
      }

      if (!sym.isJavaEnum)
        checkNoConflict(FINAL, SEALED)
      checkNoConflict(PRIVATE, PROTECTED)
      // checkNoConflict(PRIVATE, OVERRIDE) // this one leads to bad error messages like #4174, so catch in refchecks
      // checkNoConflict(PRIVATE, FINAL)    // can't do this because FINAL also means compile-time constant
      // checkNoConflict(ABSTRACT, FINAL)   // this one gives a bad error for non-@inline classes which extend AnyVal
      // @PP: I added this as a sanity check because these flags are supposed to be
      // converted to ABSOVERRIDE before arriving here.
      checkNoConflict(ABSTRACT, OVERRIDE)
    }

    // MS: End of original Namer

    // MS: macro paradise

    //val expanderErrorGen = new ErrorGen(namer.typer)
    //import expanderErrorGen._

    import Mode._
    import typer.TyperErrorGen._
    import treeInfo.AnnotationZipper

    def prepareAnnotationMacro(ann: Tree, mann: Symbol, sym: Symbol, annottee: Tree, expandee: Tree): Tree = {
      val companion = if (expandee.isInstanceOf[ClassDef]) patchedCompanionSymbolOf(sym, context) else NoSymbol
      val companionSource = if (!isWeak(companion)) attachedSource(companion) else EmptyTree
      val expandees = List(annottee, expandee, companionSource).distinct.filterNot(_.isEmpty)
      val safeExpandees = expandees.map(expandee => duplicateAndKeepPositions(expandee)).map(_.setSymbol(NoSymbol))
      val prefix = Select(ann, nme.macroTransform) setSymbol mann.info.member(nme.macroTransform) setPos ann.pos
      Apply(prefix, safeExpandees) setPos ann.pos
    }

    def expandAnnotationMacro(original: Tree, expandee: Tree): Option[List[Tree]] = {
      val sym = original.symbol
      val companion = if (original.isInstanceOf[ClassDef]) patchedCompanionSymbolOf(sym, context) else NoSymbol
      val wasWeak = isWeak(companion)
      val wasTransient = companion == NoSymbol || companion.isSynthetic
      def rollThroughImports(context: Context): Context = {
        if (context.isInstanceOf[ImportContext]) rollThroughImports(context.outer)
        else context
      }
      val typer = {
        // expanding at top level => allow the macro to see everything
        if (sym.isTopLevel) newTyper(context)
        // expanding at template level => only allow to see outside of the enclosing class
        // we have to skip two contexts:
        //  1) the Template context that hosts members
        //  2) the ImplDef context that hosts type params (and just them?)
        // upd. actually, i don't think we should skip the second context
        // that doesn't buy us absolutely anything wrt robustness
        else if (sym.owner.isClass) newTyper(rollThroughImports(context).outer)
        // expanding at block level => only allow to see outside of the block
        else newTyper(rollThroughImports(context).outer)
      }
      def onlyIfExpansionAllowed[T](expand: => Option[T]): Option[T] = {
        if (settings.Ymacroexpand.value == settings.MacroExpand.None) None
        else {
          val oldYmacroexpand = settings.Ymacroexpand.value
          try { settings.Ymacroexpand.value = settings.MacroExpand.Normal; expand }
          catch { case ex: Exception => settings.Ymacroexpand.value = oldYmacroexpand; throw ex }
        }
      }
      def expand(): Option[Tree] = (new DefMacroExpander(typer, expandee, NOmode, WildcardType) {
        override def onSuccess(expanded: Tree) = expanded
      })(expandee) match {
        case tree if tree.isErroneous => None
        case tree => Some(tree)
      }
      def extract(expanded: Tree): List[Tree] = expanded match {
        case Block(stats, Literal(Constant(()))) => stats // ugh
        case tree => List(tree)
      }
      def validate(expanded: List[Tree]): Option[List[Tree]] = {
        if (sym.owner.isPackageClass) {
          original match {
            case ClassDef(_, originalName, _, _) =>
              expanded match {
                case (expandedClass @ ClassDef(_, className, _, _)) :: Nil
                if className == originalName && wasWeak =>
                  attachExpansion(sym, List(expandedClass))
                  attachExpansion(companion, Nil)
                  Some(expanded)
                case (expandedCompanion @ ModuleDef(_, moduleName, _)) :: (expandedClass @ ClassDef(_, className, _, _)) :: Nil
                if className == originalName && moduleName == originalName.toTermName =>
                  attachExpansion(sym, if (wasWeak) List(expandedClass, expandedCompanion) else List(expandedClass))
                  attachExpansion(companion, List(expandedCompanion))
                  Some(expanded)
                case (expandedClass @ ClassDef(_, className, _, _)) :: (expandedCompanion @ ModuleDef(_, moduleName, _)) :: Nil
                if className == originalName && moduleName == originalName.toTermName =>
                  attachExpansion(sym, if (wasWeak) List(expandedClass, expandedCompanion) else List(expandedClass))
                  attachExpansion(companion, List(expandedCompanion))
                  Some(expanded)
                case _ =>
                  if (wasWeak) MacroAnnotationTopLevelClassWithoutCompanionBadExpansion(expandee)
                  else MacroAnnotationTopLevelClassWithCompanionBadExpansion(expandee)
                  None
              }
            case ModuleDef(_, originalName, _) =>
              expanded match {
                case (expandedModule @ ModuleDef(_, expandedName, _)) :: Nil if expandedName == originalName =>
                  attachExpansion(sym, List(expandedModule))
                  Some(expanded)
                case _ =>
                  MacroAnnotationTopLevelModuleBadExpansion(expandee)
                  None
              }
          }
        } else {
          if (wasTransient) {
            attachExpansion(sym, expanded)
            attachExpansion(companion, Nil)
          } else {
            def companionRelated(tree: Tree) = tree.isInstanceOf[ModuleDef] && tree.asInstanceOf[ModuleDef].name == companion.name
            val (forCompanion, forSym) = expanded.partition(companionRelated)
            attachExpansion(sym, forSym)
            attachExpansion(companion, forCompanion)
          }
          Some(expanded)
        }
      }
      for {
        lowlevelExpansion <- onlyIfExpansionAllowed(expand())
        expansion <- Some(extract(lowlevelExpansion))
        duplicated = expansion.map(duplicateAndKeepPositions)
        validatedExpansion <- validate(duplicated)
      } yield validatedExpansion
    }

    def expandMacroAnnotations(stats: List[Tree]): List[Tree] = {
      def mightNeedTransform(stat: Tree): Boolean = stat match {
        case stat: DocDef => mightNeedTransform(stat.definition)
        case stat: MemberDef => isMaybeExpandee(stat.symbol) || hasAttachedExpansion(stat.symbol)
        case _ => false
      }
      def rewrapAfterTransform(stat: Tree, transformed: List[Tree]): List[Tree] = (stat, transformed) match {
        case (stat @ DocDef(comment, _), List(transformed: MemberDef)) => List(treeCopy.DocDef(stat, comment, transformed))
        case (stat @ DocDef(comment, _), List(transformed: DocDef)) => List(transformed)
        case (_, Nil | List(_: MemberDef)) => transformed
        case (_, unexpected) => unexpected // NOTE: who knows how people are already using macro annotations, so it's scary to fail here
      }
      if (phase.id > currentRun.typerPhase.id || !stats.exists(mightNeedTransform)) stats
      else stats.flatMap(stat => {
        if (mightNeedTransform(stat)) {
          val sym = stat.symbol
          assert(sym != NoSymbol, (sym, stat))
          if (isMaybeExpandee(sym)) {
            def assert(what: Boolean) = Predef.assert(what, s"${sym.accurateKindString} ${sym.rawname}#${sym.id} with ${sym.rawInfo.kind}")
            assert(sym.rawInfo.isInstanceOf[Namer#MaybeExpandeeCompleter])
            sym.rawInfo.completeOnlyExpansions(sym)
            assert(!sym.rawInfo.isInstanceOf[Namer#MaybeExpandeeCompleter])
          }
          val derivedTrees = attachedExpansion(sym).getOrElse(List(stat))
          val (me, others) = derivedTrees.partition(_.symbol == sym)
          rewrapAfterTransform(stat, me) ++ expandMacroAnnotations(others)
        } else {
          List(stat)
        }
      })
    }

    def enterSymParadise(tree: Tree): Context = {
      def dispatch() = {
        var returnContext = context
        tree match {
          case DocDef(_, mdef) =>
            enterSym(mdef)
          case tree @ Import(_, _) =>
            createAssignAndEnterSymbol(tree)
            finishSymbol(tree)
            returnContext = context.make(tree)
          case tree: MemberDef =>
            createAssignAndEnterSymbol(tree)
            finishSymbol(tree)
          case _ =>
        }
        returnContext
      }
      tree.symbol match {
        case NoSymbol => try dispatch() catch typeErrorHandler(tree, context)
        case sym      => enterExistingSym(sym, tree)
      }
    }

    def createAssignAndEnterSymbol(tree: Tree, mask: Long = -1L): Symbol = {
      def coreCreateAssignAndEnterSymbol = {
        val sym = tree match {
          case PackageDef(pid, _) => createPackageSymbol(tree.pos, pid) // package symbols are entered elsewhere
          case imp: Import        => createImportSymbol(imp) // import symbols are dummies, no need to enter them anywhere
          case mdef: MemberDef    => enterInScope(setPrivateWithin(mdef, createMemberSymbol(mdef, mdef.name, mask)))
          case _                  => abort("Unexpected tree: " + tree)
        }
        if (isPastTyper) sym.name.toTermName match {
          case nme.IMPORT | nme.OUTER | nme.ANON_CLASS_NAME | nme.ANON_FUN_NAME | nme.CONSTRUCTOR => ()
          case _                                                                                  =>
            tree match {
              case md: DefDef => log("[+symbol] " + sym.debugLocationString)
              case _          =>
            }
        }
        tree.symbol = sym
        sym
      }
      def deriveSymbolFromSource(tree: Tree)(pf: PartialFunction[Tree, Symbol]): Symbol = {
        val sym = pf(tree)
        // can't do this in coreCreateAssignAndEnterSymbol
        // because then we won't get to update sources for redefinitions
        // this might be crucial when we have classfiles of the definition we're currently compiling
        attachSource(sym, tree)
        sym
      }
      deriveSymbolFromSource(tree) {
        case tree @ ClassDef(mods, name, _, _) =>
          val existing = context.scope.lookup(name)
          val isRedefinition = (
               existing.isType
            && existing.isTopLevel
            && context.scope == existing.owner.info.decls
            && (
                 currentRun.canRedefine(existing) ||
                 isExpanded(existing)
               )
          )
          val clazz: Symbol = {
            if (isRedefinition) {
              updatePosFlags(existing, tree.pos, mods.flags)
              setPrivateWithin(tree, existing)
              clearRenamedCaseAccessors(existing)
              tree.symbol = existing
              existing
            }
            else coreCreateAssignAndEnterSymbol setFlag inConstructorFlag
          }
          if (clazz.isClass && clazz.isTopLevel) {
            if (clazz.sourceFile != null && clazz.sourceFile != contextFile)
              devWarning(s"Source file mismatch in $clazz: ${clazz.sourceFile} vs. $contextFile")

            clazz.associatedFile = contextFile
            if (clazz.sourceFile != null) {
              assert(currentRun.canRedefine(clazz) || clazz.sourceFile == currentRun.symSource(clazz), clazz.sourceFile)
              currentRun.symSource(clazz) = clazz.sourceFile
            }
            registerTopLevelSym(clazz)
            assert(clazz.name.toString.indexOf('(') < 0, clazz.name)  // )
          }
          clazz
        case tree @ ModuleDef(mods, name, _) =>
          var m: Symbol = context.scope lookupModule name
          val moduleFlags = mods.flags | MODULE
          // TODO: inCurrentScope(m) check that's present in vanilla Namer is omitted here
          // this fixes SI-3772, but may break something else - I didn't have time to look into that
          if (m.isModule && !m.hasPackageFlag && (currentRun.canRedefine(m) || m.isSynthetic || isExpanded(m))) {
            // This code accounts for the way the package objects found in the classpath are opened up
            // early by the completer of the package itself. If the `packageobjects` phase then finds
            // the same package object in sources, we have to clean the slate and remove package object
            // members from the package class.
            //
            // TODO SI-4695 Pursue the approach in https://github.com/scala/scala/pull/2789 that avoids
            //      opening up the package object on the classpath at all if one exists in source.
            if (m.isPackageObject) {
              val packageScope = m.enclosingPackageClass.rawInfo.decls
              packageScope.filter(_.owner != m.enclosingPackageClass).toList.foreach(packageScope unlink _)
            }
            updatePosFlags(m, tree.pos, moduleFlags)
            setPrivateWithin(tree, m)
            m.moduleClass andAlso (setPrivateWithin(tree, _))
            context.unit.synthetics -= m
            tree.symbol = m
          }
          else {
            m = coreCreateAssignAndEnterSymbol
            m.moduleClass setFlag moduleClassFlags(moduleFlags)
            setPrivateWithin(tree, m.moduleClass)
          }
          m.moduleClass setInfo namerOf(m).moduleClassTypeCompleter(tree)
          if (m.isTopLevel && !m.hasPackageFlag) {
            m.moduleClass.associatedFile = contextFile
            currentRun.symSource(m) = m.moduleClass.sourceFile
            registerTopLevelSym(m)
          }
          m
        case _ =>
          coreCreateAssignAndEnterSymbol
      }
    }

    // reimplemented to integrate with weakEnsureCompanionObject
    def ensureCompanionObjectParadise(cdef: ClassDef, creator: ClassDef => Tree = companionModuleDef(_)): Symbol = {
      val m = patchedCompanionSymbolOf(cdef.symbol, context)
      def synthesizeTree = atPos(cdef.pos.focus)(creator(cdef))
      if (m != NoSymbol && currentRun.compiles(m) && !isWeak(m)) m
      else unmarkWeak(enterSyntheticSym(synthesizeTree))
    }

    /** Does the same as `ensureCompanionObject`, but also makes sure that the returned symbol destroys itself
     *  if noone ends up using it (either by calling `ensureCompanionObject` or by `finishSymbol`).
     */
    // TODO: deduplicate
    def weakEnsureCompanionObject(cdef: ClassDef, creator: ClassDef => Tree = companionModuleDef(_)): Symbol = {
      val m = patchedCompanionSymbolOf(cdef.symbol, context)
      if (m != NoSymbol && currentRun.compiles(m)) m
      else { val mdef = atPos(cdef.pos.focus)(creator(cdef)); enterSym(mdef); markWeak(mdef.symbol) }
    }

    def finishSymbol(tree: Tree) {
      // annotations on parameters expand together with their owners
      // therefore when we actually get to enter the parameters, we shouldn't even bother checking
      // TODO: we don't handle primary ctors that might get spuriously marked as maybe expandees because of primary paramss
      val aprioriNotExpandable = (context.tree, tree) match {
        case (ClassDef(_, _, _, _), TypeDef(_, _, _, _)) => true
        case (Template(_, _, _), ValDef(mods, _, _, _)) if mods.isParamAccessor => true
        // vparamss of primary ctors are entered in `enterValueParams`, which doesn't call us
        case (DefDef(_, _, _, _, _, _), TypeDef(_, _, _, _)) => true
        // vparamss of normal methods are also entered in `enterValueParams`, which doesn't call us
        case (TypeDef(_, _, _, _), TypeDef(_, _, _, _)) => true
        case _ => false
      }

      if (aprioriNotExpandable) finishSymbolNotExpandee(tree)
      else {
        treeInfo.getAnnotationZippers(tree) match {
          case Nil => finishSymbolNotExpandee(tree)
          case zippers => finishSymbolMaybeExpandee(tree, zippers)
        }

        // this will only show companions defined above ourselves
        // so when finishing `class C` in `{ class C; object C }`
        // we won't see `object C` in `companion` - we will see NoSymbol
        // that's the limitation of how namer works, but nevertheless it's not a problem for us
        // because if finishing `class C` doesn't set up the things, finishing `object C` will
        val sym = tree.symbol
        val companion = patchedCompanionSymbolOf(sym, context)

        tree match {
          // TODO: should we also support annotations on modules expanding companion classes?
          case tree @ ClassDef(_, _, _, _) if isMaybeExpandee(sym) =>
            val wasExpanded = isExpanded(companion)
            val m = weakEnsureCompanionObject(tree)
            finishSymbolMaybeExpandeeCompanion(attachedSource(m), m, sym)
            if (wasExpanded) markExpanded(m) // why is this necessary? see files/run/macro-annotation-recursive-class
                                             // TODO: in general, this first call to FSMEC usually only brings grief
                                             // can we get rid of it completely without having to sweep its results under the carpet?
          case tree @ ModuleDef(_, _, _) if isMaybeExpandee(companion) =>
            finishSymbolMaybeExpandeeCompanion(tree, sym, companion)
          case _ =>
        }
      }
    }

    def finishSymbolNotExpandee(tree: Tree) {
      val sym = tree.symbol
      def savingLock[T](op: => T): T = {
        val wasLocked = sym.hasFlag(LOCKED)
        val result = op
        if (wasLocked) sym.setFlag(LOCKED)
        result
      }
      savingLock(tree match {
        case tree @ PackageDef(_, _) =>
          newNamer(context.make(tree, sym.moduleClass, sym.info.decls)) enterSyms tree.stats
        case tree @ ClassDef(mods, name, tparams, impl) =>
          sym setInfo completerOf(tree)
          if (mods.isCase) {
            val m = ensureCompanionObjectParadise(tree, caseModuleDef)
            m.moduleClass.updateAttachment(new ClassForCaseCompanionAttachment(tree))
          }
          val hasDefault = impl.body exists treeInfo.isConstructorWithDefault
          if (hasDefault) {
            val m = ensureCompanionObjectParadise(tree)
            m.updateAttachment(new ConstructorDefaultsAttachment(tree, null))
          }
          val owner = tree.symbol.owner
          if (settings.warnPackageObjectClasses && owner.isPackageObjectClass && !mods.isImplicit) {
            reporter.warning(tree.pos,
              "it is not recommended to define classes/objects inside of package objects.\n" +
              "If possible, define " + tree.symbol + " in " + owner.skipPackageObject + " instead."
            )
          }
          // Suggested location only.
          if (mods.isImplicit) {
            if (treeInfo.primaryConstructorArity(tree) == 1) {
              log("enter implicit wrapper "+tree+", owner = "+owner)
              enterImplicitWrapper(tree)
            }
            else MultipleParametersImplicitClassError(tree)
          }
          validateCompanionDefs(tree)
        case tree @ ModuleDef(_, _, _) =>
          unmarkWeak(sym)
          sym setInfo completerOf(tree)
          validateCompanionDefs(tree)
        case tree @ ValDef(_, _, _, _) =>
          val isScala = !context.unit.isJava
          if (isScala) {
            if (nme.isSetterName(tree.name)) ValOrVarWithSetterSuffixError(tree)
            if (tree.mods.isPrivateLocal && tree.mods.isCaseAccessor) PrivateThisCaseClassParameterError(tree)
          }
          if (isScala && deriveAccessors(tree)) {
            // when refactoring enterSym, I needed to decouple symbol creation and various syntheses
            // so that annotation expansion mechanism could be installed in-between of those
            // it went well except for one thing - ValDef symbol creation is very closely tied to syntheses
            // because depending on whether the ValDef is a val, var or a lazy val, different symbols need to be generated
            // since I didn't have much time (and, back then, much understanding), I just decided to create dummies
            // that live only to stand in as potential annottees and get destroyed if any sort of synthesis is necessary
            // TODO: this is obviously ugly and needs to be fixed
            context.scope.unlink(tree.symbol)
            tree.symbol setInfo NoType
            enterGetterSetter(tree)
          } else {
            tree.symbol setInfo completerOf(tree)
          }
          if (isEnumConstant(tree))
            tree.symbol setInfo ConstantType(Constant(tree.symbol))
        case tree @ DefDef(_, nme.CONSTRUCTOR, _, _, _, _) =>
          sym setInfo completerOf(tree)
        case tree @ DefDef(mods, name, tparams, _, _, _) =>
          val bridgeFlag = if (mods hasAnnotationNamed tpnme.bridgeAnnot) BRIDGE | ARTIFACT else 0
          sym setFlag bridgeFlag
          if (name == nme.copy && sym.isSynthetic) {
            enterCopyMethod(tree)
          } else if (name == nme.apply && sym.hasAllFlags(SYNTHETIC | CASE)) {
            sym setInfo caseApplyMethodCompleter(tree, completerOf(tree).asInstanceOf[LockingTypeCompleter])
          } else {
            sym setInfo completerOf(tree)
          }
        case tree @ TypeDef(_, _, _, _) =>
          sym setInfo completerOf(tree)
        case tree @ Import(_, _) =>
          namerOf(tree.symbol) importTypeCompleter tree
      })
    }

    // we have several occasions when so called "maybe expandees" need special care
    // ("maybe expandees" = annotated members, which might or might not be annotated with a macro expansion)
    // 1) (when called by Symbol.info) trigger the MaybeExpandeeCompleter and then immediately recur into a fresh completer
    //    if we don't recur, we're doomed to fail, because there are only so many retries that Symbol.info can tolerate
    //    and this retry threshold is already fine-tuned to the current chain of completers, which makes MaybeExpandeeCompleter one too many
    // 2) (when called by expandMacroAnnotations from templateSig or typedBlock) in this situation noone needs us to fully complete
    //    the underlying symbol. just making sure that we don't have any annotations to expand is the least and the most we should do.
    //    if we're overeager like in mode #1, we might easily induce cyclic reference errors (like in tests/run/macro-annotations-packageobject)
    // 3) (when called by Symbol.typeParams) this one is different from Symbol.info, because it calls load, not complete
    //    from what I understand, this separation exists because it takes much less effort to figure out tparams rather than the full signature
    //    for example, vanilla completers assigned in namer are created with typeParams already known
    //    you can see for yourself in the distinction between monoTypeCompleter and PolyTypeCompleter
    //    therefore, just as with Symbol.info we need to trigger the MaybeExpandeeCompleter
    //    and then not forget to recur into the fresh completer's load, again because of the retry limit baked into Symbol.typeParams
    // 4) TODO: (when called by Symbol.unsafeTypeParams) figure out what's the deal with them
    //    existence of this method profoundly scares me, even though I never had a problem with it
    abstract class MaybeExpandeeCompleter(val tree: Tree) extends LockingTypeCompleter with FlagAssigningCompleter {
      def destroy(syms: Symbol*) = {
        for (sym <- syms) {
          context.unit.synthetics -= sym
          context.scope.unlink(sym)
          sym setInfo NoType
          sym.moduleClass setInfo NoType
          sym.removeAttachment[SymbolCompleterAttachment]
        }
      }

      def complete(sym: Symbol, onlyExpansions: Boolean) = {
        _lockedCount += 1
        try completeImpl(sym, onlyExpansions)
        finally _lockedCount -= 1
      }

      override def completeImpl(sym: Symbol): Unit = {
        completeImpl(sym, onlyExpansions = false)
      }

      def completeImpl(sym: Symbol, onlyExpansions: Boolean): Unit = {
        val thisCompleter = sym.rawInfo
        maybeExpand()
        assert(sym.rawInfo != thisCompleter, s"${sym.accurateKindString} ${sym.rawname}#${sym.id} with $kind")
        if (onlyExpansions) sym.rawInfo.completeOnlyExpansions(sym)
        else sym.rawInfo.complete(sym)
      }

      override def load(sym: Symbol): Unit = {
        this.completeOnlyExpansions(sym)
        sym.rawInfo.load(sym)
      }

      def maybeExpand(): Unit // TODO: should I also pass `sym` here?
    }

    abstract class MaybeExpandeeCompanionCompleter(tree: Tree) extends MaybeExpandeeCompleter(tree)

    implicit class RichType(tpe: Type) {
      def completeOnlyExpansions(sym: Symbol) = tpe match {
        case mec: Namer#MaybeExpandeeCompleter => mec.complete(sym, onlyExpansions = true)
        case c => ()
      }
    }

    def finishSymbolMaybeExpandee(tree: Tree, annZippers: List[AnnotationZipper]) {
      val sym = tree.symbol
      unmarkWeak(sym)
      markMaybeExpandee(sym)
      sym.setInfo(new MaybeExpandeeCompleter(tree) {
        override def kind = s"maybeExpandeeCompleter for ${sym.accurateKindString} ${sym.rawname}#${sym.id}"
        override def maybeExpand(): Unit = {
          val companion = if (tree.isInstanceOf[ClassDef]) patchedCompanionSymbolOf(sym, context) else NoSymbol

          def maybeExpand(annotation: Tree, annottee: Tree, maybeExpandee: Tree): Option[List[Tree]] = {
            val treeInfo.Applied(Select(New(tpt), nme.CONSTRUCTOR), _, _) = annotation
            val mann = probeMacroAnnotation(context, tpt)
            if (mann.isMacroAnnotation && context.macrosEnabled) {
              assert(!currentRun.compiles(mann), mann)
              val annm = prepareAnnotationMacro(annotation, mann, sym, annottee, maybeExpandee)
              expandAnnotationMacro(tree, annm)
              // if we encounter an error, we just return None, so that other macro annotations can proceed
              // this is unlike macroExpand1 when any error in an expandee blocks expansions
              // there it's necessary in order not to exacerbate typer errors
              // but when manning we aren't in typer, so we don't have to do as macroExpand1 does
              // and also there's a good reason not to ban other macro annotations
              // if we do ban them, we might get spurious compilation errors from non-existent members that could've been generated
            } else {
              None
            }
          }

          annZippers.toStream.flatMap(annz => maybeExpand(annz.annotation, annz.annottee, annz.owner)).headOption match {
            case Some(expanded) =>
              tellReplAboutExpansion(sym, companion, expanded)
              markExpanded(sym)
              markExpanded(companion)
              // expansion brings new trees, probably wildly different from current ones. what do we do?
              // the most robust thing would be to destroy ourselves (us and our companion), but we can't do that at top level
              // therefore at top level we don't destroy, but rather rely on enterSyms to redefine ourselves
              // however when nested we go all out
              // TODO: unlinking distorts the order of symbols in scope
              // note however that trees (calculated by expandMacroAnnotations) will be generated in correct order
              if (!sym.isTopLevel) destroy(sym, companion)
              enterSyms(expanded) // TODO: we can't reliably expand into imports, because they won't be accounted by definitions below us
            case None =>
              markNotExpandable(sym)
              finishSymbolNotExpandee(tree)
          }

          // take care of the companion if it's no longer needed
          // we can't do this in companion's completer, because that one isn't guaranteed to ever be called
          val expandedWithoutCompanion = isExpanded(sym) && attachedExpansion(companion).map(_.isEmpty).getOrElse(false)
          val companionHasReemerged = expandedWithoutCompanion && sym.isTopLevel && !isWeak(companion)
          val notExpandableWeakCompanion = isNotExpandable(sym) && isWeak(companion)
          if ((expandedWithoutCompanion && !companionHasReemerged) || notExpandableWeakCompanion) destroy(companion)
        }
      })
    }

    // how do we make sure that this completer falls back to the vanilla completer if the companion ends up not expanding?
    // well, if a module symbol has a maybeExpandee companion then the last two calls to its setInfo will be one of:
    //   * non-FSMEC completer for the module and then FSMEC => fallback should call native completer
    //   * FSMEC from enterSyntheticSym for a phantom module and then FSMEC again => fallback should do nothing
    // now it's easy to see that both are correctly handled here
    def finishSymbolMaybeExpandeeCompanion(tree: Tree, m: Symbol, c: Symbol) {
      val worthBackingUp = !m.rawInfo.isInstanceOf[Namer#MaybeExpandeeCompanionCompleter]
      if (worthBackingUp) backupCompleter(m)
      markMaybeExpandee(m)
      m.setInfo(new MaybeExpandeeCompanionCompleter(tree) {
        override def kind = s"maybeExpandeeCompanionCompleter for ${m.rawname}#${m.id}"
        override def maybeExpand(): Unit = {
          c.rawInfo.completeOnlyExpansions(c)
          // this is a very tricky part of annotation expansion
          // because now, after deferring to our companion's judgement for a while, we have to ourselves figure out:
          //   1) whether we should start completing on our own
          //   2) if we should do it on our own, then how exactly
          // 1 is easy. If our companion's expansion has destroyed us (or hasn't materialized us if we were weak)
          // then we no longer care and we silently go into oblivion. Otherwise, we should take care of ourselves.
          // 2 is hard, because we have two distinct situations to handle:
          //   2a) isExpanded(c) is true, which means that our companion has just expanded
          //   2b) isNotExpandable(c) is true, which means that our companion has just been deemed unexpandable
          // 2a is simple, because it means that we don't have to do anything, as we've either got destroyed
          // or we've got entered in `enterSyms(expanded)` that follows expansions.
          // 2b is tricky, because it means that we need to fall back to the most recent non-FSMEC completer.
          // The hardest part here is that we can't just get to the completer that was preceding `this` as m.rawInfo
          // (otherwise we run into issue #9, for more details see history of this change). Instead we need to track m's type history.
          val destroyedDuringExpansion = m.rawInfo == NoType
          val failedToMaterializeDuringExpansion = isWeak(m)
          val aliveAndKicking = !destroyedDuringExpansion && !failedToMaterializeDuringExpansion
          if (aliveAndKicking && isNotExpandable(c)) {
            if (worthBackingUp) restoreCompleter(m)
            val maybeExpandee = m.rawInfo.isInstanceOf[Namer#MaybeExpandeeCompleter]
            if (maybeExpandee) markMaybeExpandee(m) else markNotExpandable(m)
          }
        }
      })
    }

    // mostly copy/pasted and adapted from typedIdent
    // adaptations = ignore error reporting + ignore java + don't force symbols being compiled
    // the last requirement leads to us being imprecise in some situation wrt normal name resolution
    // but that's okay, since it's the only way for manns to remain modular and not to cripple normal annotations
    def probeMacroAnnotation(context: Context, tpt: Tree): Symbol = {
      // SAFE HELPERS (can't cause unnecessary completions)
      def reallyExists(sym: Symbol) = { if (newTyper(context).isStale(sym)) sym.setInfo(NoType); exists(sym) }
      def qualifies(sym: Symbol): Boolean = sym.hasRawInfo && reallyExists(sym)

      // UNSAFE HELPERS (need to guard against unnecessary completions)
      def canDefineMann(sym: Symbol): Boolean = !currentRun.compiles(sym)
      def exists(sym: Symbol) = if (canDefineMann(sym)) sym.exists else false
      def importedSymbol(imp: ImportInfo, name: Name): Symbol = { // TODO: be more precise in reproducing importSig and importedSymbol
        val impContext = context.enclosingContextChain.find(_.tree.symbol == imp.tree.symbol).get
        val sym = imp.tree.cached("importQualProbe", probeMacroAnnotation(impContext.outer, imp.tree.expr))
        val pre = if (reallyExists(sym) && isAccessible(impContext, sym)) sym.tpe else NoType
        var result: Symbol = NoSymbol
        var renamed = false
        var selectors = imp.tree.selectors
        def current = selectors.head
        while (selectors != Nil && result == NoSymbol) {
          if (current.rename == name.toTermName)
            result = nonLocalMember(pre, if (name.isTypeName) current.name.toTypeName else current.name)
          else if (selectors.head.name == name.toTermName)
            renamed = true
          else if (selectors.head.name == nme.WILDCARD && !renamed)
            result = nonLocalMember(pre, name)
          if (result == NoSymbol)
            selectors = selectors.tail
        }
        if (settings.warnUnusedImport && selectors.nonEmpty && result != NoSymbol && imp.pos != NoPosition) {
          val m_recordUsage = imp.getClass.getDeclaredMethods().find(_.getName == "recordUsage").get
          m_recordUsage.setAccessible(true)
          m_recordUsage.invoke(imp, current, result)
        }
        if (definitions isImportable result) result
        else NoSymbol
      }
      // def isAccessible(cx: Context, sym: Symbol) = if (canDefineMann(cx.owner)) cx.isAccessible(sym, cx.prefix, superAccess = false) else false
      def isAccessible(cx: Context, sym: Symbol) = true // TODO: sorry, it's 2am, and I can't figure this out
      def member(tpe: Type, name: Name) = if (canDefineMann(tpe.typeSymbol)) tpe.member(name) else NoSymbol
      def nonLocalMember(tpe: Type, name: Name) = if (canDefineMann(tpe.typeSymbol)) tpe.nonLocalMember(name) else NoSymbol

      if (tpt.hasSymbolField && tpt.symbol != NoSymbol) tpt.symbol
      else tpt match {
        case Ident(name) =>

          // STEP 1: RESOLVE THE NAME IN SCOPE
          var defSym: Symbol = NoSymbol
          var defEntry: ScopeEntry = null
          var cx = context
          while (defSym == NoSymbol && cx != NoContext && (cx.scope ne null)) {
            defEntry = cx.scope.lookupEntry(name)
            if ((defEntry ne null) && qualifies(defEntry.sym)) defSym = defEntry.sym
            else {
              cx = cx.enclClass
              val foundSym = member(cx.prefix, name) filter qualifies
              defSym = foundSym filter (isAccessible(cx, _))
              if (defSym == NoSymbol) cx = cx.outer
            }
          }
          if (defSym == NoSymbol && settings.exposeEmptyPackage) {
            defSym = rootMirror.EmptyPackageClass.info member name
          }

          // STEP 2: RESOLVE THE NAME IN IMPORTS
          val symDepth = if (defEntry eq null) cx.depth
                         else cx.depth - ({
                           if (cx.scope ne null) cx.scope.nestingLevel
                           else 0 // TODO: fix this in toolboxes, not hack around here
                         } - defEntry.owner.nestingLevel)
          var impSym: Symbol = NoSymbol
          var imports = context.imports
          while (!reallyExists(impSym) && !imports.isEmpty && imports.head.depth > symDepth) {
            impSym = importedSymbol(imports.head, name)
            if (!exists(impSym)) imports = imports.tail
          }

          // FIXME: repl hack. somehow imports that come from repl are doubled
          // e.g. after `import $line7.$read.$iw.$iw.foo` you'll have another identical `import $line7.$read.$iw.$iw.foo`
          // this is a crude workaround for the issue
          imports match {
            case fst :: snd :: _ if exists(impSym) && fst == snd => imports = imports.tail
            case _ => // do nothing
          }

          // STEP 3: TRY TO RESOLVE AMBIGUITIES
          if (exists(defSym) && exists(impSym)) {
            if (defSym.isDefinedInPackage &&
                (!currentRun.compiles(defSym) ||
                 context.unit.exists && defSym.sourceFile != context.unit.source.file))
              defSym = NoSymbol
            else if (impSym.isError || impSym.name == nme.CONSTRUCTOR)
              impSym = NoSymbol
          }
          if (!exists(defSym) && exists(impSym)) {
            var impSym1: Symbol = NoSymbol
            var imports1 = imports.tail
            while (!imports1.isEmpty &&
                   (!imports.head.isExplicitImport(name) ||
                    imports1.head.depth == imports.head.depth)) {
              impSym1 = importedSymbol(imports1.head, name)
              if (reallyExists(impSym1)) {
                if (imports1.head.isExplicitImport(name)) {
                  if (imports.head.isExplicitImport(name) ||
                      imports1.head.depth != imports.head.depth) return NoSymbol // was possibly fixable ambiguous import
                  impSym = impSym1
                  imports = imports1
                } else if (!imports.head.isExplicitImport(name) &&
                           imports1.head.depth == imports.head.depth) return NoSymbol // was possibly fixable ambiguous import
              }
              imports1 = imports1.tail
            }
          }

          // STEP 4: DEAL WITH WHAT WE HAVE
          if (exists(defSym) && !exists(impSym)) defSym
          else if (exists(defSym) && exists(impSym)) NoSymbol // was ambiguous import
          else if (!exists(defSym) && exists(impSym)) impSym
          else {
            val lastTry = rootMirror.missingHook(rootMirror.RootClass, name)
            if (lastTry != NoSymbol && isAccessible(context, lastTry)) lastTry
            else NoSymbol
          }
        case Select(qualtree, name) => // TODO: be more precise wrt typedSelect
          val qual = probeMacroAnnotation(context, qualtree)
          val sym = if (canDefineMann(qual)) member(qual.tpe, name) else NoSymbol
          if (reallyExists(sym) && isAccessible(context, sym)) sym else NoSymbol
        case AppliedTypeTree(tpt, _) => // https://github.com/scalamacros/paradise/issues/2: expand manns with type parameters
          probeMacroAnnotation(context, tpt)
        case _ =>
          NoSymbol
      }
    }

    // see https://github.com/scalamacros/paradise/issues/7
    // also see https://github.com/scalamacros/paradise/issues/64
    def patchedCompanionSymbolOf(original: Symbol, ctx: Context): Symbol = if (original == NoSymbol) NoSymbol else {
      val owner = original.owner
      // SI-7264 Force the info of owners from previous compilation runs.
      //         Doing this generally would trigger cycles; that's what we also
      //         use the lower-level scan through the current Context as a fall back.
      if (!currentRun.compiles(owner) &&
          // NOTE: the following three lines of code are added to work around #7
          !owner.enclosingTopLevelClass.isRefinementClass &&
          !owner.ownerChain.exists(_.isLocalDummy) &&
          owner.ownerChain.forall(!currentRun.compiles(_))) {
        owner.initialize
      }
      original.companionSymbol orElse {
        implicit class PatchedContext(ctx: Context) {
          trait PatchedLookupResult { def suchThat(criterion: Symbol => Boolean): Symbol }
          def patchedLookup(name: Name, expectedOwner: Symbol) = new PatchedLookupResult {
            override def suchThat(criterion: Symbol => Boolean): Symbol = {
              var res: Symbol = NoSymbol
              var ctx = PatchedContext.this.ctx
              while (res == NoSymbol && ctx.outer != ctx) {
                // NOTE: original implementation says `val s = ctx.scope lookup name`
                // but we can't use it, because Scope.lookup returns wrong results when the lookup is ambiguous
                // and that triggers https://github.com/scalamacros/paradise/issues/64
                val s = {
                  val lookupResult = ctx.scope.lookupAll(name).filter(criterion).toList
                  lookupResult match {
                    case Nil => NoSymbol
                    case List(unique) => unique
                    case _ => abort(s"unexpected multiple results for a companion symbol lookup for $original#{$original.id}")
                  }
                }
                if (s != NoSymbol && s.owner == expectedOwner)
                  res = s
                else
                  ctx = ctx.outer
              }
              res
            }
          }
        }
        ctx.patchedLookup(original.name.companionName, owner).suchThat(sym =>
          (original.isTerm || sym.hasModuleFlag) &&
          (sym isCoDefinedWith original)
        )
      }
    }

    import scala.tools.nsc.interpreter._

    private def obtainField(cls: Class[_], name: String) = { val result = cls.getDeclaredField(name); result.setAccessible(true); result }
    private lazy val f_intp = obtainField(classOf[ReplReporter], "intp")
    private lazy val f_executingRequest = obtainField(classOf[IMain], "executingRequest")
    private lazy val f_handlers = obtainField(classOf[IMain#Request], "handlers")
    private lazy val f_referencedNames = obtainField(classOf[IMain#Request], "referencedNames")

    // https://github.com/scalamacros/paradise/issues/19
    // REPL computes the list of defined members based on parsed code, not typechecked code
    // therefore we need to update its internal structures if that list changes
    // there's no API for that, but luckily it ended up being possible
    def tellReplAboutExpansion(sym: Symbol, companion: Symbol, expanded: List[Tree]): Unit = {
      if (global.reporter.isInstanceOf[ReplReporter] && sym.owner.name.toString == nme.INTERPRETER_IMPORT_WRAPPER.toString) {
        val intp = f_intp.get(global.reporter).asInstanceOf[IMain]
        val req = f_executingRequest.get(intp).asInstanceOf[intp.Request]
        import intp._
        import memberHandlers._
        val handlers1 = req.handlers.flatMap {
          // TODO: I challenge you to write this without a cast :)
          case dh: MemberDefHandler if dh.member.name == sym.name => expanded map (memberHandlers chooseHandler _.asInstanceOf[intp.global.Tree])
          case dh: MemberDefHandler if dh.member.name == companion.name => Nil
          case h => List(h)
        }
        val referencedNames1 = handlers1 flatMap (_.referencedNames)
        f_handlers.set(req, handlers1)
        f_referencedNames.set(req, referencedNames1)
      }
    }

    // MS: End of macro paradise
  }

  abstract class TypeCompleter extends LazyType {
    val tree: Tree
  }

  def mkTypeCompleter(t: Tree)(c: Symbol => Unit) = new LockingTypeCompleter with FlagAgnosticCompleter {
    val tree = t
    def completeImpl(sym: Symbol) = c(sym)
  }

  trait LockingTypeCompleter extends TypeCompleter {
    def completeImpl(sym: Symbol): Unit

    override def complete(sym: Symbol) = {
      _lockedCount += 1
      try completeImpl(sym)
      finally _lockedCount -= 1
    }
  }

  /**
   * A class representing a lazy type with known type parameters. `ctx` is the namer context in which the
   * `owner` is defined.
   *
   * Constructing a PolyTypeCompleter for a DefDef creates type skolems for the type parameters and
   * assigns them to the `tparams` trees.
   */
  class PolyTypeCompleter(tparams: List[TypeDef], restp: TypeCompleter, ctx: Context) extends LockingTypeCompleter with FlagAgnosticCompleter {
    // @M. If `owner` is an abstract type member, `typeParams` are all NoSymbol (see comment in `completerOf`),
    // otherwise, the non-skolemized (external) type parameter symbols
    override val typeParams = tparams map (_.symbol)

    /* The definition tree (poly ClassDef, poly DefDef or HK TypeDef) */
    override val tree = restp.tree

    private val defnSym = tree.symbol

    if (defnSym.isTerm) {
      // for polymorphic DefDefs, create type skolems and assign them to the tparam trees.
      val skolems = deriveFreshSkolems(tparams map (_.symbol))
      map2(tparams, skolems)(_ setSymbol _)
    }

    def completeImpl(sym: Symbol) = {
      // @M an abstract type's type parameters are entered.
      // TODO: change to isTypeMember ?
      if (defnSym.isAbstractType)
        newNamer(ctx.makeNewScope(tree, tree.symbol)) enterSyms tparams //@M
      restp complete sym
    }
  }

  // Can we relax these restrictions? For motivation, see
  //    test/files/pos/depmet_implicit_oopsla_session_2.scala
  //    neg/depmet_try_implicit.scala
  //
  // We should allow forward references since type selections on
  // implicit args are like type parameters.
  //    def foo[T](a: T, x: w.T2)(implicit w: ComputeT2[T])
  // is more compact than:
  //    def foo[T, T2](a: T, x: T2)(implicit w: ComputeT2[T, T2])
  // moreover, the latter is not an encoding of the former, which hides type
  // inference of T2, so you can specify T while T2 is purely computed
  private class DependentTypeChecker(ctx: Context)(namer: Namer) extends TypeTraverser {
    private[this] val okParams = mutable.Set[Symbol]()
    private[this] val method   = ctx.owner

    def traverse(tp: Type) = tp match {
      case SingleType(_, sym) =>
        if (sym.owner == method && sym.isValueParameter && !okParams(sym))
          namer.NamerErrorGen.IllegalDependentMethTpeError(sym)(ctx)

      case _ => mapOver(tp)
    }
    def check(vparamss: List[List[Symbol]]) {
      for (vps <- vparamss) {
        for (p <- vps)
          this(p.info)
        // can only refer to symbols in earlier parameter sections
        okParams ++= vps
      }
    }
  }

  /** The companion class or companion module of `original`.
   *  Calling .companionModule does not work for classes defined inside methods.
   *
   *  !!! Then why don't we fix companionModule? Does the presence of these
   *  methods imply all the places in the compiler calling sym.companionModule are
   *  bugs waiting to be reported? If not, why not? When exactly do we need to
   *  call this method?
   */
  def companionSymbolOf(original: Symbol, ctx: Context): Symbol = if (original == NoSymbol) NoSymbol else {
    val owner = original.owner
    // SI-7264 Force the info of owners from previous compilation runs.
    //         Doing this generally would trigger cycles; that's what we also
    //         use the lower-level scan through the current Context as a fall back.
    if (!currentRun.compiles(owner)) owner.initialize
    original.companionSymbol orElse {
      ctx.lookup(original.name.companionName, owner).suchThat(sym =>
        (original.isTerm || sym.hasModuleFlag) &&
        (sym isCoDefinedWith original)
      )
    }
  }

  /** A version of `Symbol#linkedClassOfClass` that works with local companions, ala `companionSymbolOf`. */
  final def linkedClassOfClassOf(original: Symbol, ctx: Context): Symbol =
    if (original.isModuleClass)
      companionSymbolOf(original.sourceModule, ctx)
    else
      companionSymbolOf(original, ctx).moduleClass
}
