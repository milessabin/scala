package scala
package reflect
package internal

trait StdAttachments {
  self: SymbolTable =>

  /**
   * Common code between reflect-internal Symbol and Tree related to Attachments.
   */
  trait Attachable {
    protected var rawatt: scala.reflect.macros.Attachments { type Pos = Position } = NoPosition
    def attachments = rawatt
    def setAttachments(attachments: scala.reflect.macros.Attachments { type Pos = Position }): this.type = { rawatt = attachments; this }
    def updateAttachment[T: ClassTag](attachment: T): this.type = { rawatt = rawatt.update(attachment); this }
    def removeAttachment[T: ClassTag]: this.type = { rawatt = rawatt.remove[T]; this }
    def hasAttachment[T: ClassTag]: Boolean = rawatt.contains[T]

    // cannot be final due to SynchronizedSymbols
    def pos: Position = rawatt.pos
    def pos_=(pos: Position): Unit = rawatt = (rawatt withPos pos)
    def setPos(newpos: Position): this.type = { pos = newpos; this }
  }

  /** Attachment that knows how to import itself into another universe. */
  trait ImportableAttachment {
    def importAttachment(importer: Importer): this.type
  }

  /** Attachment that doesn't contain any reflection artifacts and can be imported as-is. */
  trait PlainAttachment extends ImportableAttachment {
    def importAttachment(importer: Importer): this.type = this
  }

  /** Stores the trees that give rise to a refined type to be used in reification.
   *  Unfortunately typed `CompoundTypeTree` is lacking essential info, and the reifier cannot use `CompoundTypeTree.tpe`.
   *  Therefore we need this hack (see `Reshape.toPreTyperTypeTree` for a detailed explanation).
   */
  case class CompoundTypeTreeOriginalAttachment(parents: List[Tree], stats: List[Tree])

  /** Attached to a Function node during type checking when the expected type is a SAM type (and not a built-in FunctionN).
    *
    * Ideally, we'd move to Dotty's Closure AST, which tracks the environment,
    * the lifted method that has the implementation, and the target type.
    * For backwards compatibility, an attachment is the best we can do right now.
    *
    * @param samTp the expected type that triggered sam conversion (may be a subtype of the type corresponding to sam's owner)
    * @param sam the single abstract method implemented by the Function we're attaching this to
    *
    * @since 2.12.0-M4
    */
  case class SAMFunction(samTp: Type, sam: Symbol) extends PlainAttachment

  case object DelambdafyTarget extends PlainAttachment

  /** When present, indicates that the host `Ident` has been created from a backquoted identifier.
   */
  case object BackquotedIdentifierAttachment extends PlainAttachment

  /** Identifies trees are either result or intermediate value of for loop desugaring.
   */
  case object ForAttachment extends PlainAttachment

  /** Identifies unit constants which were inserted by the compiler (e.g. gen.mkBlock)
   */
  case object SyntheticUnitAttachment extends PlainAttachment

  /** Untyped list of subpatterns attached to selector dummy. */
  case class SubpatternsAttachment(patterns: List[Tree])

  abstract class InlineAnnotatedAttachment
  case object NoInlineCallsiteAttachment extends InlineAnnotatedAttachment
  case object InlineCallsiteAttachment extends InlineAnnotatedAttachment

  /** Attached to a local class that has its outer field elided. A `null` constant may be passed
    * in place of the outer parameter, can help callers to avoid capturing the outer instance.
    */
  case object OuterArgCanBeElided extends PlainAttachment

  case object UseInvokeSpecial extends PlainAttachment

  // MS: macro paradise

  import scala.collection.{immutable, mutable}

  case object WeakSymbolAttachment
  def markWeak(sym: Symbol) = if (sym != null && sym != NoSymbol) sym.updateAttachment(WeakSymbolAttachment) else sym
  def unmarkWeak(sym: Symbol) = if (sym != null && sym != NoSymbol) sym.removeAttachment[WeakSymbolAttachment.type] else sym
  def isWeak(sym: Symbol) = sym == null || sym == NoSymbol || sym.attachments.get[WeakSymbolAttachment.type].isDefined

  case class SymbolCompleterAttachment(info: Type)
  def backupCompleter(sym: Symbol): Symbol = {
    if (sym != null && sym != NoSymbol) {
      assert(sym.rawInfo.isInstanceOf[LazyType], s"${sym.accurateKindString} ${sym.rawname}#${sym.id} with ${sym.rawInfo.kind}")
      sym.updateAttachment(SymbolCompleterAttachment(sym.rawInfo))
    } else sym
  }
  def restoreCompleter(sym: Symbol): Unit = {
    if (sym != null && sym != NoSymbol) {
      val oldCompleter = sym.attachments.get[SymbolCompleterAttachment].get.info
      sym setInfo oldCompleter
      sym.attachments.remove[SymbolCompleterAttachment]
    } else ()
  }

  // here we should really store and retrieve duplicates of trees in order to avoid leakage through tree attributes
  case class SymbolSourceAttachment(source: Tree)
  def attachSource(sym: Symbol, tree: Tree): Symbol = if (sym != null && sym != NoSymbol) sym.updateAttachment(SymbolSourceAttachment(duplicateAndKeepPositions(tree))) else sym
  def attachedSource(sym: Symbol): Tree = if (sym != null && sym != NoSymbol) sym.attachments.get[SymbolSourceAttachment].map(att => duplicateAndKeepPositions(att.source)).getOrElse(EmptyTree) else EmptyTree

  // unfortunately we cannot duplicate here, because that would dissociate the symbol from its derived symbols
  // that's because attachExpansion(tree) happens prior to enterSym(tree), so if we duplicate the assigned symbol never makes it into the att
  // in its turn, that would mean that we won't be able to handle recursive expansions in typedTemplate
  // because by the time typedTemplate gets activated, everything's already expanded by templateSig
  // so we need to go from original trees/symbols to recursively expanded ones and that requires links to derived symbols
  // TODO: should be a better solution
  case class SymbolExpansionAttachment(expansion: List[Tree])
  def hasAttachedExpansion(sym: Symbol) = sym.attachments.get[SymbolExpansionAttachment].isDefined
  def attachExpansion(sym: Symbol, trees: List[Tree]): Symbol = if (sym != null && sym != NoSymbol) sym.updateAttachment(SymbolExpansionAttachment(trees/*.map(tree => duplicateAndKeepPositions(tree))*/)) else sym
  def attachedExpansion(sym: Symbol): Option[List[Tree]] = if (sym != null && sym != NoSymbol) sym.attachments.get[SymbolExpansionAttachment].map(_.expansion/*.map(tree => duplicateAndKeepPositions(tree))*/) else None

  import SymbolExpansionStatus._
  private def checkExpansionStatus(sym: Symbol, p: SymbolExpansionStatus => Boolean) = sym.attachments.get[SymbolExpansionStatus].map(p).getOrElse(false)
  def isMaybeExpandee(sym: Symbol): Boolean = checkExpansionStatus(sym, _.isUnknown)
  def isExpanded(sym: Symbol): Boolean = checkExpansionStatus(sym, _.isExpanded)
  def isNotExpandable(sym: Symbol): Boolean = checkExpansionStatus(sym, _.isNotExpandable)
  def markMaybeExpandee(sym: Symbol): Symbol = if (sym != null && sym != NoSymbol) sym.updateAttachment(Unknown) else sym
  def markExpanded(sym: Symbol): Symbol = if (sym != null && sym != NoSymbol) sym.updateAttachment(Expanded) else sym
  def markNotExpandable(sym: Symbol): Symbol = if (sym != null && sym != NoSymbol) sym.updateAttachment(NotExpandable) else sym
  def unmarkExpanded(sym: Symbol): Symbol = if (sym != null && sym != NoSymbol) sym.removeAttachment[SymbolExpansionStatus] else sym

  case class CacheAttachment(cache: mutable.Map[String, Any])
  implicit class RichTree(tree: Tree) {
    def cached[T](key: String, op: => T): T = {
      val cache = tree.attachments.get[CacheAttachment].map(_.cache).getOrElse(mutable.Map[String, Any]())
      val result = cache.getOrElseUpdate(key, op).asInstanceOf[T]
      tree.updateAttachment(CacheAttachment(cache))
      result
    }
  }
}

class SymbolExpansionStatus private (val value: Int) extends AnyVal {
  def isUnknown = this == SymbolExpansionStatus.Unknown
  def isExpanded = this == SymbolExpansionStatus.Expanded
  def isNotExpandable = this == SymbolExpansionStatus.NotExpandable
}
object SymbolExpansionStatus {
  val Unknown = new SymbolExpansionStatus(0)
  val Expanded = new SymbolExpansionStatus(1)
  val NotExpandable = new SymbolExpansionStatus(2)
}
