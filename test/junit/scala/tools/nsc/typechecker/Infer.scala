package scala.tools.nsc
package typechecker

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.testing.BytecodeTesting

class A
class B extends A

trait C

trait X[+T]
trait Y[T]
trait Z[-T]
trait Quux[-T] extends Z[T]

trait SubZB extends Z[B]
trait ZwC[-T] extends Z[T] with C

@RunWith(classOf[JUnit4])
class InferencerTests extends BytecodeTesting {
  import compiler.global._, definitions._, analyzer._

  @Test
  def isAsSpecificDotty(): Unit = {
    settings.YdottySpecificity.value = true

    val run = new global.Run

    enteringPhase(run.typerPhase) {
      val XA = typeOf[X[A]]
      val XB = typeOf[X[B]]

      val YA = typeOf[Y[A]]
      val YB = typeOf[Y[B]]

      val ZA = typeOf[Z[A]]
      val ZB = typeOf[Z[B]]

      val LZA = typeOf[List[Z[A]]]
      val LZB = typeOf[List[Z[B]]]

      val QuuxA = typeOf[Quux[A]]
      val QuuxB = typeOf[Quux[B]]

      val SubZB = typeOf[SubZB]
      val ZBwC = typeOf[ZwC[B]]

      // https://github.com/scala/bug/issues/2509
      // See discussion at https://github.com/lampepfl/dotty/blob/89540268e6c49fb92b9ca61249e46bb59981bf5a/src/dotty/tools/dotc/typer/Applications.scala#L925-L951

      // Covariant
      assert(!typer.infer.isAsSpecific(XA, XB))
      assert(typer.infer.isAsSpecific(XB, XA))

      // Invariant
      assert(!typer.infer.isAsSpecific(YA, YB))
      assert(!typer.infer.isAsSpecific(YB, YA))

      // Contravariant: treat top level as covariant
      assert(!typer.infer.isAsSpecific(ZA, ZB))
      assert(typer.infer.isAsSpecific(ZB, ZA))

      // Inner contravariant: unchanged
      assert(typer.infer.isAsSpecific(LZA, LZB))
      assert(!typer.infer.isAsSpecific(LZB, LZA))

      // Subtypes of contravaraint effectively unrelated
      assert(!typer.infer.isAsSpecific(ZA, SubZB))
      assert(typer.infer.isAsSpecific(SubZB, ZA))

      // Subtypes of contravaraint effectively unrelated
      assert(!typer.infer.isAsSpecific(ZA, ZBwC))
      assert(typer.infer.isAsSpecific(ZBwC, ZA))

      // Contravariant outer subtypes
      assert(!typer.infer.isAsSpecific(ZA, QuuxA))
      assert(typer.infer.isAsSpecific(QuuxA, ZA))

      assert(!typer.infer.isAsSpecific(ZA, QuuxB))
      assert(typer.infer.isAsSpecific(QuuxB, ZA))

      assert(!typer.infer.isAsSpecific(ZB, QuuxA))
      assert(!typer.infer.isAsSpecific(QuuxA, ZB))

      assert(!typer.infer.isAsSpecific(ZB, QuuxB))
      assert(typer.infer.isAsSpecific(QuuxB, ZB))
    }
  }

  @Test
  def isAsSpecificScalac(): Unit = {
    settings.YdottySpecificity.value = false

    val run = new global.Run

    enteringPhase(run.typerPhase) {
      val XA = typeOf[X[A]]
      val XB = typeOf[X[B]]

      val YA = typeOf[Y[A]]
      val YB = typeOf[Y[B]]

      val ZA = typeOf[Z[A]]
      val ZB = typeOf[Z[B]]

      val LZA = typeOf[List[Z[A]]]
      val LZB = typeOf[List[Z[B]]]

      val QuuxA = typeOf[Quux[A]]
      val QuuxB = typeOf[Quux[B]]

      val SubZB = typeOf[SubZB]
      val ZBwC = typeOf[ZwC[B]]

      // Covariant
      assert(!typer.infer.isAsSpecific(XA, XB))
      assert(typer.infer.isAsSpecific(XB, XA))

      // Invariant
      assert(!typer.infer.isAsSpecific(YA, YB))
      assert(!typer.infer.isAsSpecific(YB, YA))

      // Contravariant
      assert(typer.infer.isAsSpecific(ZA, ZB))
      assert(!typer.infer.isAsSpecific(ZB, ZA))

      // Inner contravariant
      assert(typer.infer.isAsSpecific(LZA, LZB))
      assert(!typer.infer.isAsSpecific(LZB, LZA))

      // Subtypes of contravaraint effectively unrelated
      assert(!typer.infer.isAsSpecific(ZA, SubZB))
      assert(!typer.infer.isAsSpecific(SubZB, ZA))

      // Subtypes of contravaraint effectively unrelated
      assert(!typer.infer.isAsSpecific(ZA, ZBwC))
      assert(!typer.infer.isAsSpecific(ZBwC, ZA))

      // Contravariant outer subtypes
      assert(!typer.infer.isAsSpecific(ZA, QuuxA))
      assert(typer.infer.isAsSpecific(QuuxA, ZA))

      assert(!typer.infer.isAsSpecific(ZA, QuuxB))
      assert(!typer.infer.isAsSpecific(QuuxB, ZA))

      assert(!typer.infer.isAsSpecific(ZB, QuuxA))
      assert(typer.infer.isAsSpecific(QuuxA, ZB))

      assert(!typer.infer.isAsSpecific(ZB, QuuxB))
      assert(typer.infer.isAsSpecific(QuuxB, ZB))
    }
  }
}
