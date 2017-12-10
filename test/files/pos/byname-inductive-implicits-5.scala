object ListInstances {
  type LRepr[T] = Either[::[T], Either[Nil.type, Unit]]
  type CRepr[T] = (T, (List[T], Unit))
  type NRepr = Unit

  implicit def genList[T, F[_]](implicit fr0: => F[LRepr[T]]): Generic.Aux[List[T], F, LRepr[T]] = new Generic[List[T], F] {
    type Repr = LRepr[T]
    val fr: F[LRepr[T]] = fr0
  }

  implicit def isoList[T]: Iso[List[T], LRepr[T]] = new Iso[List[T], LRepr[T]] {
    def to(t: List[T]): LRepr[T] = t match {
      case hd :: tl => Left(::(hd, tl))
      case n@Nil => Right(Left(n))
    }
    def from(r: LRepr[T]): List[T] = r match {
      case Left(c) => c
      case Right(Left(n)) => n
    }
  }

  implicit def genCons[T, F[_]](implicit fr0: => F[CRepr[T]]): Generic.Aux[::[T], F, CRepr[T]] = new Generic[::[T], F] {
    type Repr = CRepr[T]
    val fr: F[CRepr[T]] = fr0
  }

  implicit def isoCons[T]: Iso[::[T], CRepr[T]] = new Iso[::[T], CRepr[T]] {
    def to(t: ::[T]): CRepr[T] = (t.head, (t.tail, ()))
    def from(r: CRepr[T]): ::[T] = ::(r._1, r._2._1)
  }

  implicit def genNil[F[_]](implicit fr0: => F[NRepr]): Generic.Aux[Nil.type, F, NRepr] = new Generic[Nil.type, F] {
    type Repr = NRepr
    val fr: F[Repr] = fr0
  }

  implicit val isoNil: Iso[Nil.type, NRepr] = new Iso[Nil.type, NRepr] {
    def to(t: Nil.type): NRepr = ()
    def from(r: NRepr): Nil.type = Nil
  }
}

import ListInstances._

trait Generic[T, F[_]] {
  type Repr
  val fr: F[Repr]
}

object Generic {
  type Aux[T, F[_], Repr0] = Generic[T, F] { type Repr = Repr0 }

  def apply[T, F[_]](implicit gen: Generic[T, F]): Generic.Aux[T, F, gen.Repr] = gen
}

trait Iso[A, B] {
  def to(t: A): B
  def from(t: B): A
}

case class IsoAnd[T, F[_], Repr](iso: Iso[T, Repr], fr: F[Repr])

object IsoAnd {
  implicit def mkIsoAnd[T, F[_], Repr](implicit iso: Iso[T, Repr], fr: F[Repr]): IsoAnd[T, F, Repr] =
    IsoAnd[T, F, Repr](iso, fr)
}

@annotation.inductive
trait Eq[T] {
  def eqv(x: T, y: T): Boolean
}

object syntax {
  implicit class EqSyntax[T](val x: T)(implicit eqt: Eq[T]) {
    def ===(y: T): Boolean = eqt.eqv(x, y)
  }
}

import syntax._

object Eq {
  def apply[T](implicit eqt: Eq[T]): Eq[T] = eqt

  implicit val eqUnit: Eq[Unit] = new Eq[Unit] {
    def eqv(x: Unit, y: Unit): Boolean = x == y
  }

  implicit val eqBoolean: Eq[Boolean] = new Eq[Boolean] {
    def eqv(x: Boolean, y: Boolean): Boolean = x == y
  }

  implicit val eqInt: Eq[Int] = new Eq[Int] {
    def eqv(x: Int, y: Int): Boolean = x == y
  }

  implicit val eqString: Eq[String] = new Eq[String] {
    def eqv(x: String, y: String): Boolean = x == y
  }

  implicit def eqPair[T, U](implicit eqt: Eq[T], equ: Eq[U]): Eq[(T, U)] = new Eq[(T, U)] {
    def eqv(x: (T, U), y: (T, U)): Boolean = eqt.eqv(x._1, y._1) && equ.eqv(x._2, y._2)
  }

  implicit def eqEither[T, U](implicit eqt: Eq[T], equ: Eq[U]): Eq[Either[T, U]] = new Eq[Either[T, U]] {
    def eqv(x: Either[T, U], y: Either[T, U]): Boolean = (x, y) match {
      case (Left(x), Left(y)) => eqt.eqv(x, y)
      case (Right(x), Right(y)) => equ.eqv(x, y)
      case _ => false
    }
  }
}

object DerivedEq {
  implicit def genEq[T](implicit gen: Generic[T, ({ type λ[r] = IsoAnd[T, Eq, r] })#λ]): Eq[T] =
    new Eq[T] {
      import gen.fr._, iso._
      def eqv(x: T, y: T): Boolean = fr.eqv(to(x), to(y))
    }
}

import DerivedEq._

object Test {
  List(1, 2, 3) === List(1, 2, 3)
}
