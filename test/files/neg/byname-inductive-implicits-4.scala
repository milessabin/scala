@annotation.inductive
trait Foo[T]

object Foo {
  implicit def fooInt: Foo[Int] = new Foo[Int]{}

  implicit def fooPair[T, U](implicit ft: Foo[T], fu: Foo[U]): Foo[(T, U)] = new Foo[(T, U)]{}

  implicit def fooGen[F[_], T](implicit fft: => Foo[F[F[T]]]): Foo[F[T]] = new Foo[F[T]]{}
}

object Test {
  implicitly[Foo[Option[Int]]]
}
