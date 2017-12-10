@annotation.inductive
trait Foo[T]

object Foo {
  implicit def fooInt: Foo[Int] = new Foo[Int]{}

  implicit def fooPair[T, U](implicit ft: Foo[T], fu: Foo[U]): Foo[(T, U)] = new Foo[(T, U)]{}

  implicit def fooGen[T](implicit ft: => Foo[(T, T)]): Foo[T] = new Foo[T]{}
}

class Bar

object Test {
  implicitly[Foo[Bar]]
}
