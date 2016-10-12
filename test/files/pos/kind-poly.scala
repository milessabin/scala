object Test {
  trait Foo[T] { type Out ; def id(t: Out): Out = t }

  object Foo {
    implicit def foo0[T] = new Foo[T] { type Out = T }
    implicit def foo1[T[_]] = new Foo[T] { type Out = T[Any] }
  }

  def foo[T](implicit f: Foo[T]): f.type = f
  foo[Int].id(23)
  foo[List].id(List[Any](1, 2, 3))
}
