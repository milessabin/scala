class Show[T](val i: Int)
object Show extends Show0 {
  def apply[T](i: Int): Show[T] = new Show[T](i)

  implicit val show0: Show[Int] = Show[Int](0)
}

trait Show0 {
  // currently this generates an ambiguity with showGen ... we need to
  // tweak the specificity rules so that showGen is preferred to show1.
  //implicit def show1[T]: Show[T] = Show[T](1)
}

class Foo[T]
object Foo {
  implicit def showFoo[T](implicit st: Show[T]): Show[Foo[T]] = new Show[Foo[T]](2)
}

class Bar[T]
object Bar {
  implicit def barFoo[T]: Bar[Foo[T]] = new Bar[Foo[T]]
  implicit def barOption[T]: Bar[Option[T]] = new Bar[Option[T]]
}

object DerivedShow {
  implicit def showGen[T](implicit bar: Bar[T]): Show[T] = new Show[T](3)
}

object Test extends App {
  def check[T](i: Int)(implicit show: Show[T]): Unit = assert(show.i == i)

  check[Int](0)
  //check[String](1)
  check[Foo[Int]](2)
  //check[Option[Int]](1)

  {
    import DerivedShow._
    check[Int](0)
    //check[String](1)
    check[Foo[Int]](3) // Would like 2
    check[Option[Int]](3)
  }

  {
    import implicit DerivedShow._
    check[Int](0)
    //check[String](1)
    check[Foo[Int]](2)
    check[Option[Int]](3) // Would like 3
  }
}
