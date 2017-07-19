object Test {
  class Foo {
    class Bar
    object Bar {
      implicit def mkBar: Bar = new Bar
    }
  }

  implicit class Ops[F <: Foo](val f0: F) {
    def op0(implicit b: f0.Bar): f0.Bar = b
    def op1(i: Int)(implicit b: f0.Bar): f0.Bar = b
    def op2(i: Int)(j: Boolean)(implicit b: f0.Bar): f0.Bar = b
    def op3[T](implicit b: f0.Bar): f0.Bar = b
  }

  object f extends Foo

  f.op0
  f.op1(23)
  f.op2(23)(true)
  f.op3[Int]
}
