object Test {
  class Foo {
    class Bar
    object Bar {
      implicit def mkBar: Bar = new Bar
    }
  }

  object f extends Foo

  object ImplicitClass {
    implicit class Ops[F <: Foo](val f0: F) {
      def op0(implicit b: f0.Bar): f0.Bar = b
      def op1(i: Int)(implicit b: f0.Bar): f0.Bar = b
      def op2(i: Int)(j: Boolean)(implicit b: f0.Bar): f0.Bar = b
      def op3[T](implicit b: f0.Bar): f0.Bar = b
      def op4(i: => Int)(implicit b: f0.Bar): f0.Bar = b
    }

    f.op0
    f.op1(23)
    f.op2(23)(true)
    f.op3[Int]
    f.op4(23)
  }

  object LazyImplicitConversion {
    class Ops[F <: Foo](val f0: F) {
      def op0(implicit b: f0.Bar): f0.Bar = b
      def op1(i: Int)(implicit b: f0.Bar): f0.Bar = b
      def op2(i: Int)(j: Boolean)(implicit b: f0.Bar): f0.Bar = b
      def op3[T](implicit b: f0.Bar): f0.Bar = b
      def op4(i: => Int)(implicit b: f0.Bar): f0.Bar = b
    }
    implicit def ops[F <: Foo](f: => F): Ops[F] = new Ops(f)

    f.op0
    f.op1(23)
    f.op2(23)(true)
    f.op3[Int]
    f.op4(23)
  }

  object RightAssociativeOps {
    implicit class Ops[F <: Foo](val f0: F) {
      def op0_:(i: Int)(implicit b: f0.Bar): f0.Bar = b
      def op1_:(i: => Int)(implicit b: f0.Bar): f0.Bar = b
    }

    object f extends Foo

    23 op0_: f
    23 op1_: f
  }
}
