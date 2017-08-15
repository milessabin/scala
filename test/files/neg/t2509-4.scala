class A
class B extends A

trait Y {
  def value: String
} 

trait X[-T] { // if I make X invariant, this works
  def y(t: T): Y
}

trait Z[-T] extends X[T]

object XA extends Z[A] {
  def y(a: A) = new Y { def value = a.getClass + ": AValue" }
}

object ZB extends Z[B] {
  def y(b: B) = new Y { def value = b.getClass + ": BValue" }
}

object Test {
  implicit def f[T](t: T)(implicit x: X[T]): Y = x.y(t)
  implicit val za: X[A] = XA
  implicit val xb: Z[B] = ZB

  def main(argv: Array[String]): Unit = {
    val a = new A
    val b = new B
    println("A: " + a.value)
    println("B: " + b.value)
  }
}

