package test

class X1
class X2
class X3

trait One[A]
trait Two[A, B]

class Foo extends Two[X1, X2] with One[X3]
object Test {
  def test1[M[_], A](x: M[A]): M[A] = x
  def test2[M[X] <: One[X], A](x: M[A]): M[A] = x

  val foo = new Foo

  test1(foo): One[X3]     // fails with -Yhigher-order-unification enabled
  test1(foo): Two[X1, X2] // fails without -Yhigher-order-unification

  test2(foo): One[X3]     // passes in both cases
  test2(foo): Two[X1, X2] // fails in both cases
}
