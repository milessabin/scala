package cuckoo

import cats._, data._, implicits._

object CatsDemo {
  def foo(i: Int): Validated[Int, Int] = Validated.valid(i)

  Traverse[List].traverse(List(1, 2, 3))(foo)

  Functor[ValidatedNel[String, ?]]

  Functor[Kleisli[List, Int, ?]]
  Functor[Kleisli[ValidatedNel[String, ?], Int, ?]](Kleisli.kleisliFunctor[ValidatedNel[String, ?], Int])
  Functor[Kleisli[ValidatedNel[String, ?], Int, ?]](Kleisli.kleisliFunctor)
  Functor[Kleisli[ValidatedNel[String, ?], Int, ?]]
}
