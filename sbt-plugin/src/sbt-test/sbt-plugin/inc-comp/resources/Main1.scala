package somepackage

import stainless._
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Main {
  import nested._

  def head[A](l: List[A]): A = {
    require(l.size > 0)
    l match {
      case Cons(h, _) => h
    }
  }

  def tail[A](l: List[A]): List[A] = {
    require(l.size > 0)
    l match {
      case Cons(_, t) => t
    }
  }

  def something(mt: MyTrait): String = mt.myMethod(123).ensuring(_ == "Hello Incremental Compilation #1!")

  def somethingElse(mt: MyTrait): String = mt.myMethod("abc").ensuring(_ == "Hello Incremental Compilation #2!")

  def test1(mt: MyTrait): Int = mt.myOverridenMethod("xyz").ensuring(_ >= 42)

  def test2(mt: MyExtendingTrait): Int = mt.myOverridenMethod("hjk").ensuring(_ >= 42)
}
