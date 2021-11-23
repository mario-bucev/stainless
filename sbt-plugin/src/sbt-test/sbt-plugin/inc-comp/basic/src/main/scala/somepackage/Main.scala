package somepackage

import stainless._
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Main {
  def head[A](l: List[A]): A = {
    require(l.size > 0)
    l match {
      case Cons(h, _) => h
    }
  }
}
