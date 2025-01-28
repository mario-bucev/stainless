/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Unap {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] =
    if (i._1 == 0) None() else Some((i._3, i._2))
}

object Unapply {

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  def bar1: Bool = { (42, False().asInstanceOf[Bool], ()) match {
    case Unap(_, b) if b == True() => b
    case Unap((), b) => b
  }}.ensuring { res => res == True() }

  def bar2: Bool = { (42, False().asInstanceOf[Bool], ()) match {
    case Unap(_, b) if b == True() => b
  }}.ensuring { res => res == True() }
}
