package stainless.frontends.dotc

import dotty.tools.dotc.ast.tpd

object common {
  case class ClassDefs(defs: List[tpd.TypeDef] = Nil)
}
