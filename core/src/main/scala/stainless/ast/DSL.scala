package stainless
package ast

trait DSL extends inox.ast.DSL {
  protected val trees: Trees
  import trees.*

}
