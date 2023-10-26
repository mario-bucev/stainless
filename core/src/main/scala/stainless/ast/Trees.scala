/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

trait Trees
  extends inox.ast.Trees
     with Definitions
     with Expressions
     with Types
     with Constructors
     with Deconstructors
     with TreeOps { self =>

  type Symbol = ast.Symbol
  type SymbolIdentifier = ast.SymbolIdentifier

  val patternOps: inox.ast.GenTreeOps {
    val sourceTrees: self.type
    val targetTrees: self.type
    type Source = Pattern
    type Target = Pattern
  } = {
    class PatternOpsImpl(override val sourceTrees: self.type,
                         override val targetTrees: self.type) extends inox.ast.GenTreeOps {
      type Source = Pattern
      type Target = Pattern
      val Deconstructor = PatternExtractor
    }
    new PatternOpsImpl(self, self)
  }

  override val exprOps: ExprOps { val trees: self.type } = {
    class ExprOpsImpl(override val trees: self.type) extends ExprOps(trees)
    new ExprOpsImpl(self)
  }

  override val dsl: DSL {val trees: self.type} = {
    class DSLImpl(override val trees: self.type) extends DSL
    new DSLImpl(this)
  }

  val printer: Printer { val trees: self.type }
}
