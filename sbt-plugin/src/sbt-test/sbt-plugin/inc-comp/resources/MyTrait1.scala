package somepackage
package nested

trait MyTrait {
  def myMethod(x: Int): String = (??? : String).ensuring(_ == "Hello Incremental Compilation #1!")
  def myMethod(x: String): String = (??? : String).ensuring(_ == "Hello Incremental Compilation #2!")
  def myOverridenMethod(x: String): Int = (??? : Int).ensuring(_ >= 42)
}

trait MyExtendingTrait extends MyTrait {
  override final def myOverridenMethod(x: String): Int = 42
}