package somepackage
package nested

object FancyComputation {
  def compute(x: String): Int = {
    val y = 1000
    val z = 337
    y + z
  }.ensuring(_ == 1337)
}