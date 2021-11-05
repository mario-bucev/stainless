
object AbstractValsOverrideOk {

  abstract class Abs {
    val x: Int
    val y: Int
    def z: Int
  }

  abstract class Sub extends Abs {
    def z: Int = 42
  }
// TODO: aussi tester avec val x = ... dans le body
  case class Ok(x: Int, y: Int) extends Sub
}

