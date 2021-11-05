import stainless.annotation._

object GoodInitialization {
  case class AAA(xxx: BigInt) {
    val yyy = xxx
    val zzz = yyy + yyy
  }
  def f(z: BigInt) = {
    assert(AAA(21).zzz == 42)
  }
}
