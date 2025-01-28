object AssertFalse {

  // The assert(false) used to not have an attached position
  def test1(x: BigInt) = { // return type is Nothing
    val y = x + x
    assert(x - x == 0)
    val z = y + x
    assert(z == 3 * x)
    assert(false)
  }

  // This used to scramble the summary report as follows:
  // [  Info  ] ║ PositionsTest.scala:21:5:    test2  body assertion: Expression of type Nothing: assert(x - x == 0)
  // [  Info  ] val z: BigInt = y + x
  // [  Info  ] assert(z == 3 * x)
  // [  Info  ] assert(false)
  // [  Info  ] <empty tree>[{ x: Object | @dropConjunct false }]  invalid           U:smt-z3  0,0 ║
  // The difference from test1 is the Unit type annotation of the function
  def test2(x: BigInt): Unit = {
    val y = x + x
    assert(x - x == 0)
    val z = y + x
    assert(z == 3 * x)
    assert(false) // Sadly this is positioned at line 21 due to how NoTree and let bindings positions are handled
  }

  // The assert(false) used to not have an attached position
  // The difference with test2 is the explicit () return
  def test3(x: BigInt): Unit = {
    val y = x + x
    assert(x - x == 0)
    val z = y + x
    assert(z == 3 * x)
    assert(false)
    ()
  }

  def test4(x: BigInt): Int = { // Ok since assert(false) : Nothing
    val y = x + x
    assert(x - x == 0)
    val z = y + x
    assert(z == 3 * x)
    assert(false) // Sadly this is positioned at line 40 due to how NoTree and let bindings positions are handled
  }
}