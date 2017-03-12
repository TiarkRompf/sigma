package analysis

import Frontend._

class TestAnalysis4 extends RunAndCheckSuite {

  val prefix = "test-out/test-analysis-4"

  // test some integer computations

  testProg("A1") {
      Block(List(
        Assign("i", Const(0)),
        Assign("y", Const(0)),
        Assign("x", Const(8)),
        While(Less(Ref("i"),Const(100)), Block(List(
          Assign("x", Const(7)),
          Assign("x", Plus(Ref("x"), Const(1))),
          Assign("y", Plus(Ref("y"), Const(1))),
          Assign("i", Plus(Ref("i"), Const(1)))
        )))
      ))
    } {
      """Map(
        "&i" -> Map("val" -> 100), 
        "&y" -> Map("val" -> 100), 
        "&x" -> Map("val" -> 8)
      )"""
    }

  testProg("A2") {
      Block(List(
        Assign("x", Const(900)), // input
        Assign("y", Const(0)),
        While(Less(Const(0), Ref("x")), Block(List(
//          If(Less(Ref("y"),Const(17)), 
//            Block(List(
              Assign("y", Plus(Ref("y"), Const(1)))
,//            )),
//            Block(Nil)
//          ),
          Assign("x", Plus(Ref("x"), Const(-1)))
        ))),
        Assign("r", Ref("x"))
      ))
    }{
      """Map(
        "&x"  -> Map("val" -> 0), 
        "&y"  -> Map("val" -> 900), 
        "&r"  -> Map("val" -> 0)
      )"""
    }
/*
      """Map(
        "&x"  -> Map("val" -> 0), 
        "&y"  -> Map("val" -> 17), 
        "&r"  -> Map("val" -> 0)
      )"""
*/

  testProg("A3") {
      Block(List(
        Assign("x", Const(900)), // input
        Assign("z", Const(0)),
        While(Less(Const(0), Ref("x")), Block(List(
          Assign("z", Plus(Ref("z"), Ref("x"))),
          Assign("x", Plus(Ref("x"), Const(-1)))
        ))),
        Assign("r", Ref("x"))
      ))
    }{
      """Map(
        "&x"  -> Map("val" -> 0), 
        "&z"  -> Map("val" -> 405450), 
        "&r"  -> Map("val" -> 0)
      )"""
    }

/* XXX this one doesn't terminate??? --> investigate!

    Main.runAndCheck {
      Block(List(
        Assign("x", Const(900)), // input
        Assign("y", Const(0)),
        Assign("z", Const(0)),
        Assign("z2", Const(0)),
        While(Less(Const(0), Ref("x")), Block(List(
          Assign("z", Plus(Ref("z"), Ref("x"))),
          Assign("z2", Plus(Ref("z2"), Plus(Times(Ref("x"),Const(3)), Const(5)))),
          If(Less(Ref("y"),Const(17)), 
            Block(List(
              Assign("y", Plus(Ref("y"), Const(1)))
            )),
            Block(Nil)
          ),
          Assign("x", Plus(Ref("x"), Const(-1)))
        ))),
        Assign("r", Ref("x"))
      ))
    }{
      """Map(
        "&x"  -> Map("val" -> 0), 
        "&z"  -> Map("val" -> 405450), 
        "&y"  -> Map("val" -> 17), 
        "&r"  -> Map("val" -> 0), 
        "&z2" -> Map("val" -> 1220850)
      )"""
    }
*/
}
