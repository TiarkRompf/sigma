package analysis

import SimpleFrontend._

class TestAnalysis5 extends RunAndCheckSuite {

  val prefix = "test-out/test-analysis-5"

  // test arrays / computed index access
  //   first, some unit tests
  testProg("A1") {
      Block(List(
        Assign("x", Const(0)), // "input"
        Assign("a", New("A")),
        Put(Ref("a"), Const("field"), Times(Ref("x"),Const(2))),
        Assign("r", Ref("a"))
      ))
    }{
      """{
        "&x" -> {"val" -> 0},
        "A"  -> {top -> {"field" -> 0}},
        "&a" -> {"val" -> (A,top)},
        "&r" -> {"val" -> (A,top)}}"""
    }

  testProg("A2") {
      Block(List(
        Assign("x", Const(0)), // "input"
        Assign("a", New("A")),
        Put(Ref("a"), Ref("x"), Times(Ref("x"),Const(2))),
        Assign("r", Ref("a"))
      ))
    }{
      """{
        "&x" -> {"val" -> 0},
        "A"  -> {top -> {0 -> 0}},
        "&a" -> {"val" -> (A,top)},
        "&r" -> {"val" -> (A,top)}}"""
    }

  testProg("A3") {
      Block(List(
        Assign("x", Const(0)),
        Assign("a", New("A")),
        Put(Ref("a"), Const("field"), Const(7)),
        While(Less(Ref("x"),Const(100)), Block(List(
          Put(Ref("a"), Const("field"), Const(7)),
          Assign("x", Plus(Ref("x"), Const(1)))
        ))),
        Assign("r", Ref("a"))
      ))
    }{
      """{
        "&x" -> {"val" -> 100},
        "A"  -> {top -> {"field" -> 7}},
        "&a" -> {"val" -> (A,top)},
        "&r" -> {"val" -> (A,top)}}"""
    }

  //   update array at loop index
  testProg("A4") {
      Block(List(
        Assign("x", Const(0)),
        Assign("y", Const(10)),
        Assign("a", New("A")),
        While(Less(Ref("x"),Const(100)), Block(List(
          Put(Ref("a"), Ref("x"), Times(Ref("x"),Const(2))),
          Assign("x", Plus(Ref("x"), Const(1))),
          Assign("y", Plus(Ref("y"), Const(1)))
        ))),
        Assign("r", Ref("a"))
      ))
    }{
      """
      {
        "&a" -> {"val" -> (A,top)},
        "A"  -> {"top" -> collect(100) { x9_A_top_x10 => (x9_A_top_x10 * 2) }},
        "&x" -> {"val" -> 100},
        "&y" -> {"val" -> 110},
        "&r" -> {"val" -> (A,top)}
      }
      """
    }

}
