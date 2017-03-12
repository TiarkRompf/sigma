package analysis

import Frontend._

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
      """Map(
        "&x" -> Map("val" -> 0), 
        "A"  -> Map(top -> Map("field" -> 0)),
        "&a" -> Map("val" -> (A,top)), 
        "&r" -> Map("val" -> (A,top)))"""   
    }    

  testProg("A2") {
      Block(List(
        Assign("x", Const(0)), // "input"
        Assign("a", New("A")),
        Put(Ref("a"), Ref("x"), Times(Ref("x"),Const(2))),
        Assign("r", Ref("a"))
      ))
    }{
      """Map(
        "&x" -> Map("val" -> 0), 
        "A"  -> Map(top -> Map(0 -> 0)), 
        "&a" -> Map("val" -> (A,top)), 
        "&r" -> Map("val" -> (A,top)))"""
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
      """Map(
        "&x" -> Map("val" -> 100), 
        "A"  -> Map(top -> Map("field" -> 7)), 
        "&a" -> Map("val" -> (A,top)), 
        "&r" -> Map("val" -> (A,top)))"""
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
      Map(
        "&a" -> Map("val" -> (A,top)), 
        "A"  -> Map("top" -> collect(100) { x9_A_top_x10 => x9_A_top_x10 * 2 }), 
        "&x" -> Map("val" -> 100), 
        "&y" -> Map("val" -> 110), 
        "&r" -> Map("val" -> (A,top))
      )
      """
    }

}
