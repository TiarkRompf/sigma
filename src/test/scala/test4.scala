package analysis

class TestAnalysis4 extends FileDiffSuite {

  val prefix = "test-out/test-analysis-4"

  // test some integer computations

  test("A") { withOutFileChecked(prefix+"A") {
    import Test1._
    Test1.runAndCheck {
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

    Test1.runAndCheck {
      Block(List(
        Assign("x", Const(900)), // input
        Assign("y", Const(0)),
        While(Less(Const(0), Ref("x")), Block(List(
//          If(Less(Ref("y"),Const(17)), 
//            Block(List(
              Assign("y", Plus(Ref("y"), Const(1)))
//            )),
//            Block(Nil)
,//          ),
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


    Test1.runAndCheck {
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

    Test1.runAndCheck {
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
  }}

  // test arrays / computed index access
  //   first, some unit tests
  test("A2") { withOutFileChecked(prefix+"A2") {
    import Test1._
    Test1.runAndCheck {
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
    Test1.runAndCheck {
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
  }}

  test("A3") { withOutFileChecked(prefix+"A3") {
    import Test1._
    Test1.runAndCheck {
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
  }}

  //   update array at loop index
  test("A4") { withOutFileChecked(prefix+"A4") {
    import Test1._
    Test1.runAndCheck {
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

  }}

  // test store logic (1): build a linked list

  test("B") { withOutFileChecked(prefix+"B") {
    import Test1._
    Test1.runAndCheck { // test3
      Block(List(
        Assign("i", Const(0)),
        Assign("z", New("A")),
        Assign("x", Ref("z")),
        While(Less(Ref("i"),Const(100)), Block(List(
          Assign("y", New("B")),
          Put(Ref("y"), Const("head"), Ref("i")),
          Put(Ref("y"), Const("tail"), Ref("x")),
          Assign("x", Ref("y")),
          Assign("i", Plus(Ref("i"), Const(1)))
        )))
      ))
    } {
      """
      Map(
        "&i" -> Map("val" -> 100), 
        "B"  -> Map("top" -> 
          collect(100) { x8_B_top_x9 => 
            Map(
              "head" -> x8_B_top_x9, 
              "tail" -> if (0 < x8_B_top_x9) ("B",("top",x8_B_top_x9 + -1)) 
                        else                 (A,top)
            ) 
          }), 
        "A"  -> Map("top" -> Map()), 
        "&x" -> Map("val" -> (B,(top,99))), 
        "&z" -> Map("val" -> (A,top)), 
        "&y" -> Map("val" -> (B,(top,99)))
      )
      """
    }


  // back to simpler tests (compare to test3)
  // 3 and 4 should be different: alloc within the loop vs before
  
    Test1.runAndCheck { // test4
      Block(List(
        Assign("i", Const(0)),
        Assign("z", New("A")),
        Assign("x", Ref("z")),
        Assign("y", New("B")),
        While(Less(Ref("i"),Const(100)), Block(List(
          Put(Ref("y"), Const("head"), Ref("i")),
          Put(Ref("y"), Const("tail"), Ref("x")),
          Assign("x", Ref("y")),
          Assign("i", Plus(Ref("i"), Const(1)))
        )))
      ))
    }{
      """
      Map(
        "&i" -> Map("val" -> 100), 
        "B"  -> Map("top" -> Map(
                              "head" -> 99, 
                              "tail" -> (B,top))), 
        "A"  -> Map("top" -> Map()), 
        "&x" -> Map("val" -> (B,top)), 
        "&z" -> Map("val" -> (A,top)), 
        "&y" -> Map("val" -> (B,top))
      )
      """
    }

    Test1.runAndCheck { // test5
      Block(List(
        Assign("i", Const(0)),
        Assign("z", New("A")),
        Assign("x", Ref("z")),
        While(Less(Ref("i"),Const(100)), Block(List(
          Put(Ref("x"), Const("head"), Ref("i")),
          Assign("i", Plus(Ref("i"), Const(1)))
        )))
      ))
    } {
      """
      Map(
        "&i" -> Map("val" -> 100), 
        "A"  -> Map("top" -> Map("head" -> 99)), 
        "&z" -> Map("val" -> (A,top)), 
        "&x" -> Map("val" -> (A,top))
      )
      """
    }
  }}



/*
  var i = 0
  var z = new A
  var x = z
  while (i < 100) {
    var y = new B
    y.head = i
    y.tail = x
    x = y
    i = i + 1
  }

  Version 1: Optimistic rewriting, but flat stores. We obtain this code:

  val x7 = { x8 => 
  if (0 < x8) 
    x7(x8 + -1) 
      + ("&y" -> Map("val" -> ("B",(1,x8)))) 
      + (("B",(1,x8)) -> 
          x7(x8 + -1)(("B",(1,x8))) 
          + ("head" -> x7(x8 + -1)("&i")("val"))) 
      + (("B",(1,x8)) -> 
          x7(x8 + -1)(("B",(1,x8))) 
          + ("head" -> x7(x8 + -1)("&i")("val")) 
          + ("tail" -> x7(x8 + -1)("&x")("val"))) 
      + ("&x" -> Map("val" -> ("B",(1,x8)))) 
      + ("&i" -> Map("val" -> x7(x8 + -1)("&i")("val") + 1)) 
  else 
    Map("&i" -> Map("val" -> 0), "&z" -> Map("val" -> (A,1)), "&x" -> Map("val" -> (A,1)), "&y" -> Map("val" -> ("B",(1,x8)))) 
      + (("B",(1,x8)) -> Map("head" -> 0)) 
      + (("B",(1,x8)) -> Map("head" -> 0, "tail" -> (A,1))) 
      + ("&x" -> Map("val" -> ("B",(1,x8)))) 
      + ("&i" -> Map("val" -> 1)) 
  }
  x7(fixindex(x8 => x7(x8 + -1)("&i")("val") < 100))

  The store can't be safely split into a Map because (("B",(1,x8))
  is not a unique value. The idea is to make the store hierarchical: 
  first address with "B", then (1,x8). Essentially this models
  allocations inside loops as arrays, although the representation is
  a little different from objects accessed as first class arrays 
  (see testProg1c). In comparison, we remove a level of indirection (or
  should we try to be completely uniform?). Store lookups will need to 
  become hierarchy aware in general, too. If we do a lookup like store(x99), 
  x99 could be either a tuple, or a flat address.

  Version 2: Preliminary support for nested stores. We obtain:

  val x7_&x_val = { x8 => ("B",(1,x8)) }
  val x7_B = { x8 => 
    if (0 < x8) 
      x7_B(x8 + -1) 
        + ((1,x8) -> 
            x7_B(x8 + -1)((1,x8)) 
            + ("head" -> x8 + -1)) 
        + ((1,x8) -> 
            x7_B(x8 + -1)((1,x8)) 
            + ("head" -> x8 + -1) 
            + ("tail" -> x7_&x_val(x8 + -1)))   <--- why not inlined? (call doesn't see rhs -- still in iteration mode)
    else 
      Map(1 ->
        Map() 
        + (x8 -> 
            "undefined"((1,x8))       <--- accessing "undefined": base case? 
            + ("head" -> x8 + -1)) 
        + (x8 -> 
            "undefined"((1,x8)) 
            + ("head" -> x8 + -1) 
            + ("tail" -> (A,1)))) 
  }
  
  Map(
    "&i" -> Map("val" -> 100), 
    "B" -> x7_B(100), 
    "&x" -> Map("val" -> (B,(1,100))), 
    "&z" -> Map("val" -> (A,1)), 
    "&y" -> Map("val" -> (B,(1,100))))


  Version 3: Tweak it! Speculative loop peeling for tuple addresses 
  removes x7_&x_val fundef; rewriting on 'update' ops removes dead stores. 
  
  val x7_B = { x8 => 
    if (0 < x8) 
      x7_B(x8 + -1) 
        + ((1,x8) -> 
            x7_B(x8 + -1)((1,x8)) 
            + ("head" -> x8 + -1) 
            + ("tail" -> ("B",(1,x8 + -1)))) 
    else 
      Map(1 -> 
        Map() 
        + (x8 -> 
            "undefined"((1,x8)) 
            + ("head" -> x8 + -1) 
            + ("tail" -> (A,1)))) 
  }

  Map(
    "&i" -> Map("val" -> 100), 
    "B" -> x7_B(100), 
    "&x" -> Map("val" -> (B,(1,100))), 
    "&z" -> Map("val" -> (A,1)), 
    "&y" -> Map("val" -> (B,(1,100)))
  )

  Version 4: (XXX tentative; rolled back for the time being)
  fix 'undefined' access; explicit 0 case in fundef

  val x7_B = { x8 => 
    if (0 < x8) 
      x7_B(x8 + -1) 
        + ((1,x8) -> 
            x7_B(x8 + -1)((1,x8)) 
            + ("head" -> x8 + -1) 
            + ("tail" -> ("B",(1,x8 + -1)))) 
    else "undefined" }

    Map(
      "&i" -> Map("val" -> 100), 
      "B" -> x7_B(100), 
      "&x" -> Map("val" -> (B,(1,100))), 
      "&z" -> Map("val" -> (A,1)), 
      "&y" -> Map("val" -> (B,(1,100)))
    )

    FIXME: base case at index 0 should have 'tail' pointing to (A,1)
    (question about base index again: value before or after iteration i?)

    TODO: recursive reference to previous value in 
      x7_B(x8 + -1)((1,x8)) + ("head" -> ...) + ("tail" -> ...)
    is not necessary. first, we know that x7_B only ever contains head 
    and tail fields, which would be overridden here. second, we
    know that key (1,x8) is undefined at index x8-1.

*/

  // test store logic (2): build and traverse a linked list

  test("B1") { withOutFileChecked(prefix+"B1") {
  import Test1._
    Test1.runAndCheck { // test3a
      Block(List(
        Assign("i", Const(0)),
        Assign("z", New("A")),
        Assign("x", Ref("z")),
        While(Less(Ref("i"),Const(100)), Block(List(
          Assign("y", New("B")),
          Put(Ref("y"), Const("head"), Ref("i")),
          Put(Ref("y"), Const("tail"), Ref("x")),
          Assign("x", Ref("y")),
          Assign("i", Plus(Ref("i"), Const(1)))
        ))),
        Assign("s", Const(0)),
        Assign("i", Get(Ref("x"), Const("head"))),
        Assign("x", Get(Ref("x"), Const("tail"))),
        Assign("s", Plus(Ref("s"), Ref("i")))
      ))
    }{
      """
        Map(
          "&i" -> Map("val" -> 99), 
          "B"  -> Map("top" -> 
            collect(100) { x8_B_top_x9 => 
              Map(
                "head" -> x8_B_top_x9, 
                "tail" -> if (0 < x8_B_top_x9) ("B",("top",x8_B_top_x9 + -1)) else (A,top)
              ) 
            }), 
          "&s" -> Map("val" -> 99), 
          "A"  -> Map("top" -> Map()), 
          "&x" -> Map("val" -> (B,(top,98))), 
          "&z" -> Map("val" -> (A,top)), 
          "&y" -> Map("val" -> (B,(top,99)))
        )
      """
    }
  }}


  test("B2") { withOutFileChecked(prefix+"B2") {
    import Test1._
    Test1.runAndCheck { //test3b
      Block(List(
        Assign("i", Const(0)),
        Assign("z", New("A")),
        Assign("x", Ref("z")),
        While(Less(Ref("i"),Const(100)), Block(List(
          Assign("y", New("B")),
          Put(Ref("y"), Const("head"), Ref("i")),
          Put(Ref("y"), Const("tail"), Ref("x")),
          Assign("x", Ref("y")),
          Assign("i", Plus(Ref("i"), Const(1)))
        ))),
        Assign("s", Const(0)),
        Assign("i2", Ref("i")),
        Assign("x2", Ref("x")),
        While(NotEqual(Ref("x2"),Ref("z")), Block(List(
          Assign("i2", Get(Ref("x2"), Const("head"))),
          Assign("x2", Get(Ref("x2"), Const("tail"))),
          Assign("s", Plus(Ref("s"), Ref("i2")))
        )))
      ))
    } {
      """
        Map(
          "&i"  -> Map("val" -> 100), 
          "&i2" -> Map("val" -> 0), 
          "&x2" -> Map("val" -> (A,top)), 
          "B"   -> Map("top" -> collect(100) { x8_B_top_x9 => 
                      Map(
                        "head" -> x8_B_top_x9, 
                        "tail" -> if (0 < x8_B_top_x9) ("B",("top",x8_B_top_x9 + -1)) else (A,top)
                      ) 
                    }), 
          "&s" -> Map("val" -> 4950), 
          "A"  -> Map("top" -> Map()), 
          "&x" -> Map("val" -> (B,(top,99))), 
          "&z" -> Map("val" -> (A,top)), 
          "&y" -> Map("val" -> (B,(top,99)))
        )
      """


/* old
      """
        val x8_B_top = { x9 => 
          if (0 < x9) 
            x8_B_top(x9 + -1) 
            + (x9 -> Map("head" -> x9 + -1, "tail" -> ("B",("top",x9 + -1)))) 
          else 
            Map() 
            + (x9 -> Map("head" -> x9 + -1, "tail" -> (A,top))) 
        }
        Map(
          "&i" -> Map("val" -> 
            if (0 < fixindex(x92 => if (1 < x92) 1 else x8_B_top(100)(100)("tail") != (A,top))) 
              "undefined" 
            else 
              x8_B_top(100)(100)("head")), 
          "B"  -> Map("top" -> x8_B_top(100)), 
          "&s" -> Map("val" -> 
            if (0 < fixindex(x92 => if (1 < x92) 1 else x8_B_top(100)(100)("tail") != (A,top))) 
              "undefined" 
            else 
              x8_B_top(100)(100)("head")), 
          "A"  -> Map("top" -> Map()), 
          "&x" -> Map("val" -> 
            if (0 < fixindex(x92 => if (1 < x92) 1 else x8_B_top(100)(100)("tail") != (A,top))) 
              "undefined" 
            else 
              x8_B_top(100)(100)("tail")), 
          "&z" -> Map("val" -> (A,top)), 
          "&y" -> Map("val" -> (B,(top,100)))
        )
      """
*/
    }
  }}




    // (to try: fac, first as while loop, then as recursive
    // function with defunctionalized continuations in store)



    // modify stuff after a loop

  test("C") { withOutFileChecked(prefix+"C") {
    import Test1._
    Test1.runAndCheck { //test6
      Block(List(
        Assign("i", Const(0)),
        Assign("z", New("A")),
        Assign("x", Ref("z")),
        Assign("y", New("B")),
        While(Less(Ref("i"),Const(100)), Block(List(
          Put(Ref("y"), Const("head"), Ref("i")),
          Put(Ref("y"), Const("tail"), Ref("x")),
          Assign("x", Ref("y")),
          Assign("i", Plus(Ref("i"), Const(1)))
        ))),
        Put(Ref("y"), Const("tail"), Ref("z")),
        Put(Ref("y"), Const("head"), Const(7))
      ))
    } {
      """
        Map(
          "&i" -> Map("val" -> 100), 
          "B"  -> Map("top" -> Map("head" -> 7, "tail" -> (A,top))), 
          "A"  -> Map("top" -> Map()), 
          "&x" -> Map("val" -> (B,top)), 
          "&z" -> Map("val" -> (A,top)), 
          "&y" -> Map("val" -> (B,top))
        )
      """
    }
  }}

    // strong update for if

  test("D") { withOutFileChecked(prefix+"D") {
    import Test1._
    Test1.runAndCheck { //test7
      Block(List(
        Assign("x", New("A")),
        If(Direct(vref("input")),
          Block(List(
            Put(Ref("x"), Const("a"), New("B")),
            Put(Get(Ref("x"), Const("a")), Const("foo"), Const(5))
          )),
          Block(List(
            Put(Ref("x"), Const("a"), New("C")),
            Put(Get(Ref("x"), Const("a")), Const("bar"), Const(5))
          ))
        ),
        Assign("foo", Get(Get(Ref("x"), Const("a")), Const("foo"))),
        Assign("bar", Get(Get(Ref("x"), Const("a")), Const("bar")))
      ))
    }{
      """
        Map(
          "B"  -> Map("top" -> Map("foo" -> 5)), 
          "A"  -> Map("top" -> Map("a" -> (B,top))), 
          "&x" -> Map("val" -> (A,top)), 
          "&bar" -> Map("val" -> "undefined"), 
          "&foo" -> Map("val" -> 5)
        )
      """
    }
    Test1.runAndCheck { //test8
      Block(List(
        Assign("x", New("A")),
        Put(Ref("x"), Const("a"), New("A2")),
        Put(Get(Ref("x"), Const("a")), Const("baz"), Const(3)),
        If(Direct(vref("input")),
          Block(List(
            Put(Ref("x"), Const("a"), New("B")), // strong update, overwrite
            Put(Get(Ref("x"), Const("a")), Const("foo"), Const(5))
          )),
          Block(List(
            Put(Ref("x"), Const("a"), New("C")), // strong update, overwrite
            Put(Get(Ref("x"), Const("a")), Const("bar"), Const(5))
          ))
        ),
        Put(Get(Ref("x"), Const("a")), Const("bar"), Const(7)), // this is not a strong update, because 1.a may be one of two allocs
        Assign("xbar", Get(Get(Ref("x"), Const("a")), Const("bar"))) // should still yield 7!
      ))
    }{
      """
        Map(
          "B"  -> Map("top" -> Map("foo" -> 5, "bar" -> 7)), 
          "A2" -> Map("top" -> Map("baz" -> 3)), 
          "A"  -> Map("top" -> Map("a" -> (B,top))), 
          "&x" -> Map("val" -> (A,top)), 
          "&xbar" -> Map("val" -> 7)
        )
      """
    }
  }}

    // update stuff allocated in a loop

  test("E") { withOutFileChecked(prefix+"E") {
    import Test1._
    Test1.runAndCheck { //test9
      Block(List(
        Assign("i", Const(0)),
        Assign("x", New("X")),
        Put(Ref("x"), Const("a"), New("A")),
        Put(Get(Ref("x"), Const("a")), Const("baz"), Const(3)),
        While(Less(Ref("i"),Direct(vref("COUNT"))),
          Block(List(
            Put(Ref("x"), Const("a"), New("B")), // strong update, overwrite
            Put(Get(Ref("x"), Const("a")), Const("foo"), Const(5)),
            Assign("i", Plus(Ref("i"),Const(1)))
          ))
        ),
        Put(Get(Ref("x"), Const("a")), Const("bar"), Const(7)), // this is not a strong update, because 1.a may be one of two allocs
        Assign("xbar", Get(Get(Ref("x"), Const("a")), Const("bar"))) // should still yield 7!
      ))
    } {
      """
      Map(
        "&i" -> Map("val" -> "COUNT"), 
        "B"  -> Map("top" -> 
          if (1 < "COUNT") 
            collect("COUNT") { x14_B_top_x15 => Map("foo" -> 5) } 
            + ("COUNT" + -1 -> Map("foo" -> 5, "baz" -> "nil", "bar" -> 7)) 
          else 
            collect("COUNT") { x14_B_top_x15 => Map("foo" -> 5) }
        ), 
        "X"  -> Map("top" -> Map("a" -> 
          if (1 < "COUNT") 
            ("B",("top","COUNT" + -1)) 
          else 
            (A,top)
        )), 
        "A"  -> Map("top" -> Map("baz" -> 3, "foo" -> "nil", "bar" -> if (1 < "COUNT") "nil" else 7)), 
        "&x" -> Map("val" -> (X,top)), 
        "&xbar" -> Map("val" -> 7)
      )
      """
    }
  }}


  // factorial: direct
  test("F1") { withOutFileChecked(prefix+"F1") {
    import Test1._
    Test1.runAndCheck {
      Block(List(
        Assign("n", Direct(vref("N"))),
        Assign("i", Const(0)),
        Assign("r", Const(1)),
        While(Less(Ref("i"),Ref("n")),
          Block(List(
            Assign("i", Plus(Ref("i"),Const(1))),
            Assign("r", Times(Ref("r"),Ref("i")))
          ))
        )
      ))
    } {
      """
        val x7_&r_val = { x8 => if (0 < x8) x7_&r_val(x8 + -1) * x8 + x7_&r_val(x8 + -1) else x8 + 1 }
        Map(
          "&n" -> Map("val" -> "N"), 
          "&i" -> Map("val" -> "N"), 
          "&r" -> Map("val" -> x7_&r_val("N" + -1))
        )
      """
    }
  }}
}



/*

McCarthy's 91 program:

MC(n)= if (n>100) n-10 else MC(MC(n + 11)) // n ≤ 100

equivalent to:

MC(n)= (n>100) n-10 else 91

non-recursive version:

 int mccarthy(int n)
 {
     int c;
     for (c = 1; c != 0; ) {
         if (n > 100) {
             n = n - 10;
             c--;
         } else {
             n = n + 11;
             c++;
         }
     }
     return n;
 }


*/