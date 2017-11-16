package analysis

import SimpleFrontend._

class TestAnalysis6 extends RunAndCheckSuite {

  val prefix = "test-out/test-analysis-6"
  // test store logic (1): build a linked list

  testProg("B0") { // test3
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
      {
        "&i" -> {"val" -> 100},
        "B"  -> {"top" ->
          collect(100) { x8_B_top_x9 =>
            {
              "head" -> x8_B_top_x9,
              "tail" -> if ((0 < x8_B_top_x9)) { ("B",("top",(x8_B_top_x9 + -1))) }
                        else                 { (A,top) }
            }
          }},
        "A"  -> {"top" -> Map()},
        "&x" -> {"val" -> (B,(top,99))},
        "&z" -> {"val" -> (A,top)},
        "&y" -> {"val" -> (B,(top,99))}
      }
      """
    }


  // back to simpler tests (compare to test3)
  // 3 and 4 should be different: alloc within the loop vs before

  testProg("B1") { // test4
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
      {
        "&i" -> {"val" -> 100},
        "B"  -> {"top" -> {
                              "head" -> 99,
                              "tail" -> (B,top)}},
        "A"  -> {"top" -> Map()},
        "&x" -> {"val" -> (B,top)},
        "&z" -> {"val" -> (A,top)},
        "&y" -> {"val" -> (B,top)}
      }
      """
    }

  testProg("B2") { // test5
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
      {
        "&i" -> {"val" -> 100},
        "A"  -> {"top" -> {"head" -> 99}},
        "&z" -> {"val" -> (A,top)},
        "&x" -> {"val" -> (A,top)}
      }
      """
    }



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
      + ("&y" -> {"val" -> ("B",(1,x8))))
      + (("B",(1,x8)) ->
          x7(x8 + -1)(("B",(1,x8)))
          + ("head" -> x7(x8 + -1)("&i")("val")))
      + (("B",(1,x8)) ->
          x7(x8 + -1)(("B",(1,x8)))
          + ("head" -> x7(x8 + -1)("&i")("val"))
          + ("tail" -> x7(x8 + -1)("&x")("val")))
      + ("&x" -> {"val" -> ("B",(1,x8))))
      + ("&i" -> {"val" -> x7(x8 + -1)("&i")("val") + 1))
  else
    {"&i" -> {"val" -> 0), "&z" -> {"val" -> (A,1)), "&x" -> {"val" -> (A,1)), "&y" -> {"val" -> ("B",(1,x8))))
      + (("B",(1,x8)) -> {"head" -> 0))
      + (("B",(1,x8)) -> {"head" -> 0, "tail" -> (A,1)))
      + ("&x" -> {"val" -> ("B",(1,x8))))
      + ("&i" -> {"val" -> 1))
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
      {1 ->
        {)
        + (x8 ->
            "undefined"((1,x8))       <--- accessing "undefined": base case?
            + ("head" -> x8 + -1))
        + (x8 ->
            "undefined"((1,x8))
            + ("head" -> x8 + -1)
            + ("tail" -> (A,1))))
  }

  {
    "&i" -> {"val" -> 100),
    "B" -> x7_B(100),
    "&x" -> {"val" -> (B,(1,100))),
    "&z" -> {"val" -> (A,1)),
    "&y" -> {"val" -> (B,(1,100))))


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
      {1 ->
        {)
        + (x8 ->
            "undefined"((1,x8))
            + ("head" -> x8 + -1)
            + ("tail" -> (A,1))))
  }

  {
    "&i" -> {"val" -> 100),
    "B" -> x7_B(100),
    "&x" -> {"val" -> (B,(1,100))),
    "&z" -> {"val" -> (A,1)),
    "&y" -> {"val" -> (B,(1,100)))
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

    {
      "&i" -> {"val" -> 100),
      "B" -> x7_B(100),
      "&x" -> {"val" -> (B,(1,100))),
      "&z" -> {"val" -> (A,1)),
      "&y" -> {"val" -> (B,(1,100)))
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

  testProg("C1") { // test3a
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
        {
          "&i" -> {"val" -> 99},
          "B"  -> {"top" ->
            collect(100) { x8_B_top_x9 =>
              {
                "head" -> x8_B_top_x9,
                "tail" -> if ((0 < x8_B_top_x9)) { ("B",("top",(x8_B_top_x9 + -1))) } else { (A,top) }
              }
            }},
          "&s" -> {"val" -> 99},
          "A"  -> {"top" -> Map()},
          "&x" -> {"val" -> (B,(top,98))},
          "&z" -> {"val" -> (A,top)},
          "&y" -> {"val" -> (B,(top,99))}
        }
      """
    }


  testProg("C2") { //test3b
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
        {
          "&i"  -> {"val" -> 100},
          "&i2" -> {"val" -> 0},
          "&x2" -> {"val" -> (A,top)},
          "B"   -> {"top" -> collect(100) { x8_B_top_x9 =>
                      {
                        "head" -> x8_B_top_x9,
                        "tail" -> if ((0 < x8_B_top_x9)) {("B",("top",(x8_B_top_x9 + -1)))} else {(A,top)}
                      }
                    }},
          "&s" -> {"val" -> 4950},
          "A"  -> {"top" -> Map()},
          "&x" -> {"val" -> (B,(top,99))},
          "&z" -> {"val" -> (A,top)},
          "&y" -> {"val" -> (B,(top,99))}
        }
      """

/* old
      """
        val x8_B_top = { x9 =>
          if (0 < x9)
            x8_B_top(x9 + -1)
            + (x9 -> {"head" -> x9 + -1, "tail" -> ("B",("top",x9 + -1))))
          else
            {)
            + (x9 -> {"head" -> x9 + -1, "tail" -> (A,top)))
        }
        {
          "&i" -> {"val" ->
            if (0 < fixindex(x92 => if (1 < x92) 1 else x8_B_top(100)(100)("tail") != (A,top)))
              "undefined"
            else
              x8_B_top(100)(100)("head")),
          "B"  -> {"top" -> x8_B_top(100)),
          "&s" -> {"val" ->
            if (0 < fixindex(x92 => if (1 < x92) 1 else x8_B_top(100)(100)("tail") != (A,top)))
              "undefined"
            else
              x8_B_top(100)(100)("head")),
          "A"  -> {"top" -> {)),
          "&x" -> {"val" ->
            if (0 < fixindex(x92 => if (1 < x92) 1 else x8_B_top(100)(100)("tail") != (A,top)))
              "undefined"
            else
              x8_B_top(100)(100)("tail")),
          "&z" -> {"val" -> (A,top)),
          "&y" -> {"val" -> (B,(top,100)))
        )
      """
*/
  }

}
