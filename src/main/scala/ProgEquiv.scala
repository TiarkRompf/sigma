package analysis

object ProgEquiv extends CFGtoEngine with Test1 {
  import IRD._

  val assign_loop = ("""
    int main() {
      int a = __VERIFIER_nondet_int();
      if (a < 0) a = 0;
      int b = 1;
      while (b < a) {
        b = b + 1;
      }
      return b;
    }""",
    """
    int main() {
      int a = __VERIFIER_nondet_int();
      if (a < 0) a = 0;
      int b = 0;
    more:
      b = 1 + b;
      if (b < a) goto more;
      return b;
    }
    """)

  def isEquiv(tup: (String, String)) = {

    val parsed1 = parseCString(tup._1)
    val cfgs1 = fileToCFG(parsed1)
    val (args, cfg) = cfgs1("main")
    val store1 = evalCFG(args, cfg)

    System.err.println(termToString(store1))

    val parsed2 = parseCString(tup._2)
    val cfgs2 = fileToCFG(parsed2)
    val (args2, cfg2) = cfgs2("main")
    val store2 = evalCFG(args2, cfg2)

    System.err.println(termToString(store2))

    (store1 == store2, store1, store2)
  }
}
