package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

import CFrontend2._
import Test1._
import IRD._

object ProgEquiv {

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
    val store1 = evalCFG(cfgs1("main"))

    System.err.println(termToString(store1))

    val parsed2 = parseCString(tup._2)
    val cfgs2 = fileToCFG(parsed2)
    val store2 = evalCFG(cfgs2("main"))

    System.err.println(termToString(store2))

    (store1 == store2, store1, store2)
  }
}
