package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

import CFrontend2._
import Test1._
import IRD._

object MyMain {
  def main(arr: Array[String]) = {
    val code1 = """
    int main() {
      int a[1];
      return a[0];
    }
    """
    val code2 = """
    #define NULL 0
    struct list {
      int value;
      struct list* next;
    };
    int main() {
      int n = __VERIFIER_nondet_int();
      struct list* x = NULL;
      int i = 0;
      while (i < n) {
        struct list* y = (struct list *) malloc(sizeof(struct list));
        y->tail = x;
        y->tail = i++;
        x = y;
      }
      struct list* z = x;
      int s = 0;
      while (z != NULL) {
        s = s + z->head;
        z = z->tail;
      }

      assert(2*s == n*(n-1));
      return 0;
    }
    """
    val parsed = parseCString(code)
    val cfgs = fileToCFG(parsed)

    evalCfgUnit(parsed)
    val store = evalCFG(cfgs("main"))
    val valid = store match {
      case GConst(m: Map[GVal,GVal]) => m.get(GConst("valid"))
      case Def(DMap(m)) => m.get(GConst("valid"))
    }

    println(s"Valid: ${valid.getOrElse(valid)}")
  }
}
