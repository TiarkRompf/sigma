package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

import CFrontend2._
import Test1._
import IRD._

object MyMain {
  def testOmega = {
    import Constraint._
    import Problem._
    // if (100 < x0? + 1) 1 else x0? < 101
    val cond = GT(List(-99, 1), List(PConst, "x0"))
    val thenBr = Problem(cond.toGEQ ++ List(TRUE))
    val elseBr = Problem(cond.negation ++ GT(List(101, -1), List(PConst, "x0")).toGEQ)
    val alwaysValid = thenBr.hasIntSolutions && elseBr.hasIntSolutions
    assert(alwaysValid)
    println(s"alwaysValid: $alwaysValid")

    val alwaysValid1 = Problem(cond.toGEQ).implies(Problem(List(TRUE))) && 
                       Problem(cond.negation).implies(Problem(GT(List(101, -1), List(PConst, "x0")).toGEQ))
    assert(alwaysValid1)
  }

  def main(arr: Array[String]) = {
    val code = """
    #define NULL 0
    struct list {
      int value;
      struct list* next;
    };
    int main() {
      int n = 5;
      struct list* x = (struct list *) NULL; // malloc(sizeof(struct list));
      int i = 0;
      while (i < n) {
        struct list* y = (struct list *) malloc(sizeof(struct list));
        y->value = i;
        y->next = x;
        x = y;
        i = i + 1;
      }

      struct list* z = x;
      int agg = 0;
      i = 0;
      while (i < n) {
        agg = agg + z->value;
        z = z->next;
        i = i + 1;
      }

      assert(2 * agg == n * (n - 1));
      return 0;
    }
    """
    val code1 = """
    #define NULL 0
    struct list {
      int value;
      struct list* next;
    };
    int main() {
      int n = 5;
      struct list* x = (struct list *) NULL; // malloc(sizeof(struct list));
      int i = 0;
      while (i < n) {
        struct list* y = (struct list *) malloc(sizeof(struct list));
        y->value = i;
        y->next = x;
        x = y;
        i = i + 1;
      }

      struct list* z = x;
      int agg = 0;
      while (z != NULL) {
        agg = agg + z->value;
        z = z->next;
      }

      assert(2 * agg == n * (n - 1));
      return 0;
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
      if (n < 0) n = 0;
      struct list* x = (struct list *) NULL; // malloc(sizeof(struct list));
      int i = 0;
      while (i < n) {
        struct list* y = (struct list *) malloc(sizeof(struct list));
        y->value = i;
        y->next = x;
        x = y;
        i = i + 1;
      }

      struct list* z = x;
      int agg = 0;
      i = 0;
      while (i < n) {
        agg = agg + z->value;
        z = z->next;
        i = i + 1;
      }

      assert(2 * agg == n * (n - 1));
      return 0;
    }
    """
    val code3 = """
    #define NULL 0
    struct list {
      int value;
      struct list* next;
    };
    int main() {
      int n = __VERIFIER_nondet_int();
      if (n < 0) n = 0;
      struct list* x = (struct list *) NULL; // malloc(sizeof(struct list));
      int i = 0;
      while (i < n) {
        struct list* y = (struct list *) malloc(sizeof(struct list));
        y->value = i;
        y->next = x;
        x = y;
        i = i + 1;
      }

      struct list* z = x;
      int agg = 0;
      while (z != NULL) {
        agg = agg + z->value;
        z = z->next;
      }

      assert(2 * agg == n * (n - 1));
      return 0;
    }
    """
    val parsed = parseCString(code2)
    val cfgs = fileToCFG(parsed)

    evalCfgUnit(parsed)
    val store = evalCFG(cfgs("main"))
    println(s"Store: $store")
    val valid = store match {
      case GConst(m: Map[GVal,GVal]) => m.get(GConst("valid"))
      case Def(DMap(m)) => m.get(GConst("valid"))
    }

    println(s"Valid: ${valid.getOrElse(valid)}")

    testOmega
  }
}
