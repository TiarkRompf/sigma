package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

import CFrontend2._
import Test1._
import IRD._

import Omega._

object MyMain {
  def testOmega = {
    import Constraint._
    import Problem._
    // if (100 < x0? + 1) 1 else x0? < 101
    val cond = GT(List(-100, 1), List(PConst, "x0"))
    val thenBr = Problem(cond.toGEQ ++ List(TRUE))
    val elseBr = Problem(cond.negation(0) ++ GT(List(100, -1), List(PConst, "x0")).toGEQ)
    val alwaysValid = thenBr.hasIntSolutions && elseBr.hasIntSolutions
    assert(alwaysValid)
    println(s"alwaysValid: $alwaysValid")

    val alwaysValid1 = Problem(cond.toGEQ).implies(Problem(List(TRUE))) &&
                       Problem(cond.negation(0)).implies(Problem(GT(List(101, -1), List(PConst, "x0")).toGEQ))
    assert(alwaysValid1)
  }


    val simple_code = """
    int main() {
      int n = __VERIFIER_nondet_int();
      if (n > 100)
        n = 100;
      assert(n <= 100);
      return 0;
    }
    """
    val simple_code1 = """
    int main() {
      int n = __VERIFIER_nondet_int();
      if (n <= 0)  n = 0;
      // int n = 5;

      int i = 0;
      int agg = 0;
      while (i < n) {
        agg = agg + i;
        i = i + 1;
      }

      assert(2 * agg == n * (n - 1));
      return 0;
    }
    """

    val simple_nest = """
    // PASS
    int main() {
      int n = 5;
      int m = 4;
      int i = 0; int j = 0;
      int agg = 0;
      while (i < n) {
        while (j < m) {
          agg = agg + 1;
          j = j + 1;
        }
        j = 0;
        i = i + 1;
      }
      assert(agg == n * m);
      return 0;
    }
    """

    val simple_nest1 = """
    // NOT WORK
    int main() {
      int n = __VERIFIER_nondet_int();
      if (n < 0) n = 0;
      int m = __VERIFIER_nondet_int();
      if (m < 0) m = 0;
      int i = 0; int j = 0;
      int agg = 0;
      while (i < m) {
        while (j < n) {
          agg = agg + 1;
          j = j + 1;
        }
        j = 0;
        i = i + 1;
      }
      assert(agg == n * m);
      return 0;
    }
    """

    val simple_nest2 = """
    // NOT WORK
    int main() {
      int n = 5; int m = 4; int p = 3;
      int i = 0; int j = 0; int k = 0;
      int agg = 0;
      while (i < n) {
        while (j < m) {
          while (k < p) {
            agg = agg + 1;
            k = k + 1;
          }
          k = 0;
          j = j + 1;
        }
        j = 0;
        i = i + 1;
      }
      assert(agg == (n * (m * p));
      return 0;
    }
    """

    val code = """
    #define NULL 0
    struct list {
      int value;
      struct list* next;
    };
    int main() {
      int n = 2;
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
      while (z != (struct list *)NULL) {
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
      if (n <= 0) n = 0;
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
      while (z != (struct list *)NULL) {
        agg = agg + z->value;
        z = z->next;
      }

      assert(2 * agg == n * (n - 1));
      return 0;
    }
    """

  val sv1 = """
  int main() {
    int i,j,k;
    i = 0;
    k = 9;
    j = -100;
    while (i <= 100) {
      i = i + 1;
      while (j < 20) {
	j = i + j;
      }
      k = 4;
      while (k <= 3) {
	k = k + 1;
      }
    }
    __VERIFIER_assert(k == 4);
    return 0;
  }
  """

  val simple_sv1 = """
  int main() {
    int k;
    k = 4;
    while (k <= 3) {
      k = k + 1;
    }
    __VERIFIER_assert(k == 4);
    return 0;
  }
  """

  def constant(it: Int) = s"""
  int main() {
    int k, i;
    k = 4;
    i = 0;
    while (i < $it) {
      k = 9;
      i = i + 1;
    }
    __VERIFIER_assert(($it > 0 && k == 9) || ($it == 0 && k == 4));
    return 0;
  }
  """

  val sv2 = """
int main() {
    int i,j,k,n,l,m;
    n = __VERIFIER_nondet_int();
    m = __VERIFIER_nondet_int();
    l = __VERIFIER_nondet_int();
    __VERIFIER_assume(-1000000 < n && n < 1000000);
    __VERIFIER_assume(-1000000 < m && m < 1000000);
    __VERIFIER_assume(-1000000 < l && l < 1000000);
    if(3*n<=m+l); else goto END;
    for (i=0;i<n;i++)
        for (j = 2*i;j<3*i;j++)
            for (k = i; k< j; k++)
                __VERIFIER_assert( k-i <= 2*n );
END:
    return 0;
}
  """

  val incr2 = """
  int main() {
    int n;
    int i;
    int agg = 0;

    n = __VERIFIER_nondet_int();
    if (n < 0) n = 0;


    for (i = 0; i < 2 * n; i = i + 2)
      agg = agg + i;

    assert(agg == n * (n - 1));
    return 0;
  }
  """

  val infloop = """
int main() {
    int lo, mid, hi;
    lo = 0;
    mid = __VERIFIER_nondet_int();
    __VERIFIER_assume(mid > 0 && mid <= 1000000);
    hi = 2*mid;
    while (mid > 0) {
        lo = lo + 1;
        hi = hi - 1;
        mid = mid - 1;
    }
    __VERIFIER_assert(lo == hi);
    return 0;
}
    """

    val nbreak = """
int main() {
    int x = 0;
    int y = 50;
    while(x < 100) {
      if (x < 50) {
        x = x + 1;
      } else {
        x = x + 1;
        y = y + 1;
      }
    }
    __VERIFIER_assert(y == 100);
    return 0;
}
          """

  val sin = """
int main() {
  int i,j,k;
  i = 0;
  k = 9;
  j = -100;
  while (i <= 100) {
    i = i + 1;
    while (j < 20) {
      j = i + j;
    }
    k = 4;
    while (k <= 3) {
      k = k + 1;
    }
  }
  __VERIFIER_assert(k == 4);
  return 0;
}
"""

   def analyze(code: String) = {
    val parsed = parseCString(code)
    val cfgs = fileToCFG(parsed)

    val store = evalCFG(cfgs("main"))

    val valid = store match {
      case GConst(m: Map[GVal,GVal]) => m.get(GConst("valid"))
      case Def(DMap(m)) => m.get(GConst("valid"))
    }
    println(s"Valid: ${termToString(valid.get)}")

    // Should be something like this for simple_code
    // { -100 + 1x0? >= 0 } ==> { 0 = 0 } &&
    // { 99 - 1x0? >= 0 } ==> { 100 - 1x0? >= 0 }
    val validOmega = translateBoolExpr(IR.not(valid.get))
    println(s"!valid (omega form): $validOmega")
    assert(!verify(validOmega))
    //OmegaTest.test
  }


  def main(arr: Array[String]) = {
    analyze(infloop) // constant(arr(0).toInt))
  }
}
