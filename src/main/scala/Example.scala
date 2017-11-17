package analysis

object Example {

  val two_loops = """
  int main() {
    int n = __VERIFIER_nondet_int();
    if (n <= 0) n = 0;
    int i = 0;
    int agg = 0;

    while (i < n) {
      agg = agg + i;
      i = i + 1;
    }

    i = 0;
    int agg1 = 0;
    while (i < n) {
      agg1 = agg1 + i;
      i = i + 1;
    }

    assert(agg == agg1);

    return 0;
  }

  """
  val two_loops1 = """
  int main() {
    int n = __VERIFIER_nondet_int();
    if (n <= 0) n = 0;
    int i = 0;
    int agg = 0;

    while (i < n) {
      agg = agg + 1;
      i = i + 1;
    }

    int m = __VERIFIER_nondet_int();
    if (m <= 0) m = 0;
    i = 0;

    while (i < m) {
      agg = agg - 1;
      i = i + 1;
    }

    assert(2 * agg == n - m);

    return 0;
  }

  """

  val two_loops2 = """
  int main() {
    int n = __VERIFIER_nondet_int();
    if (n <= 0) n = 0;
    int i = 0;
    int agg = 0;

    while (i < n) {
      agg = agg + i;
      i = i + 1;
    }

    int m = __VERIFIER_nondet_int();
    if (m <= 0) m = 0;
    i = 0;

    while (i < m) {
      agg = agg - i;
      i = i + 1;
    }

    assert(2 * agg == n*(n - 1) - m*(m - 1));

    return 0;
  }

  """

}
