package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

class CTest2 extends FileDiffSuite {

  val prefix = "test-out/test-c-2"

  test("A1") { withOutFileChecked(prefix+"A1") {
    val code = """
    int main() {
      int x = 0;
      ++x;
      assert(x == 1);
      return 0;
    }
    """

    val parsed = parseCString(code)
    val cfgs = fileToCFG(parsed)
    evalCFG(cfgs("main"))
  }}

  test("A2") { withOutFileChecked(prefix+"A2") {
    val code = """
    int main() {
      int x = 0;
      if (x == 0) {
      } else
        assert(x == 1);
      }
      return 0;
    }
    """

    val parsed = parseCString(code)
    val cfgs = fileToCFG(parsed)
    evalCFG(cfgs("main"))
  }}

}