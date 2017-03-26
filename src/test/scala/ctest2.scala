package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

class CTest2 extends FileDiffSuite {

  val prefix = "test-out/test-c-2"

  def runAndCheck(code: String) = {
    val parsed = parseCString(code)
    val cfgs = fileToCFG(parsed)

    import Test1._

    store = store0
    itvec = itvec0
    varCount = varCount0
    globalDefs = globalDefs0
    rebuildGlobalDefsCache()

    evalCFG(cfgs("main"))
  }


  test("A0") { withOutFileChecked(prefix+"A0") {
    val code = """
    int main() {
      int x = 0;
      ++x;
      assert(x == 1);
      return 0;
    }
    """
    runAndCheck(code)
  }}

  test("A1") { withOutFileChecked(prefix+"A1") {
    val code = """
    int main() {
      int i = 0;
      int y = 0;
      int x = 8;
      while (i < 100) {
        x = 7;
        x = x + 1;
        y = y + 1;
        i = i + 1;
      }
      assert(x == 8);
      assert(y == 100);
      assert(i == 100);
      return 0;
    }
    """
    runAndCheck(code)
  }}

}