package analysis

import CBase._
import CtoCFG._
import CFGtoEngine._

import CFrontend2._
import Test1._
import IRD._

class CTest2 extends FileDiffSuite {

  val prefix = "test-out/test-c-2"

  def runAndCheck(code: String) = {
    val parsed = parseCString(code)
    val cfgs = fileToCFG(parsed)

    evalCfgUnit(parsed)
    val store = evalCFG(cfgs("main"))
    val valid = store match {
      case GConst(m: Map[GVal,GVal]) => m.get(GConst("valid"))
      case Def(DMap(m)) => m.get(GConst("valid"))
      case _ => ???
    }

    assert(valid.getOrElse(GError) == GConst(1), s": valid -> ${IR.termToString(valid.getOrElse(GError))}")
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

  test("A2") { withOutFileChecked(prefix+"A2") {
    val code = """
    int main() {
      int i = 0;
      while (1) {
        if (i < 100)
          i = i + 1;
        else
          goto out;
      }
      out:
      assert(i == 100);
      return 0;
    }
    """
    runAndCheck(code)
  }}

  // should be same as above (!= 100 vs < 100)
  test("A3") { withOutFileChecked(prefix+"A3") {
    val code = """
    int main() {
      int i = 0;
      while (1) {
        if (i != 100)
          i = i + 1;
        else
          goto out;
      }
      out:
      assert(i == 100);
      return 0;
    }
    """
    runAndCheck(code)
  }}

  test("A4") { withOutFileChecked(prefix+"A4") {
    val code = """
    int main() {
      int i = 0;
      loop: {
        int more = 0;
        if (i != 100) {
          i = i + 1;
          more = 1;
        }
        if (more)
          goto loop;
      }
      assert(i == 100);
      return 0;
    }
    """
    runAndCheck(code)
  }}

}
