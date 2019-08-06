package analysis

import org.scalatest._

trait RunAndCheckSuite extends FileDiffSuite with MainAux {

  def prefix: String

  def clean(s: String) = s.replaceAll("\"","").replaceAll("\n","").replaceAll(" +","")

  def testProg(name: String)(block: => Exp)(want: Any): Unit =
    test(name) {
      withOutFileChecked(prefix+name) {
        val out = runAndCheck { block }
        if (want != "")
          assert(clean(out) === clean(want.toString)) //sanitize...
      }
    }

}
