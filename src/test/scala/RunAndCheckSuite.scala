package analysis

import org.scalatest._

trait RunAndCheckSuite extends FileDiffSuite {
  
  def prefix: String

  def testProg(name: String)(block: =>Frontend.Exp)(want: Any): Unit = 
    test(name) { 
      var out = ""
      withOutFileChecked(prefix+name) {
            out = Main.runAndCheck { block }
      }
      def clean(s: String) = s.replaceAll("\"","").replaceAll("\n","").replaceAll(" +","")
      if (want != "")
        assert(clean(out) === clean(want.toString)) //sanitize...
    }

}
