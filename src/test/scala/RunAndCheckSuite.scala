package analysis

import org.scalatest._

trait RunAndCheckSuite extends FileDiffSuite {
  
  def prefix: String

  def testProg(name: String)(block: =>Frontend.Exp)(want: Any): Unit = 
    test(name) { withOutFileChecked(prefix+name) {
      Main.runAndCheck { block } { want }
    }}

}
