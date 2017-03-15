package analysis

import CFrontend._

class CTest1 extends FileDiffSuite {

  val prefix = "test-out/test-c-1"

  test("A1") { withOutFileChecked(prefix+"A1") {

    val parsed = parseCFile("test-in/cpachecker-example.c")
    evalUnit(parsed)

  }}

  /*test("A2") { withOutFileChecked(prefix+"A2") {

    println("done here ...")
  }}*/

}