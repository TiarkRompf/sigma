package analysis

import CFrontend._

class CTest1 extends FileDiffSuite {

  val prefix = "test-out/test-c-1"

  test("A1") { withOutFileChecked(prefix+"A1") {

    val file = "test-in/cpachecker-example.c"
    println("// # literal source")
    println(readFile(file))    
    val parsed = parseCFile(file)
    //evalUnit(parsed)
    evalCfgUnit(parsed)


  }}

  /*test("A2") { withOutFileChecked(prefix+"A2") {

    println("done here ...")
  }}*/

}