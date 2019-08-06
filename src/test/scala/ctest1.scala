package analysis

class CTest1 extends FileDiffSuite with CtoCFG with CFGPrinter {

  val prefix = "test-out/test-c-1"

  test("A1") { withOutFileChecked(prefix+"A1") {

    val file = "test-in/cpachecker-example.c"
    println("// # literal source")
    println(readFile(file))
    val parsed = parseCFile(file)
    //evalUnit(parsed)

    val cfgs = fileToCFG(parsed)
    val (args, cfg) = cfgs("main")
    evalCFG(cfg)


  }}

  /*test("A2") { withOutFileChecked(prefix+"A2") {

    println("done here ...")
  }}*/

}
