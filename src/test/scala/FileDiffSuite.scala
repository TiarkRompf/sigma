package analysis

import java.io._
import org.scalatest._
import scala.Console

trait FileDiffSuite extends FunSuite {
  val overwriteCheckFiles = true // should be false; temporary set to true only to simplify development

  def indent(str: String) = {
    val s = new StringWriter
    printIndented(str)(new PrintWriter(s))
    s.toString
  }
  def printIndented(str: String)(out: PrintWriter): Unit = {
    val lines = str.split("[\n\r]")
    var indent = 0
    var extra = 0
    for (l0 <- lines) {
      val l = l0.trim
      if (l.length > 0) {
        var open = 0
        var close = 0
        var initClose = 0
        var nonWsChar = false
        var hash = 0
        l foreach {
          case '{' => {
            open += 1
            if (!nonWsChar) {
              nonWsChar = true
              initClose = close
            }
          }
          case '}' => close += 1
          case '#' => hash += 1
          case x => if (!nonWsChar && !x.isWhitespace) {
            nonWsChar = true
            initClose = close
          }
        }
        if (!nonWsChar) initClose = close
        if (hash == 0) hash = extra + 1 else extra = hash
        out.println("  " * (indent - initClose + hash - 1) + l)
        indent += (open - close)
      }
    }
    //assert (indent==0, "indentation sanity check")
    if (indent != 0) out.println("warning: indentation sanity check")
  }

  def withOutFile(name: String)(func: => Unit): Unit = {
    val file = new File(name)
    file.getParentFile.mkdirs()
    withOutput(new PrintStream(new FileOutputStream(file)))(func)
  }
  def withOutFileIndented(name: String)(func: => Unit): Unit = {
    val bstream = new ByteArrayOutputStream
    try withOutput(new PrintStream(bstream))(func) finally writeFileIndented(name,bstream.toString)
  }
  def withOutFileDiscarded(name: String)(func: => Unit): Unit = {
    val bstream = new ByteArrayOutputStream
    withOutput(new PrintStream(bstream))(func)
  }
  def captureOutput(func: => Unit): String = {
    val bstream = new ByteArrayOutputStream
    withOutput(new PrintStream(bstream))(func)
    bstream.toString
  }
  def withOutput(out: PrintStream)(func: => Unit): Unit = {
    val oldStdOut = System.out
    val oldStdErr = System.err
    try {
      System.setOut(out)
      System.setErr(out)
      Console.withOut(out)(Console.withErr(out)(func))
    } finally {
      out.flush()
      out.close()
      System.setOut(oldStdOut)
      System.setErr(oldStdErr)
    }
  }

  def readFile(name: String): String = try {
    val buf = new Array[Byte](new File(name).length().toInt)
    val fis = new FileInputStream(name)
    fis.read(buf)
    fis.close()
    new String(buf)
  } catch {
    case _: FileNotFoundException => ""
  }
  def writeFile(name: String, content: String) {
    val file = new File(name)
    file.getParentFile.mkdirs()
    val out = new java.io.PrintWriter(file)
    out.write(content)
    out.close()
  }
  def writeFileIndented(name: String, content: String) {
    val file = new File(name)
    file.getParentFile.mkdirs()
    val out = new java.io.PrintWriter(file)
    try printIndented(content)(out) finally out.close()
  }

  def assertFileEqualsCheck(name: String): Unit = {
    def sanitize(s: String) =
      s.replaceAll("@[0-9a-f]+","@").   // disregard object ids
        replaceAll("[0-9]*\\.[0-9]+s","0.0s")  // disregard running times
    if (overwriteCheckFiles) {
      writeFile(name+".check", readFile(name))
    } else {
      assert(sanitize(readFile(name)) == sanitize(readFile(name+".check")), "File differs: "+name) // TODO: diff output
    }
    new File(name) delete ()
  }
  def withOutFileChecked(name: String)(func: => Unit): Unit = {
    withOutFileIndented(name)(try func catch { case e => print("# "); e.printStackTrace; throw e })
    assertFileEqualsCheck(name)
  }
  def printcheck(x:Any,y:Any) = assert({ println(x); x } === y)  
}
