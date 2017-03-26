package analysis

import org.eclipse.cdt.core.dom.ast._
import org.eclipse.cdt.internal.core.dom.parser.c._

import scala.collection.{mutable,immutable}
import mutable.ArrayBuffer

import Util._

object CFGtoEngine {
  import CFGBase._
  import Test1._
  import Approx._
  val IR = IRD

  type Val = IR.From

  val trackValid = false

  val store0 = if (trackValid) GConst(Map(GConst("valid") -> GConst(1))) else GConst(Map())

  val itvec0 = IR.const("top")

  var store: Val = store0
  var itvec: Val = itvec0

  def evalStm(x: IASTStatement): Any = {
    CPrinter.evalStm(x)
  }
  def evalExp(x: IASTNode): Val = {
    GConst(CPrinter.evalExp(x))
  }

  def handleReturn(e: Val): Unit = {
    println("return "+e)
  }

  def handleContinue(l: String): Unit = {
    println("${l}_more = true")
  }


  def evalCFG(cfg: CFG): Unit = {
    import cfg._
    val blockIndex = cfg.blockIndex

    var fuel = 500*1000
    def consume(l: String, stop: Set[String], cont: Set[String]): Unit = {
      fuel -= 1; if (fuel == 0) throw new Exception("XXX consume out of fuel")
      
      if (stop contains l) {
        //println("// break "+l)
        return
      }
      if (cont contains l) {
        //println("// continue "+l)
        return handleContinue(l)
      }

      //println("// "+l)
      val b = blockIndex(l)

      // strict post-dominators (without self)
      val sdom = postDom(l)-l
      // immediate post-dominator (there can be at most one)
      var idom = sdom.filter(n => sdom.forall(postDom(n)))
      // Currently there's an issue in 
      // loop-invgen/string_concat-noarr_true-unreach-call_true-termination.i
      // TODO: use Cooper's algorithm to compute idom directly
      if (idom.contains("STUCK")) idom = Set("STUCK") // HACK
      if (l == "STUCK") idom = Set() // HACK
      assert(idom.size <= 1, s"sdom($l) = $sdom\nidom($l) = ${idom}")


      def evalBody(stop1: Set[String], cont1: Set[String]): Unit = {
        b.stms.foreach(evalStm)
        b.cnt match {
          case Return(e) => 
            handleReturn(evalExp(e))
            assert(idom.isEmpty)
          case Jump(a) => 
            assert(a == l || idom == Set(a)) // handled below
          case CJump(c,a,b) => 
            println("if "+evalExp(c)+" {")
            consume(a, stop1, cont1)
            println("} else {")
            consume(b, stop1, cont1)
            println("}")
        }
      }

      // Simplifying assumption: the immediate post-dominator
      // of a loop header is *outside* the loop. This is not
      // necessarily true in general.
      // TODO: refine to compute post-dom outside loop.
      val isLoop = loopHeaders contains l
      if (isLoop) {
        println("do {")
        println(s"bool ${l}_more = false")
        evalBody(idom, cont + l)
        println(s"} while (${l}_more)")
      } else {
        evalBody(idom, cont)
      }

      if (idom.nonEmpty)
        consume(idom.head, stop, cont)
    }
    time{consume(entryLabel, Set.empty, Set.empty)}
  }

}
