package analysis

import org.eclipse.cdt.core.dom.ast._
import org.eclipse.cdt.internal.core.dom.parser.c._

import scala.collection.{mutable,immutable}
import mutable.ArrayBuffer

import Util._

object CFGtoEngine {
  import CFGBase._

  import CPrinter._
  import CFGBase._

  def evalCFG(cfg: CFG): Unit = {
    import cfg._
    val blockIndex = cfg.blockIndex

    println("# control-flow graph:")

    for (v <- blocks) {
      println(v.label+": {")
      v.stms.foreach(evalStm)
      println(v.cnt)
      println("}")
    }

    println("# loop headers:")
    println(loopHeaders)

    println("# post dominators:")
    println(postDom)

    println("# restructure:")

    var fuel = 500*1000
    def consume(l: String, stop: Set[String], cont: Set[String]): Unit = {
      fuel -= 1; if (fuel == 0) throw new Exception("XXX consume out of fuel")
      
      if (stop contains l) {
        //println("// break "+l)
        return
      }
      if (cont contains l) {
        //println("// continue "+l)
        println(s"${l}_more = true")
        return
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
            println("return "+evalExp(e))
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
