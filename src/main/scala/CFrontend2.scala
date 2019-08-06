package analysis

import org.eclipse.cdt.core.dom.ast._
import org.eclipse.cdt.internal.core.dom.parser.c._

import scala.collection.{mutable,immutable}
import mutable.ArrayBuffer

import Util._

trait CFGBase extends CBase {

  abstract class Continuation
  case class Return(e: IASTExpression) extends Continuation
  case class Jump(target: String) extends Continuation
  case class CJump(c: IASTExpression, a: String, b: String) extends Continuation

  case class Block(label: String, stms: Array[IASTStatement], cnt: Continuation) {
    val successors = cnt match {
      case Return(_)    => Nil
      case Jump(b)      => List(b)
      case CJump(c,a,b) => List(a,b)
    }
  }

  class CFG (
    val entryLabel:  String,
    val blocks:      Array[Block],
    val blockIndex:  Map[String,Block],
    val loopHeaders: Set[String],
    val loopBodies:  Map[String,Set[String]],
    val postDom:     Map[String,Set[String]]
  ) {
    override def toString = s"""
    label: ${entryLabel}
    blocks: ${blocks mkString("\n\t", "\n\t", "\n")}
    blockIndex: ${blockIndex}
    loopHeaders: ${loopHeaders}
    loopBodies: ${loopBodies}
    postDominators: ${postDom}
    """
  }

}


trait CtoCFG extends CFGBase {

  // CFG builder state follows

  // state per function
  var curFunction: String = null
  var blocks: ArrayBuffer[Block] = new ArrayBuffer
  var blockIndex: mutable.HashMap[String,Block] = new mutable.HashMap

  // state per block
  var blockName: String = null
  var stms: ArrayBuffer[IASTStatement] = new ArrayBuffer


  var nBlocks = 0
  def freshLabel(s:String="") = try "b"+s+nBlocks finally nBlocks += 1

  def endBlock(cnt: Continuation) = {
    val b = Block(blockName,stms.toArray, cnt)
    blocks += b
    blockIndex(blockName) = b
    stms.clear
    println(s"New block: $b")
    blockName = null
  }
  def startBlock(s: String) = {
    blockName = s
    stms.clear
  }

  def fileToCFG(node: IASTTranslationUnit): Map[String,(Seq[String], CFG)] = node match {
    case node: CASTTranslationUnit =>
      var map = Map.empty[String,(Seq[String], CFG)]
      val decls = node.getDeclarations
      decls foreach {
        case d: CASTFunctionDefinition =>
          val name = d.getDeclarator.getName.toString
          val args = d.getDeclarator.asInstanceOf[CASTFunctionDeclarator].getParameters.map(_.getDeclarator.getName.toString)
          map += (name -> (args, funToCFG(d)))
        case _ => // ignore
      }
      map
  }

  def funToCFG(node: CASTFunctionDefinition): CFG  = {
    nBlocks = 0
    blocks.clear
    blockIndex.clear
    curFunction = node.getDeclarator.getName.toString

    val declarator = node.getDeclarator()
    val declSpecifier = node.getDeclSpecifier

    val entryLabel = freshLabel("Entry")
    startBlock(entryLabel)
    stmToCFG(node.getBody)
    endBlock(Return(null))

    val loopHeaders = new mutable.HashSet[String]
    val loopBodies = new mutable.HashMap[String,Set[String]]

    var seen = new mutable.HashSet[String]
    def dfs(l: String, path: List[String]): Unit = {
      if (path contains l) {
        loopHeaders += l
        // Note: may reach loop header on multiple paths
        // -> don't overwrite previous body nodes
        val bodyNodes = path.takeWhile(_ != l)
        val prev = loopBodies.getOrElseUpdate(l,Set())
        loopBodies(l) = (prev ++ bodyNodes)
      } else if (!seen(l)) {
        seen += l
        val path1 = l::path
        blockIndex(l).successors.foreach(l1 => dfs(l1, path1))
      }
    }
    dfs(entryLabel, Nil)

    def postDominators(blocks: List[Block]) = {
      var PostDom: Map[String,Set[String]] = Map()
      val labels = blocks.map(_.label).toSet
      val (exit,internal) = blocks.partition(_.successors.isEmpty)
      for (n <- exit)
        PostDom += (n.label -> Set(n.label))
      for (n <- internal)
        PostDom += (n.label -> labels)
      var p0 = PostDom
      do {
        p0 = PostDom
        for (n <- internal) {
          val x = (labels /: n.successors) ((a:Set[String],b:String) => a intersect PostDom(b))
          PostDom += (n.label -> (Set(n.label) ++ x))
        }
      } while (PostDom != p0)
      PostDom
    }
    val postDom = postDominators(blocks.toList)

    new CFG(entryLabel, blocks.toArray, Map.empty ++ blockIndex, Set.empty ++ loopHeaders, Map.empty ++ loopBodies, postDom)
  }


  var curLoopEnd: String = null
  var curLoopBegin: String = null
  def stmToCFG(node: IASTStatement): Unit = node match {
      case node: CASTCompoundStatement =>
          // TODO: push / pop scope
          //println("{")
          for (s <- node.getStatements) stmToCFG(s)
          //println("}")
      case node: CASTWhileStatement =>
          val c = node.getCondition
          val b = node.getBody
          val clabel = freshLabel("WhileHead")
          val blabel = freshLabel("WhileBody")
          val elabel = freshLabel("WhileExit")

          val save = curLoopEnd
          val save1 = curLoopBegin
          curLoopEnd = elabel
          curLoopBegin = clabel

          endBlock(Jump(clabel))
          startBlock(clabel)
          endBlock(CJump(c,blabel,elabel))
          startBlock(blabel)
          stmToCFG(b)
          endBlock(Jump(clabel))
          startBlock(elabel)

          curLoopEnd = save
          curLoopBegin = save1
      /*case node: CASTDoStatement =>
          val c = node.getCondition
          val b = node.getBody
          print("do ")
          stmToCFG(b)
          println("while "+evalExp(c))*/
      case node: CASTForStatement =>
          val c = node.getConditionExpression
          val i = node.getInitializerStatement
          val p = node.getIterationExpression
          val b = node.getBody
          val clabel = freshLabel("ForHead")
          val blabel = freshLabel("ForBody")
          val elabel = freshLabel("ForExit")

          val save = curLoopEnd
          val save1 = curLoopBegin
          curLoopEnd = elabel
          curLoopBegin = clabel

          stmToCFG(i)
          endBlock(Jump(clabel))
          startBlock(clabel)
          endBlock(CJump(c,blabel,elabel))
          startBlock(blabel)
          stmToCFG(b)
          if (p != null) stmToCFG(new CASTExpressionStatement(p.copy))
          endBlock(Jump(clabel))
          startBlock(elabel)

          curLoopEnd = save
          curLoopBegin = save1

      case node: CASTIfStatement =>
          val c = node.getConditionExpression
          val a = node.getThenClause
          val b = node.getElseClause
          val alabel = freshLabel("IfThen")
          val blabel = freshLabel("IfElse")
          val elabel = freshLabel("IfExit")
          endBlock(CJump(c,alabel,blabel))
          startBlock(alabel)
          stmToCFG(a)
          endBlock(Jump(elabel))
          startBlock(blabel)
          stmToCFG(b)
          endBlock(Jump(elabel))
          startBlock(elabel)
/*      case node: CASTSwitchStatement =>
          val c = node.getControllerExpression()
          val b = node.getBody
          println("switch "+evalExp(c))
          stmToCFG(b)
      case node: CASTCaseStatement =>
          println("case "+evalExp(node.getExpression)+":")
*/
      case node: CASTLabelStatement =>
          endBlock(Jump(node.getName.toString))
          startBlock(node.getName.toString)
          stmToCFG(node.getNestedStatement)
      case node: CASTGotoStatement =>
          endBlock(Jump(node.getName.toString))
          startBlock(freshLabel())
      case node: CASTBreakStatement =>
          println("break / TODO")
          endBlock(Jump(curLoopEnd))

      case node: CASTContinueStatement =>
          println("continue / TODO")
          endBlock(Jump(curLoopBegin))

      case node: CASTReturnStatement =>
          endBlock(Return(node.getReturnValue))
          startBlock(freshLabel())
      case node: CASTNullStatement =>
      case null =>
      case _ => stms += node
  }

}


trait CFGPrinter extends CPrinter with CFGBase {

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

    var fuel = 1*1000
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

      // strict post-dominators (without self, and without loop body)
      val sdom = postDom(l)-l -- loopBodies.getOrElse(l,Set())
      // immediate post-dominator (there can be at most one)
      var idom = sdom.filter(n => sdom.forall(postDom(n)))
      // the same, but may be inside loop body
      val sdomIn = postDom(l)-l
      // immediate post-dominator (may be inside loop)
      var idomIn = sdomIn.filter(n => sdomIn.forall(postDom(n)))


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
            assert(a == l || idom == Set(a), s"a=$a, l=$l, idom=$idom, pdom=${postDom(l)}") // handled below
          case CJump(c,a,b) =>
            println("if "+evalExp(c)+" {")
            consume(a, stop1, cont1)
            println("} else {")
            consume(b, stop1, cont1)
            println("}")
        }
      }

      // Some complication: the immediate post-dominator
      // of a loop header may be *inside* the loop.
      // Need to consume rest of loop body, too.
      val isLoop = loopHeaders contains l
      if (isLoop) {
        println("do {")
        println(s"bool ${l}_more = false")
        evalBody(idomIn, cont + l)
        if (idomIn.nonEmpty) // continue consuming loop body
          consume(idomIn.head, idom, cont + l)
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


object CFrontend2 extends CtoCFG with CFGPrinter {

  def evalCfgUnit(parsed: IASTTranslationUnit) = {
    val cfgs = fileToCFG(parsed)
    val (args, cfg) = cfgs("main")
    evalCFG(cfg)
  }
}

