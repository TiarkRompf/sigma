package analysis

import org.eclipse.cdt.core.dom.ast._
import org.eclipse.cdt.internal.core.dom.parser.c._

import CBase._
import CPrinter._
import Util._

object CFrontend2 {

  // CFG gen
  def resetCFG() = {
    nBlocks = 0
  }

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

  import scala.collection.{mutable,immutable}
  import mutable.ArrayBuffer

  
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
    blockName = null
  }
  def startBlock(s: String) = {
    blockName = s
    stms.clear
  }

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







  def evalCfgStm(node: IASTStatement): Unit = node match {
      case node: CASTCompoundStatement =>
          // TODO: push / pop scope
          //println("{")
          for (s <- node.getStatements) evalCfgStm(s)
          //println("}")
      case node: CASTWhileStatement =>
          val c = node.getCondition
          val b = node.getBody
          val clabel = freshLabel("WhileHead")
          val blabel = freshLabel("WhileBody")
          val elabel = freshLabel("WhileExit")
          endBlock(Jump(clabel))
          startBlock(clabel)
          endBlock(CJump(c,blabel,elabel))
          startBlock(blabel)
          evalCfgStm(b)
          endBlock(Jump(clabel))
          startBlock(elabel)
      /*case node: CASTDoStatement =>
          val c = node.getCondition
          val b = node.getBody
          print("do ")
          evalCfgStm(b)      
          println("while "+evalExp(c))*/
      case node: CASTForStatement =>
          val c = node.getConditionExpression
          val i = node.getInitializerStatement
          val p = node.getIterationExpression
          val b = node.getBody
          val clabel = freshLabel("ForHead")
          val blabel = freshLabel("ForBody")
          val elabel = freshLabel("ForExit")
          evalCfgStm(i)
          endBlock(Jump(clabel))
          startBlock(clabel)
          endBlock(CJump(c,blabel,elabel))
          startBlock(blabel)
          evalCfgStm(b)
          if (p != null) evalCfgStm(new CASTExpressionStatement(p.copy))
          endBlock(Jump(clabel))
          startBlock(elabel)

      case node: CASTIfStatement =>
          val c = node.getConditionExpression
          val a = node.getThenClause
          val b = node.getElseClause
          val alabel = freshLabel("IfThen")
          val blabel = freshLabel("IfElse")
          val elabel = freshLabel("IfExit")
          endBlock(CJump(c,alabel,blabel))
          startBlock(alabel)
          evalCfgStm(a)
          endBlock(Jump(elabel))
          startBlock(blabel)
          evalCfgStm(b)
          endBlock(Jump(elabel))
          startBlock(elabel)
/*      case node: CASTSwitchStatement =>
          val c = node.getControllerExpression()
          val b = node.getBody
          println("switch "+evalExp(c))
          evalCfgStm(b)
      case node: CASTCaseStatement =>
          println("case "+evalExp(node.getExpression)+":")
*/
      case node: CASTLabelStatement =>
          endBlock(Jump(node.getName.toString))
          startBlock(node.getName.toString)
          evalCfgStm(node.getNestedStatement)
      case node: CASTGotoStatement =>
          endBlock(Jump(node.getName.toString))
          startBlock(freshLabel())
/*      case node: CASTBreakStatement =>
          println("break / TODO")
      case node: CASTContinueStatement =>
          println("continue / TODO")
*/          
      case node: CASTReturnStatement =>
          endBlock(Return(node.getReturnValue))
          startBlock(freshLabel())
      case node: CASTNullStatement =>
      case null => 
      case _ => stms += node
  }
  def evalCfgGlobalDecl(node: IASTDeclaration): Unit = node match {
      case node: CASTFunctionDefinition =>
          nBlocks = 0
          blocks.clear
          blockIndex.clear
          curFunction = node.getDeclarator.getName.toString

          val declarator = node.getDeclarator()
          val declSpecifier = node.getDeclSpecifier
          print(evalType(declSpecifier))
          print(" ")
          evalDeclarator(declarator)

          if (curFunction != "main")
            return println("{ ... skipping body ... }")

          println(" {")
          println("# control-flow graph:")

          val entryLabel = freshLabel("Entry")
          startBlock(entryLabel)
          evalCfgStm(node.getBody)
          endBlock(Return(null))

          for (v <- blocks) {
            println(v.label+": {")
            v.stms.foreach(evalStm)
            println(v.cnt)
            println("}")
          }

          if (blocks.length > 200) {
            println(s"CFG too large: ${blocks.length} nodes")
          } else {
            println("# loop headers:")

            val loopHeaders = new mutable.HashSet[String]

            var fuel = 20000
            var seen = new mutable.HashSet[String]
            def dfs(l: String, path: Set[String]): Unit = {
              fuel -= 1; if (fuel == 0) throw new Exception("XXX dfs out of fuel")              
              if (path contains l) {
                loopHeaders += l
              } else if (!seen(l)) {
                seen += l
                val path1 = path + l
                blockIndex(l).successors.foreach(l1 => dfs(l1, path1))
              }
            }
            time {
              dfs(entryLabel, Set.empty)
              println(loopHeaders)
            }

            println("# post-dominators:")
            val postDom = time {
              val postDom = postDominators(blocks.toList)
              println(postDom)
              postDom
            }

            println("# restructure:")

            fuel = 500000
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

              // Simplifying assumption: the immediate post-dominator
              // of a loop header is *outside* the loop. This is not
              // necessarily true in general.
              // TODO: refine to compute post-dom outside loop.
              val isLoop = loopHeaders contains l
              if (isLoop) {
                println("do {")
                println(s"bool ${l}_more = false")
              }
              val stop1 = idom
              val cont1 = if (isLoop) cont + l else cont

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
              if (isLoop)
                println(s"} while (${l}_more)")

              if (idom.nonEmpty)
                consume(idom.head, stop, cont)
            }
            time{consume(entryLabel, Set.empty, Set.empty)}
          }

          println("}")
      case _ =>
          evalLocalDecl(node)
  }
  def evalCfgUnit(node: IASTTranslationUnit): Unit = node match {
      case node: CASTTranslationUnit =>
          val decls = node.getDeclarations
          for (d <- decls) evalCfgGlobalDecl(d)
  }


}