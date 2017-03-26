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

  val trackValid = true

  val store0 = if (trackValid) GConst(Map(GConst("valid") -> GConst(1))) else GConst(Map())

  val itvec0 = IR.const("top")

  var store: Val = store0
  var itvec: Val = itvec0

  def evalType(node: IASTDeclSpecifier) = node match {
    case d: CASTSimpleDeclSpecifier     => CPrinter.types(d.getType)
    case d: CASTTypedefNameSpecifier    => d.getName
    case d: CASTElaboratedTypeSpecifier => d.getName // enough?
    case d: CASTCompositeTypeSpecifier  => d.getName // enough?
  }
  def evalExp(node: IASTNode): Val = node match {
      case node: CASTLiteralExpression =>
          val lk = node.getKind
          lk match {
            case 0 => /* int const */
              GConst(node.toString.toInt)
          }
      case node: CASTIdExpression =>
          val name = node.getName.toString
          IR.select(IR.select(store,IR.const("&"+name)), IR.const("val"))
      case node: CASTUnaryExpression =>
          val op = CPrinter.operators1(node.getOperator)
          val arg = node.getOperand
          op match {
            case "op_prefixIncr" => 
              val name = arg.asInstanceOf[CASTIdExpression].getName.toString // TODO: proper lval?
              val cur = IR.select(IR.select(store,IR.const("&"+name)), IR.const("val"))
              val upd = IR.plus(cur,IR.const(1))
              store = IR.update(store, IR.const("&"+name), IR.update(IR.const(Map()), IR.const("val"), upd))
              upd
          }
      case node: CASTBinaryExpression =>
          val op = CPrinter.operators2(node.getOperator)
          val arg1 = evalExp(node.getOperand1)
          val arg2 = evalExp(node.getOperand2)
          op match {
            case "op_equals" => IR.equal(arg1,arg2)
          }
      case node: CASTFunctionCallExpression =>
          val fun = node.getFunctionNameExpression
          val arg = node.getParameterExpression
          fun.asInstanceOf[CASTIdExpression].getName.toString match {
            case "assert" => 
              val c1 = evalExp(arg)
              val old = IR.select(store, IR.const("valid"))
              store = IR.update(store, IR.const("valid"), IR.times(old,c1)) // IR.times means IR.and
              IR.const(())
            //case _ => evalExp(fun)+"("+evalExp(arg)+")"
          }
      /*case node: CASTArraySubscriptExpression =>
          val a = node.getArrayExpression
          val x = node.getSubscriptExpression
          evalExp(a) + "["+ evalExp(x) + "]"
      case node: CASTExpressionList =>
          val as = node.getExpressions
          as.map(evalExp).mkString("(",",",")")
      case node: CASTInitializerList =>
          val as = node.getInitializers
          as.map(evalExp).mkString("{",",","}")
      case node: CASTEqualsInitializer => // copy initializer
          evalExp(node.getInitializerClause)
      case node: CASTCastExpression =>
          "("+CPrinter.types(node.getOperator)+")"+evalExp(node.getOperand)
      case node: CASTTypeIdExpression => // sizeof
          val op = CPrinter.type_ops(node.getOperator)
          val tp = node.getTypeId
          val declarator = tp.getAbstractDeclarator.asInstanceOf[CASTDeclarator]
          val declSpecifier = tp.getDeclSpecifier
          // TODO: pointer types, ...
          op + "("+evalType(declSpecifier)+")"*/
      case null => GConst(0)
      //case _ => "(exp "+node+")"
  }
  def evalDeclarator(node: IASTDeclarator): Unit = node match {
    case d1: CASTDeclarator =>
      val ptr = d1.getPointerOperators()
      // TODO: pointer types, ...
      val name = d1.getName
      /* val nested = d1.getNestedDeclarator // used at all?
      if (nested != null) {
        print("(")
        evalDeclarator(nested)
        print(")")
      }*/
      val init = d1.getInitializer
      if (init != null) {
        val init1 = init.asInstanceOf[CASTEqualsInitializer].getInitializerClause

        val v = evalExp(init1)
        store = IR.update(store, IR.const("&"+name), IR.update(IR.const(Map()), IR.const("val"), v))
      }
  }
  def evalLocalDecl(node: IASTDeclaration): Unit = node match {
      case node: CASTSimpleDeclaration =>
          val declSpecifier = node.getDeclSpecifier
          val decls = node.getDeclarators
          val tpe = (evalType(declSpecifier))
          //print(tpe+" ")
          for (d <- decls) {
            evalDeclarator(d)
          }
      case _ => 
  }
  def evalStm(node: IASTStatement): Unit = node match {
      case node: CASTCompoundStatement =>
          for (s <- node.getStatements) evalStm(s)
      case node: CASTDeclarationStatement =>
          val decl = node.getDeclaration
          evalLocalDecl(decl)
      case node: CASTExpressionStatement =>
          val exp = node.getExpression
          evalExp(exp)
      case node: CASTNullStatement =>
      case null => 
  }  

  def handleReturn(v: Val): Unit = {
    store = IR.update(store, IR.const("return"), v)
    //println("goto exit") TODO handle abort?
  }

  def handleContinue(l: String): Unit = {
    println("${l}_more = true")
  }

  def handleIf(c1: Val)(a: => Unit)(b: => Unit): Unit = {
    val save = store
    //assert(c1)
    val e1 = a
    val s1 = store
    store = save
    //assertNot(c1)
    val e2 = b
    val s2 = store
    store = IR.iff(c1,s1,s2)
    //IR.iff(c1,e1,e2)
  }

  def handleLoop(l:String)(body: => Unit): Unit = {
    println("do {") /*}*/
    println(s"bool ${l}_more = false")
    body
    println(s"} while (${l}_more)")
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
            handleIf(evalExp(c)) {
              consume(a, stop1, cont1)
            } {
              consume(b, stop1, cont1)
            }
        }
      }

      // Simplifying assumption: the immediate post-dominator
      // of a loop header is *outside* the loop. This is not
      // necessarily true in general.
      // TODO: refine to compute post-dom outside loop.
      val isLoop = loopHeaders contains l
      if (isLoop) {
        handleLoop(l) { evalBody(idom, cont + l) }
      } else {
        evalBody(idom, cont)
      }

      if (idom.nonEmpty)
        consume(idom.head, stop, cont)
    }
    time{consume(entryLabel, Set.empty, Set.empty)}

    val store2 = store
    println("## term:")
    val out = IR.termToString(store2)
    println(out)

  }

}
