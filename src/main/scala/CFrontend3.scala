package analysis

import org.eclipse.cdt.core.dom.ast._
import org.eclipse.cdt.internal.core.dom.parser.c._

import scala.collection.{mutable,immutable}
import mutable.ArrayBuffer

import Util._
import Omega._

object CFGtoEngine {
  import CFGBase._
  import Test1._
  import Approx._
  val IR = IRD

  type Val = IR.From

  val value = GConst("$value")
  val tpe = GConst("$type")
  def typedGVal(x: Val, tp: Val) = IR.map(Map(value -> x, tpe -> tp))
  def gValValue(x: Val) = IR.select(x, value)
  def gValType(x: Val) = IR.select(x, tpe)


  val valid = GConst("valid")
  val rand = GRef("rand?")
  val store0 = GConst(Map(valid -> GConst(1))) // , rand -> rand))
  val constraints0 = List[OProb]()

  val itvec0 = IR.const("top")

  var store: Val = store0
  var itvec: Val = itvec0
  var constraints = constraints0

  def evalType(node: IASTDeclSpecifier) = node match {
    case d: CASTSimpleDeclSpecifier     => CPrinter.types(d.getType)
    case d: CASTTypedefNameSpecifier    => d.getName
    case d: CASTElaboratedTypeSpecifier => d.getName // enough?
    case d: CASTCompositeTypeSpecifier  => d.getName // enough?
  }

  def updateValid(check: Val) = {
    val oldValid = IR.select(store, valid)
    val newValid = IR.times(oldValid, check)
    if (debugF && newValid == GConst(0)) {
      println(s"Not valid anymore... $oldValid -- $check")
      ???
    }
    IR.update(store, valid, newValid)
  }

  def safeSelect(arg: Val, field: Val) = {
    debug("select", s"${IR.termToString(field)} from ${IR.termToString(arg)}")
    val check = IR.hasfield(arg, field)
    store = updateValid(check)

    IR.iff(check, IR.select(arg, field), GError)
  }

  def gValTypeCheck(arg: Val, tp: Val)(eval: Val => Val) = {
    val check = IR.times(IR.hasfield(arg, tpe), IR.equal(gValType(arg), tp))
    debug("TypeCheck", s"Type found: ${gValType(arg)}, expected: $tp")
    store = updateValid(check)

    IR.iff(check, eval(gValValue(arg)), GError)
  }

  def gValPointerTypeCheck(arg: Val)(eval: (Val, Val) => Val) = {
    val check = IR.times(IR.hasfield(arg, tpe), IR.const(if (gValType(arg) match { // FIXME
      case GConst(s: String) => s.endsWith(" *")
      case _ => false }) 1 else 0))

    store = updateValid(check)

    IR.iff(check, eval(gValValue(arg), gValType(arg) match {
      case GConst(s: String) => GConst(s.substring(0, s.length - 2))
      case _ => GError}), GError)
  }

  val location = new mutable.HashMap[Any,String]()
  val locNum =   new mutable.HashMap[String,Int]()
  def next(st: String) = { val idx = locNum.getOrElse(st, 0); locNum(st) = idx + 1; s"&$st:$idx" }
  def evalExp(node: IASTNode): Val = { /* println(s"NODE: $node"); */ node } match {
      case node: CASTLiteralExpression =>
          val lk = node.getKind
          lk match {
            case 0 => /* int const */
              // need to handle postfix like L, UL, ...
              val str = node.toString
              try {
              if (str.endsWith("UL"))
                typedGVal(GConst(str.substring(0,str.length-2).toInt), GType.int)// what do we do with long and unsigned long?
              else
                typedGVal(GConst(str.toInt), GType.int)
              } catch { case e: Exception =>
                println(str)
                println(str.endsWith("UL"))
                println(str.substring(0,str.length-2))
                throw e
              }
            case _ => ???
          }
      case node: CASTIdExpression =>
        val name = node.getName.toString
        // val idx = IR.pair(itvec, IR.const("&"+name))
        // val idx = IR.pair(IR.const("&"+name), itvec)
        val idx = IR.const("&" + name)
        debug("Variable", name)
        safeSelect(store, idx)
      case node: CASTUnaryExpression =>
          val op = CPrinter.operators1(node.getOperator)
          val arg = node.getOperand
          op match {
            case "op_bracketedPrimary" =>
              evalExp(arg) // OK?
            case "op_not" =>
              gValTypeCheck(evalExp(arg), GType.int) { x => typedGVal(IR.not(x), GType.int) }
            case "op_minus" =>
              gValTypeCheck(evalExp(arg), GType.int) { x => typedGVal(IR.times(IR.const(-1), x), GType.int) }
            case "op_prefixIncr" | "op_prefixDecr" =>
              val name = arg.asInstanceOf[CASTIdExpression].getName.toString // TODO: proper lval?
              val cur = safeSelect(store,IR.const("&"+name))
              val upd = gValTypeCheck(cur, GType.int) {
                cur => typedGVal(IR.plus(cur,IR.const(if (op.endsWith("Incr")) 1 else -1)), GType.int)
              }
              store = IR.update(store, IR.const("&"+name), upd) // update always safe?
              upd
            case "op_postFixIncr" | "op_postFixDecr" =>
              val name = arg.asInstanceOf[CASTIdExpression].getName.toString // TODO: proper lval?
              val cur = safeSelect(store,IR.const("&"+name))
              val upd = gValTypeCheck(cur, GType.int) {
                cur => typedGVal(IR.plus(cur,IR.const(if (op.endsWith("Incr")) 1 else -1)), GType.int)
              }
              store = IR.update(store, IR.const("&"+name), upd) // update always safe?
              cur
          }
      case node: CASTBinaryExpression =>
          val op = CPrinter.operators2(node.getOperator)
          lazy val arg1 = evalExp(node.getOperand1) // Dangerous for side effect...
          lazy val arg2 = evalExp(node.getOperand2)
          op match {
            case "op_plus" =>
              gValTypeCheck(arg1, GType.int) { arg1 => // FIXME: what about pointer operation?
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.plus(arg1,arg2), GType.int)
                }
              }
            case "op_minus" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.plus(arg1,IR.times(IR.const(-1),arg2)), GType.int)
                }
              }
            case "op_multiply" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.times(arg1,arg2), GType.int)
                }
              }
            case "op_divide" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  arg2 match {
                    case GConst(k: Int) =>
                      typedGVal(IR.times(arg1,IR.const(1.0/k)), GType.int)
                    case _ => ???
                  }
                }
              }

            case "op_equals" =>
              typedGVal(IR.equal(arg1,arg2), GType.int) // does Map == Map works?
            case "op_notequals" => typedGVal(IR.not(IR.equal(arg1,arg2)), GType.int)

            case "op_lessThan" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.less(arg1,arg2), GType.int)
                }
              }
            case "op_greaterThan" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.less(arg2,arg1), GType.int)
                }
              }
            case "op_lessEqual" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.less(arg1,IR.plus(arg2,IR.const(1))), GType.int) // OK
                }
              }
            case "op_greaterEqual" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.less(arg2,IR.plus(arg1,IR.const(1))), GType.int) // OK
                }
              }

            case "op_logicalAnd" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.iff(arg1,arg2,IR.const(0)), GType.int) // OK
                }
              }
            case "op_logicalOr" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.iff(arg1,IR.const(1),arg2), GType.int) // OK
                }
              }

            case "op_minusAssign" =>
              node.getOperand1 match {
                case id: CASTIdExpression =>
                  val name = id.getName.toString // TODO: proper lval?
                  debug("Assign", s"$name = ${IR.termToString(arg2)}")
                  // val idx = IR.pair(itvec, IR.const("&"+name))
                  // val idx = IR.pair(IR.const("&"+name), itvec)
                  val idx = IR.const("&" + name)
                  val cur = safeSelect(store,idx)
                  val upd = gValTypeCheck(cur, GType.int) { cur =>
                    gValTypeCheck(arg2, GType.int) { arg2 =>
                      typedGVal(IR.plus(cur,IR.times(arg2, IR.const(-1))), GType.int)
                    }
                  }
                  store = IR.update(store, idx, upd)
                  upd
              }

            case "op_plusAssign" =>
              node.getOperand1 match {
                case id: CASTIdExpression =>
                  val name = id.getName.toString // TODO: proper lval?
                  debug("Assign", s"$name = ${IR.termToString(arg2)}")
                  // val idx = IR.pair(itvec, IR.const("&"+name))
                  // val idx = IR.pair(IR.const("&"+name), itvec)
                  val idx = IR.const("&" + name)
                  val cur = safeSelect(store,idx)
                  val upd = gValTypeCheck(cur, GType.int) { cur =>
                    gValTypeCheck(arg2, GType.int) { arg2 =>
                      typedGVal(IR.plus(cur,arg2), GType.int)
                    }
                  }
                  store = IR.update(store, idx, upd)
                  upd
              }
            case "op_assign" =>
              node.getOperand1 match {
                case id: CASTIdExpression =>
                  val name = id.getName.toString // TODO: proper lval?
                  debug("Assign", s"$name = ${IR.termToString(arg2)}")
                  // val idx = IR.pair(itvec, IR.const("&"+name))
                  // val idx = IR.pair(IR.const("&"+name), itvec)
                  val idx = IR.const("&" + name)
                  val sarg2 = arg2 // side effect!!!!
                  store = IR.update(store, idx, sarg2)
                  sarg2
                // case array: CASTArraySubscriptExpression =>
                //   val name = array.getArrayExpression.asInstanceOf[CASTIdExpression].getName.toString // FIXME may not be static
                //   val x = array.getSubscriptExpression
                //   val ex = evalExp(x)
                //   val ref = IR.const("&"+name)
                //   gValPointerTypeCheck(safeSelect(store, ref)) { (arr, tp) =>
                //     gValTypeCheck(ex, GType.int) { ex =>
                //       gValTypeCheck(arg2, tp) { arg2 =>
                //         arr match {
                //           case IR.Def(DCollect(n, x, c)) =>
                //             store = updateValid(IR.times(IR.less(IR.const(-1), ex), IR.less(ex, n)))
                //             store = IR.update(store, ref, typedGVal(IR.collect(n, x, IR.iff(IR.equal(GRef(x), ex), arg2, c)), GType.pointer(tp.asInstanceOf[GConst]))) // FIXME
                //             GError
                //           case _ => GError // FIXME
                //         }
                //       }
                //     }
                //   }
                //   arg2
                //
                case node: CASTFieldReference if node.isPointerDereference() =>
                  val name = node.getFieldOwner.asInstanceOf[CASTIdExpression].getName.toString
                  val idx = IR.const("&"+name)
                  val pStruct = safeSelect(store, idx)
                  debug("Assign", s"B) pStruct: ${IR.termToString(pStruct)}")
                  gValTypeCheck(pStruct, GType.pointer(GConst("list"))) { pStruct =>
                    val struct = safeSelect(store, pStruct)
                    debug("Assign", s"B) struct: ${IR.termToString(struct)}")
                    gValTypeCheck(struct, GConst("list")) { struct =>
                      struct match {
                        case IR.Def(_: DPair) =>
                          store = IR.update(store, struct, arg2)
                        case _ => println(s"${IR.termToString(struct)}")
                          store = IR.update(store, pStruct, typedGVal(IR.update(struct, GConst(node.getFieldName.toString), arg2), GConst("list")))
                      }
                      arg2
                    }
                  }
                case node: CASTFieldReference =>
                  val name = node.getFieldOwner.asInstanceOf[CASTIdExpression].getName.toString
                  val idx = IR.const("&"+name)
                  val struct = safeSelect(store, idx)
                  gValTypeCheck(struct, GConst("list")) { struct =>
                    store = IR.update(store, idx, typedGVal(IR.update(struct, GConst(node.getFieldName.toString), arg2), GConst("list")))
                    arg2
                  }

              }
          }
      case node: CASTFunctionCallExpression =>
          val fun = node.getFunctionNameExpression
          val arg = node.getParameterExpression
          fun.asInstanceOf[CASTIdExpression].getName.toString match {
            case "__VERIFIER_nondet_int" =>
              val idx = IR.pair(GConst(location.getOrElseUpdate(node.hashCode, next("rand"))),itvec)
              typedGVal(IR.select(rand, idx), GType.int)
              // newV
            case "__VERIFIER_assume" =>
              constraints = assumeTrue(evalExp(arg))(constraints):::constraints
              println(s"Assume: constraints: ${constraints.mkString("\n\t", "\n\t", "\n")}")
              GError
            case "assert" | "__VERIFIER_assert" =>

              gValTypeCheck(evalExp(arg), GType.int) { arg =>
                  debug("Assert", IR.termToString(arg))
                  store = updateValid(arg)
                  typedGVal(IR.const(()), GType.void)
              }
            case "malloc" =>
              val newV = gValTypeCheck(evalExp(arg), GType.int) { arg =>
                typedGVal(IR.map(Map(GConst("value") -> typedGVal(GConst(0), GType.int), GConst("next") -> typedGVal(GConst(0), GType.pointer(GConst("list"))))), GConst("list"))
              }

              val idx = IR.pair(GConst(location.getOrElseUpdate(node.hashCode, next("new"))),itvec)
              store = IR.update(store, idx, newV)
              typedGVal(idx, GType.pointer(GConst("list")))
            case name =>
              println("ERROR: unknown function call: "+name)
              GConst("<call "+name+">")
            //case _ => evalExp(fun)+"("+evalExp(arg)+")"
          }
      case node: CASTArraySubscriptExpression =>
          val a = node.getArrayExpression
          val x = node.getSubscriptExpression
          val ea = evalExp(a)
          val ex = evalExp(x)
          // typedGVal(GConst(-1), GType.int)
          gValPointerTypeCheck(ea) { (ea, tpe) =>
            gValTypeCheck(ex, GType.int) { ex =>
              typedGVal(safeSelect(ea, ex), tpe)
            }
          }
      /* case node: CASTExpressionList =>
          val as = node.getExpressions
          as.map(evalExp).mkString("(",",",")")
      case node: CASTInitializerList =>
          val as = node.getInitializers
          as.map(evalExp).mkString("{",",","}")
      case node: CASTEqualsInitializer => // copy initializer
          evalExp(node.getInitializerClause)
          */
      case node: CASTCastExpression =>
        val op = node.getOperand
        val tp = node.getExpressionType
        val res = typedGVal(gValValue(evalExp(op)), GType(tp.toString))
        res

      case node: CASTTypeIdExpression => // sizeof
        val op = CPrinter.type_ops(node.getOperator)
        val tp = node.getTypeId
        val declarator = tp.getAbstractDeclarator.asInstanceOf[CASTDeclarator]
        val declSpecifier = tp.getDeclSpecifier

        typedGVal(GConst(2), GType.int)
      case node: CASTFieldReference if node.isPointerDereference() =>
        val pStruct = evalExp(node.getFieldOwner)
        debug("FieldRef", s"A) pStruct ${IR.termToString(pStruct)}")
        gValTypeCheck(pStruct, GType.pointer(GConst("list"))) { pStruct =>
          val struct = safeSelect(store, pStruct)
          debug("FieldRef", s"A) struct ${IR.termToString(struct)}")
          gValTypeCheck(struct, GConst("list")) { struct =>
            safeSelect(struct, GConst(node.getFieldName.toString))
          }
        }
      case node: CASTFieldReference =>
        val struct = evalExp(node.getFieldOwner)
        debug("FieldRef", s"D) struct (${node.isPointerDereference()}): ${IR.termToString(struct)}")
        gValTypeCheck(struct, GConst("list")) { struct =>
          safeSelect(struct, GConst(node.getFieldName.toString))
        }

      case null => typedGVal(GConst(0), GType.int)
      //case _ => "(exp "+node+")"
  }

  def makePtrType(n: Int, tp: GVal) = {
    (tp /: (0 until n)) { case (agg, _) => GType.pointer(agg.asInstanceOf[GConst]) } // FIXME
  }

  def evalDeclarator(node: IASTDeclarator): Unit = node match {
    case d1: CASTArrayDeclarator => println(s"Array"); ???
    case d1: CASTFieldDeclarator => println(s"Field"); ???
    case d1: CASTFunctionDeclarator => println(s"Function"); ???
    case d1: CASTKnRFunctionDeclarator => println(s"Function KnR"); ???
    case d1: CASTDeclarator =>
     val ptr = d1.getPointerOperators()
     // TODO: pointer types, ...
     val name = d1.getName
     val nested = d1.getNestedDeclarator // used at all?
     val init = d1.getInitializer
     debug("Declarator", s"""decl: ${ptr.length} - ${ptr map(_.getSyntax) mkString ","} - $name: init value $init""")
     if (init != null) {
       val init1 = init.asInstanceOf[CASTEqualsInitializer].getInitializerClause

       val v = evalExp(init1)
       val idx = IR.pair(itvec, IR.const("&"+name))
       // val idx = IR.pair(IR.const("&"+name), itvec)
       store = IR.update(store, IR.const("&"+name), v)
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
      case _ => ???
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
      case node: CASTProblemStatement => // FIXME
      case null =>
  }

  def handleReturn(v: Val): Unit = {
    store = IR.update(store, IR.const("return"), v)
    //println("goto exit") TODO handle abort?
  }

  def handleContinue(l: String): Unit = {
    //println("${l}_more = true")
    val more = l+"_more"
    store = IR.update(store, IR.const(more), GConst(1))
  }

  def handleIf(c1: Val)(a: => Unit)(b: => Unit): Unit = {
    println(s"if condition: ${IR.termToString(c1)}")

    val save = store
    val save1 = constraints
    //assert(c1)
    println(s"store before then >> ${IR.termToString(store)}")
    if (IR.select(c1, value) != GConst(0))
      constraints = assumeTrue(c1)(save1):::save1
    val e1 = a
    val s1 = simplify(store)(constraints)
    println(s"store after then >> ${IR.termToString(s1)}\nunder: ${constraints.mkString("\n\t- ", "\n\t- ", "\n")}")
    //assertNot(c1)
    if (IR.select(c1, value) != GConst(1))
      constraints = assumeTrue(IR.not(c1))(save1):::save1
    store = save
    println(s"\nstore before else >> ${IR.termToString(store)}")
    val e2 = b
    val s2 = simplify(store)(constraints)
    println(s"store after else >> ${IR.termToString(s2)}\nunder: ${constraints.mkString("\n\t- ", "\n\t- ", "\n")}")
    store = gValTypeCheck(c1, GType.int) { c1 =>
      IR.iff(c1,s1,s2)
    }
    constraints = save1
    //IR.iff(c1,e1,e2)
  }

  def printList(seq: List[Val]) = println(seq map("\t" + IR.termToString(_)) mkString("\n"))

  def toOStruct(term: Val): Option[OStruct] = try {
    Some(translateBoolExpr(term))
  } catch {
    case _: NotImplementedError => None
  }

  def toOProb(term: Val): Option[OProb] = toOStruct(term) match {
    case Some(op@OProb(_)) => Some(op)
    case _ => None
  }

  def alwaysFalse(cond: Val)(implicit constraints: List[OProb]) = { toOStruct(cond) } match {
    case Some(cond) => !verify(cond, constraints)
    case _ => false
  }

  def assumeTrue(cond: Val)(implicit constraints: List[OProb]): List[OProb] = cond match {
    case GConst(0) => println("False can not be assumed true"); ???
    // case _ if alwaysFalse(cond) => println("False can not be assumed true"); ???
    case GConst(1) => Nil
    case IR.Def(DIf(c, a, b)) if alwaysFalse(b)(toOProb(IR.not(c)) ++: constraints) => toOProb(c) ++: assumeTrue(a)
    case IR.Def(DIf(c, a, b)) if alwaysFalse(a)(toOProb(c) ++: constraints) => toOProb(IR.not(c)) ++: assumeTrue(b)
    case IR.Def(DIf(c, a, b)) if alwaysFalse(c) => assumeTrue(b)
    case IR.Def(DIf(c, a, b)) if simplifyBool(b)(toOProb(c) ++: constraints) == a => assumeTrue(b) // Generalize
    case IR.Def(DIf(c, a, b)) if alwaysFalse(IR.not(c)) => assumeTrue(a)
    case IR.Def(DMap(m)) => m.get(GConst("$value")).fold(toOProb(cond).toList)(assumeTrue(_))
    // case IR.Def(DNot(IR.Def(DEqual(a, b)))) => assumeTrue(IR.less(b, a)) // HACK... may be false
    case IR.Def(DNot(IR.Def(DEqual(a, b)))) =>
      val x = IR.less(a, b)
      val y = IR.less(b, a)
      val xAF = alwaysFalse(x)
      val yAF = alwaysFalse(y)

      (xAF,yAF) match {
        case (true, false) => toOProb(y).toList
        case (false, true) => toOProb(x).toList
        case (true, true) => ???
        case (false, false) => println(s"Can't extract information from this situation"); Nil
      }
    case IR.Def(DTimes(a, b)) => assumeTrue(a) ++ assumeTrue(b)
    case a@_ => println(s"Nothing has been simplified for ${IR.termToString(a)}"); toOProb(a).toList
  }

  def simplifyBool(term: Val)(implicit constraints: List[OProb]): Val = term match {
    case GConst(0) => IR.const(0)
    case GConst(_: Int) => IR.const(1)
    case GConst(_) => term
    case IR.Def(DTimes(x, y)) =>
      val sx = simplifyBool(x)
      val sy = simplifyBool(y)
      if (sx == sy)
        sx
      else
        IR.times(sx, sy)
    case _ if alwaysFalse(term) => IR.const(0)
    case _ if alwaysFalse(IR.not(term)) => IR.const(1)
    case IR.Def(DIf(c, GConst(1), GConst(0))) => simplifyBool(c)          // can generalize with alwaysFalse...
    case IR.Def(DIf(c, GConst(0), GConst(1))) => simplifyBool(IR.not(c))
    case IR.Def(DIf(c, a, b)) =>
      val sc = simplifyBool(c)
      if (alwaysFalse(sc))
        simplifyBool(b)(toOProb(IR.not(sc)) ++: constraints)
      else if (alwaysFalse(IR.not(sc)))
        simplifyBool(a)(toOProb(sc) ++: constraints)
      else {
        // IR.iff(sc, simplify(a)(toOProb(sc) ++: constraints), simplify(b)(toOProb(IR.not(sc)) ++: constraints))
        val t = simplifyBool(a)(toOProb(sc) ++: constraints)
        val e = simplifyBool(b)(toOProb(IR.not(sc)) ++: constraints)
        // if (alwaysFalse(IR.not(t))(toOProb(sc) ++: constraints) && alwaysFalse(e)(toOProb(IR.not(sc)) ++: constraints)) {
        //   println(s"${IR.termToString(t)} -- ${IR.termToString(e)}"); sc
        // } else if (alwaysFalse(t)(toOProb(sc) ++: constraints) && alwaysFalse(IR.not(e))(toOProb(IR.not(sc)) ++: constraints)) {
        //   println(s"${IR.termToString(t)} -- ${IR.termToString(e)}"); ??? // IR.not(sc)
        // } else
          IR.iff(sc, t, e)
      }
    case IR.Def(DLess(x, y))  =>
      val t = IR.less(simplify(x), simplify(y))
      val res = if (alwaysFalse(t))
        IR.const(0)
      else if (alwaysFalse(IR.not(t)))
        IR.const(1)
      else
        t
      res
    case IR.Def(DEqual(x, y)) => IR.equal(simplify(x), simplify(y))
    case IR.Def(DNot(x))      => IR.not(simplifyBool(x))
    case _ => term
  }

  def simplify(term: Val)(implicit constraints: List[OProb]): Val = { debug("Simplify", s"${IR.termToString(term)} - contraints: $constraints"); term } match {
    case IR.Def(DIf(c, a, b)) =>
      val sc = simplifyBool(c)

      if (alwaysFalse(sc))
        simplify(b)(toOProb(IR.not(sc)) ++: constraints)
      else if (alwaysFalse(IR.not(sc)))
        simplify(a)(toOProb(sc) ++: constraints)
      else if (alwaysFalse(IR.not(IR.equal(a, b)))) {
        println(s"${IR.termToString(a)} -- ${IR.termToString(b)}")
        simplify(a)
      } else {
        // FIXME: working on that
        // How to make it better?
        val sa = simplify(a)(toOProb(IR.not(sc)) ++: constraints)
        if (sa == b) {
          simplify(a)(constraints) // Not sure adding sc == 1 is correct (toOProb(sc) ++: constraints)
        } else {
          val sb = simplify(b)(toOProb(sc) ++: constraints)
          if (sb == a) {
            simplify(b)(constraints)
          } else {
            val na = simplify(a)(toOProb(sc) ++: constraints)
            val nb = simplify(b)(toOProb(IR.not(sc)) ++: constraints)
            if (alwaysFalse(IR.not(IR.equal(na, nb))))
              na
            else
              IR.iff(sc, na, nb)
          }
        }
      }
    case IR.Def(DFixIndex(x, c)) => IR.fixindex(x, simplifyBool(c))
    case IR.Def(DMap(m)) =>
      def isBool(key: Val) = {
        (key == valid) // || s"$key".endsWith("_more\"")
      }
      IR.map(m map { case (key, value) =>
        // if (!key.toString.startsWith("\"$")) println(s"Simplify key $key -> ${IR.termToString(value)}:")
        key -> (if (isBool(key)) simplifyBool(value) else simplify(value))
      }) // FIXME ???
    case IR.Def(DUpdate(x, f, y))  => IR.update(simplify(x), simplify(f), simplify(y))
    case r@IR.Def(DSelect(x@GRef("rand?"), f)) =>
        IR.select(x, simplify(f))
    case IR.Def(DSelect(x, f))     => IR.select(simplify(x), simplify(f))
    // (x26? * rand?((&rand:1,top))) + (x26? * (rand?((&rand:0,top)) * -1))
    case IR.Def(DPlus(IR.Def(DTimes(a, b)), IR.Def(DTimes(a1, IR.Def(DTimes(b1, k: GConst)))))) if a == a1 && alwaysFalse(IR.not(IR.equal(b, b1))) => IR.times(a, IR.times(b, IR.plus(IR.const(1), k)))
    // (x26? * a1) + ((x26? * (a0 * -1)) + 1)
    case IR.Def(DPlus(IR.Def(DTimes(a, b)), IR.Def(DPlus(IR.Def(DTimes(a1, IR.Def(DTimes(b1, k: GConst)))), d)))) if a == a1 && alwaysFalse(IR.not(IR.equal(b, b1))) => IR.plus(IR.times(a, IR.times(b, IR.plus(IR.const(1), k))), d)
    // ((x15? * (a0 * a0)) + ((x15? * (a0 * (a1 * -1))) + 1)))
    case IR.Def(DPlus(IR.Def(DTimes(k1, IR.Def(DTimes(a1, a2)))), IR.Def(DPlus(IR.Def(DTimes(k2, IR.Def(DTimes(a3, IR.Def(DTimes(a4, k3)))))), d))))
    if k1 == k2 && alwaysFalse(IR.not(IR.equal(a1, a2))) && alwaysFalse(IR.not(IR.equal(a2, a3))) && alwaysFalse(IR.not(IR.equal(a3, a4))) => IR.plus(IR.times(IR.times(IR.const(1), k3), IR.times(k1, IR.times(a1, a2))), d)
    // (a0 * a0) + ((x15? * (a0 * -2)) + ((a0 * (a1 * -1)) + (x15? * (a1 * 2))))
    case IR.Def(DPlus(a, IR.Def(DPlus(IR.Def(DTimes(c1, IR.Def(DTimes(a3, k1)))), IR.Def(DPlus(b, IR.Def(DTimes(c2, IR.Def(DTimes(a4, k2))))))))))
    if c1 == c2 && alwaysFalse(IR.not(IR.equal(a3, a4))) => IR.plus(IR.times(c1, IR.times(a3, IR.plus(k1, k2))), IR.plus(a, b))
    case IR.Def(DPlus(x, y))       => IR.plus(simplify(x), simplify(y))
    case IR.Def(DTimes(x, y))      => IR.times(simplify(x), simplify(y))
    case IR.Def(DPair(x, y))       => IR.pair(simplify(x), simplify(y))
    case IR.Def(DLess(x, y))       => simplifyBool(term)
    case IR.Def(DEqual(x, y))      => simplifyBool(term)
    case IR.Def(DNot(x))           => simplifyBool(term)
    case IR.Def(DSum(n, x, c))     => IR.sum(simplify(n), x, c) // simplify(c))
    case IR.Def(DCollect(n, x, c)) => IR.collect(simplify(n), x, simplify(c)) // (toOProb(IR.not(IR.less(GRef(x), 0))) ++: constraints))
    case IR.Def(DCall(f, x))       => IR.call(simplify(f), simplify(x))
    case IR.Def(DFun(f, x, y))     => IR.fun(f, x, simplify(y))
    case IR.Def(DHasField(x, f))   => IR.hasfield(simplify(x), simplify(f))
    case x@GRef(_) =>
      if (alwaysFalse(IR.not(IR.equal(x, IR.const(0))))) { // FIXME: hack if GRef(x) == 0
        println(s"Simplifed $x to 0"); IR.const(0)
      } else {
        x
      }
    case _ => term
  }

  def handleLoop(l:String)(body: => Unit): Unit = {
    import IR._
    val saveit = itvec
    val save = constraints

    val loop = GRef(freshVar)
    val n0 = GRef(freshVar + "?")

    val before = store

    itvec = pair(itvec,n0)

    println(s"\n\n\nbegin loop f(n)=$loop($n0), iteration vector $itvec {")

    println(s"initial assumption: f(0)=$before, f($n0)=$before, f($n0+1)=$before")

    var init = before
    var path = Nil: List[GVal]

    var iterCount = 0
    def iter: GVal = {
      if (iterCount > 3) { println("XXX ABORT XXX"); return GConst(0) }
      println(s"## iteration $iterCount, f(0)=$before, f($n0)=$init")
      assert(!path.contains(init), "hitting recursion: "+(init::path))
      path = init::path
      constraints = toOProb(not(less(n0, const(0)))) ++: save

      store = init // simplify(init)(save)
      println(s"Init before loop: ${IR.termToString(store)}")

      // s"bool ${l}_more = false"
      val more = l+"_more"
      store = IR.update(store, IR.const(more), GConst(0))

      println(s"==== eval body $loop ($n0) ====")
      body // eval loop body ...
      println("===========================")

      println("Compute constraints:")
      constraints = constraints ++ toOProb(not(less(n0,const(0)))).toList

      println(s"$more: ${IR.termToString(IR.select(store,IR.const(more)))}")
      val cv = simplifyBool(IR.select(store,IR.const(more)))(constraints)

      println(s"cv: $n0 -- ${IR.termToString(cv)}")

      constraints ++= toOProb(simplify(not(less(fixindex(n0.toString, cv),n0)))(constraints))

      // FIXME: is it still necessary? Should be handle by simplification step.
      // store = subst(store,less(fixindex(n0.toString, cv),n0),const(0)) // i <= n-1
      // store = subst(store,less(n0,const(0)),const(0)) // 0 <= i

      println(s"Store after iter: ${IR.termToString(store)}")
      // store = simplify(store)(constraints)
      // println(s"Store after simplifications: ${IR.termToString(store)}")

      println("trip count: "+termToString(simplify(fixindex(n0.toString, cv))(constraints)))
      if (cv == GConst(0)) {
        println("\n\n\t\tno more....???\n\n")
        itvec = saveit
        constraints = save
        return IR.const(())
      }


      val afterB = store

      // inside the loop we know the check succeeded.
      // val next = subst(afterB,cv,const(1))

      val trueClauses = assumeTrue(cv)(constraints)
      println(s"TrueClauses:\n\t${trueClauses.mkString("\n", "\t\n", "\n")}")

      // FIXME: may be useful for complex form
      // var next = (afterB /: trueClauses) {
      //   case (agg, t) => subst(subst(agg, t, const(1)), not(t), const(0))
      // }

      constraints = trueClauses:::constraints
      val next = simplify(afterB)(constraints)
      println(s"Store after simplifications: ${IR.termToString(next)}")
      println(s"Under the constraints: ${constraints.mkString("\n\t- ", "\n\t- ", "\n")}")
      println(s"Before the loop: ${save.mkString("\n\t- ", "\n\t- ", "\n")}")

      // generalize init/next based on previous values
      // and current observation
      println(s"approx f(0)=$before, f($n0)=$init, f($n0+1)=$next) = {")

      val sBefore = simplify(before)(constraints)
      val sInit   = simplify(init)(constraints)
      println("\n**********************************")
      println(s"Before :\n${IR.termToString(sBefore)}")
      println(s"Init :\n${IR.termToString(sInit)}")
      println(s"Next :\n${IR.termToString(next)}")
      println("**********************************\n")

      val (initNew,nextNew) = lub(sBefore, sInit, next)(loop,n0)
      println("\n**********************************")
      println(s"Init new:\n${IR.termToString(initNew)}")
      // println(s"Init new:\n${IR.termToString(simplify(initNew)(constraints))}")
      println(s"Next new:\n${IR.termToString(nextNew)}")
      // println(s"Next new:\n${IR.termToString(simplify(nextNew)(constraints))}")
      println("**********************************\n")

      println(s"} -> f($n0)=$initNew, f($n0+1)=$nextNew")

      // are we done or do we need another iteration?
      if (init != initNew) {
        init = initNew; iterCount += 1;
        println("==========================\n")
        iter
      } else {
        // no further information was gained: go ahead
        // and generate the final (set of) recursive
        // functions, or closed forms.
        println(s"create function def f(n) = $loop($n0) {")

        // given f(n+1) = nextNew, derive formula for f(n)
        val body = iff(less(const(0),n0),
                      subst(nextNew,n0,plus(n0,const(-1))),
                      before)

        // create function definition, which we call below
        lubfun(loop,n0,body)

        println("}")

        // compute trip count
        val nX = fixindex(n0.toString, cv)

        // invoke computed function at trip count
        val tmp = call(loop,nX)
        println(s"Store non simplified loop $loop: ${IR.termToString(tmp)}")
        store = simplify(tmp)(save)

        // wrap up
        println(s"} end loop $loop, trip count ${IR.termToString(nX)}, state")

        println(s"Constraints: ${constraints.mkString("\n\t", "\n\t", "\n")}")

        println(s"Simplified store: ${IR.termToString(store)}")
        itvec = saveit
        println(s"======= Iteration $loop Done =======\n\n\n\n")
        constraints = save
        IR.const(())
      }
    }

    iter
  }

  def evalCFG(cfg: CFG): GVal = {
    import cfg._
    val blockIndex = cfg.blockIndex

    // global reset ...
    store = store0
    itvec = itvec0
    constraints = constraints0
    varCount = varCount0
    globalDefs = globalDefs0
    rebuildGlobalDefsCache()

    var fuel = 1*1000
    def consume(l: String, stop: Set[String], cont: Set[String]): Unit = {
      fuel -= 1; if (fuel == 0) {
        println(l,stop,cont,postDom(l))
        throw new Exception("XXX consume out of fuel")
      }

      debug("consume", s"label $l -- stop: $stop -- cont: $cont")

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

      // strict post-dominators (without self, and without loop body)
      val sdom = postDom(l)-l -- loopBodies.getOrElse(l,Set())
      // immediate post-dominator (there can be at most one)
      var idom = sdom.filter(n => sdom.forall(postDom(n)))
      // the same, but may be inside loop body
      val sdomIn = postDom(l)-l
      // immediate post-dominator (may be inside loop)
      var idomIn = sdomIn.filter(n => sdomIn.forall(postDom(n)))
      debug("consume", s"sdom: $sdom -- idom: $idom -- sdomIn: $sdomIn -- idomIn: $idomIn")

      // Currently there's an issue in
      // loop-invgen/string_concat-noarr_true-unreach-call_true-termination.i
      // TODO: use Cooper's algorithm to compute idom directly
      if (idom.contains("STUCK")) idom = Set("STUCK") // HACK
      if (l == "STUCK") idom = Set() // HACK
      assert(idom.size <= 1, s"sdom($l) = $sdom\nidom($l) = ${idom}")


      def evalBody(stop1: Set[String], cont1: Set[String]): Unit = {
        debug("consume", s"eval body (${b.stms.length})")
        b.stms.foreach { stm =>
          evalStm(stm)
        }
        debug("consume", s"continue to ${b.cnt}")
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

      // Some complication: the immediate post-dominator
      // of a loop header may be *inside* the loop.
      // Need to consume rest of loop body, too.
      val isLoop = loopHeaders contains l
      if (isLoop) {
        debug("consume", "It is a loop!")
        handleLoop(l) {
          evalBody(idomIn, cont + l)
          if (idomIn.nonEmpty) // continue consuming loop body
            consume(idomIn.head, idom, cont + l)
        }
      } else {
        debug("consume", "Not a loop!")
        evalBody(idom, cont)
      }


      if (idom.nonEmpty)
        consume(idom.head, stop, cont)
    }

    time{consume(entryLabel, Set.empty, Set.empty)}

    println(s"Final store: ${IR.termToString(store)}")
    println(s"Constraints: ${constraints.mkString("\n\t", "\n\t", "\n")}")
    var store2 = simplify(store)(constraints)
    var go = true
    while (go) {
      val ns = simplify(store2)(constraints)
      go = ns != store2
      store2 = ns
    }
    println("## term:")
    val out = IR.termToString(store2)
    println(out)
    store2
  }

}
