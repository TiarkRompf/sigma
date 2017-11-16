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
  val store0 = GConst(Map(valid -> GConst(1)))

  val itvec0 = IR.const("top")

  var store: Val = store0
  var itvec: Val = itvec0

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
      debug(s"Not valid anymore...")
      ???
    }
    IR.update(store, valid, newValid)
  }

  def safeSelect(arg: Val, field: Val) = {
    debug(s"select ${IR.termToString(field)} from ${IR.termToString(arg)}")
    val check = IR.hasfield(arg, field)
    store = updateValid(check)

    IR.iff(check, IR.select(arg, field), GError)
  }

  def gValTypeCheck(arg: Val, tp: Val)(eval: Val => Val) = {
    val check = IR.times(IR.hasfield(arg, tpe), IR.equal(gValType(arg), tp))
    debug(s"Type found: ${gValType(arg)}, expected: $tp")
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
  var nextV = 0
  def next = { nextV += 1; s"&new:$nextV" }
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
        debug(s"Variable: $name")
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
            case "op_prefixIncr" =>
              val name = arg.asInstanceOf[CASTIdExpression].getName.toString // TODO: proper lval?
              val cur = safeSelect(store,IR.const("&"+name))
              val upd = gValTypeCheck(cur, GType.int) {
                cur => typedGVal(IR.plus(cur,IR.const(1)), GType.int)
              }
              store = IR.update(store, IR.const("&"+name), upd) // update always safe?
              upd
            case "op_postFixIncr" =>
              val name = arg.asInstanceOf[CASTIdExpression].getName.toString // TODO: proper lval?
              val cur = safeSelect(store,IR.const("&"+name))
              val upd = gValTypeCheck(cur, GType.int) {
                cur => typedGVal(IR.plus(cur,IR.const(1)), GType.int)
              }
              store = IR.update(store, IR.const("&"+name), upd) // update always safe?
              cur
          }
      case node: CASTBinaryExpression =>
          val op = CPrinter.operators2(node.getOperator)
          val arg1 = evalExp(node.getOperand1)
          val arg2 = evalExp(node.getOperand2)
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
            case "op_equals" =>
              typedGVal(IR.equal(arg1,arg2), GType.int) // does Map == Map works?
            case "op_notequals" => typedGVal(IR.not(IR.equal(arg1,arg2)), GType.int)

            case "op_lessThan" =>
              gValTypeCheck(arg1, GType.int) { arg1 =>
                gValTypeCheck(arg2, GType.int) { arg2 =>
                  typedGVal(IR.less(arg1,arg2), GType.int)
                }
              }
            case "op_greaterEqual" =>
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
            case "op_greaterThan" =>
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


            case "op_assign" =>
              node.getOperand1 match {
                case id: CASTIdExpression =>
                  val name = id.getName.toString // TODO: proper lval?
                  debug(s"Assign: $name = ${IR.termToString(arg2)}")
                  // val idx = IR.pair(itvec, IR.const("&"+name))
                  // val idx = IR.pair(IR.const("&"+name), itvec)
                  val idx = IR.const("&" + name)
                  store = IR.update(store, idx, arg2)
                  arg2
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
                  debug(s"B) pStruct: ${IR.termToString(pStruct)}")
                  gValTypeCheck(pStruct, GType.pointer(GConst("list"))) { pStruct =>
                    val struct = safeSelect(store, pStruct)
                    debug(s"B) struct: ${IR.termToString(struct)}")
                    gValTypeCheck(struct, GConst("list")) { struct =>
                      store = IR.update(store, pStruct, typedGVal(IR.update(struct, GConst(node.getFieldName.toString), arg2), GConst("list")))
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
            case "__VERIFIER_nondet_int" => typedGVal(GRef(freshVar + "?"), GType.int)
            case "assert" | "__VERIFIER_assert" =>
              gValTypeCheck(evalExp(arg), GType.int) { arg =>
                  debug(s"Assert: ${IR.termToString(arg)}")
                  store = updateValid(arg)
                  typedGVal(IR.const(()), GType.void)
              }
            case "malloc" =>
              val newV = gValTypeCheck(evalExp(arg), GType.int) { arg =>
                typedGVal(IR.map(Map(GConst("value") -> typedGVal(GConst(0), GType.int), GConst("next") -> typedGVal(GConst(0), GType.pointer(GConst("list"))))), GConst("list"))
              }

              val idx = IR.pair(GConst(location.getOrElseUpdate(node.hashCode, next)),itvec)
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
        debug(s"A) pStruct ${IR.termToString(pStruct)}")
        gValTypeCheck(pStruct, GType.pointer(GConst("list"))) { pStruct =>
          val struct = safeSelect(store, pStruct)
          debug(s"A) struct ${IR.termToString(struct)}")
          gValTypeCheck(struct, GConst("list")) { struct =>
            safeSelect(struct, GConst(node.getFieldName.toString))
          }
        }
      case node: CASTFieldReference =>
        val struct = evalExp(node.getFieldOwner)
        debug(s"D) struct (${node.isPointerDereference()}): ${IR.termToString(struct)}")
        gValTypeCheck(struct, GConst("list")) { struct =>
          safeSelect(struct, GConst(node.getFieldName.toString))
        }

      // case null => typedGVal(GConst(0), GType.int)
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
     debug(s"""decl: ${ptr.length} - ${ptr map(_.getSyntax) mkString ","} - $name""")
     val nested = d1.getNestedDeclarator // used at all?
     val init = d1.getInitializer
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
    val save = store
    //assert(c1)
    val e1 = a
    val s1 = store
    store = save
    //assertNot(c1)
    val e2 = b
    val s2 = store
    store = gValTypeCheck(c1, GType.int) { c1 =>
      IR.iff(c1,s1,s2)
    }
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

  def alwaysFalse(cond: Val)(implicit constraints: List[OProb]) = toOStruct(cond) match {
    case Some(cond) => !verify(cond, constraints)
    case _ => false
  }

  def assumeTrue(cond: Val)(implicit constraints: List[OProb]): List[Val] = cond match {
    case GConst(0) => println("False can not be assumed true"); ???
    // case _ if alwaysFalse(cond) => println("False can not be assumed true"); ???
    case GConst(1) => Nil
    case IR.Def(DIf(c, a, b)) if alwaysFalse(b)(toOProb(IR.not(c)) ++: constraints) => c :: assumeTrue(a)
    case IR.Def(DIf(c, a, b)) if alwaysFalse(a)(toOProb(c) ++: constraints) => IR.not(c) :: assumeTrue(b)
    case IR.Def(DIf(c, a, b)) if alwaysFalse(c) => assumeTrue(b)
    case IR.Def(DIf(c, a, b)) if alwaysFalse(IR.not(c)) => assumeTrue(a)
    case a@_ => println(s"Nothing as been simplified: ${IR.termToString(a)}"); List(a)
  }

  def simplifyBool(term: Val)(implicit constraints: List[OProb]): Val = term match {
    case GConst(0) => IR.const(0)
    case GConst(_: Int) => IR.const(1)
    case IR.Def(DTimes(x, y)) =>
      val sx = simplifyBool(x)
      val sy = simplifyBool(y)
      if (sx == sy)
        sx
      else
        IR.times(sx, sy)
    case _ if alwaysFalse(term) => IR.const(0)
    case _ if alwaysFalse(IR.not(term)) => IR.const(1)
    case IR.Def(DIf(c, a, b)) =>
      val sc = simplify(c)
      if (alwaysFalse(sc))
        simplify(b)(toOProb(IR.not(sc)) ++: constraints)
      else if (alwaysFalse(IR.not(sc)))
        simplify(a)(toOProb(sc) ++: constraints)
      else
        IR.iff(sc, simplify(a)(toOProb(sc) ++: constraints), simplify(b)(toOProb(IR.not(sc)) ++: constraints))
    case _ => term
  }

  def simplify(term: Val)(implicit constraints: List[OProb]): Val = { debug(s"> ${IR.termToString(term)} - contraints: $constraints"); term } match {
    case IR.Def(DIf(c, a, b)) =>
      val sc = simplify(c)
      if (alwaysFalse(sc))
        simplify(b)(toOProb(IR.not(sc)) ++: constraints)
      else if (alwaysFalse(IR.not(sc)))
        simplify(a)(toOProb(sc) ++: constraints)
      else
        IR.iff(sc, simplify(a)(toOProb(sc) ++: constraints), simplify(b)(toOProb(IR.not(sc)) ++: constraints))
    case IR.Def(DIf(c, a, b)) if alwaysFalse(IR.not(c)) => simplify(a)
    case IR.Def(DFixIndex(x, c)) => IR.fixindex(x, simplify(c))
    case IR.Def(DMap(m)) =>
      IR.map(m map { case (key, value) =>
        // if (!key.toString.startsWith("\"$")) println(s"Simplify key $key -> ${IR.termToString(value)}:")
      simplify(key) -> (if (key == valid) simplifyBool(value) else simplify(value)) }) // FIXME ???
    case IR.Def(DUpdate(x, f, y))  => IR.update(simplify(x), simplify(f), simplify(y))
    case IR.Def(DSelect(x, f))     => IR.select(simplify(x), simplify(f))
    case IR.Def(DPlus(x, y))       => IR.plus(simplify(x), simplify(y))
    case IR.Def(DTimes(x, y))      => IR.times(simplify(x), simplify(y))
    case IR.Def(DLess(x, y))       => simplifyBool(IR.less(simplify(x), simplify(y)))
    case IR.Def(DEqual(x, y))      => simplifyBool(IR.equal(simplify(x), simplify(y)))
    case IR.Def(DNot(x))           => IR.not(simplify(x))
    case IR.Def(DSum(n, x, c))     => IR.sum(simplify(n), x, simplify(c))
    case IR.Def(DCollect(n, x, c)) => IR.collect(simplify(n), x, simplify(c)) // (toOProb(IR.not(IR.less(GRef(x), 0))) ++: constraints))
    case IR.Def(DCall(f, x))       => IR.call(simplify(f), simplify(x))
    case IR.Def(DFun(f, x, y))     => IR.fun(f, x, simplify(y))
    case IR.Def(DHasField(x, f))   => IR.hasfield(simplify(x), simplify(f))
    // case x@GRef(_) if x.toString == "x8?" => IR.const(0)
    case x@GRef(_) => println(s"Ref $x")
      simplifyBool(IR.equal(x, IR.const(0))) match { // FIXME: hack if GRef(x) == 0
        case GConst(1) => println(s"Simplifed $x"); IR.const(0)
        case z@_ => println(s"Simplify ref: ${IR.termToString(z)} - $constraints"); x
      }
    case _ => term
  }

  def handleLoop(l:String)(body: => Unit): Unit = {
    import IR._
    val saveit = itvec

    val loop = GRef(freshVar)
    val n0 = GRef(freshVar + "?")

    val before = store

    itvec = pair(itvec,n0)

    println(s"begin loop f(n)=$loop($n0), iteration vector $itvec {")

    println(s"initial assumption: f(0)=$before, f($n0)=$before, f($n0+1)=$before")

    var init = before
    var path = Nil: List[GVal]

    var iterCount = 0
    def iter: GVal = {
      if (iterCount > 3) { println("XXX ABORT XXX"); return GConst(0) }
      println(s"## iteration $iterCount, f(0)=$before, f($n0)=$init")
      assert(!path.contains(init), "hitting recursion: "+(init::path))
      path = init::path

      store = init

      // s"bool ${l}_more = false"
      val more = l+"_more"
      store = IR.update(store, IR.const(more), GConst(0))

      body // eval loop body ...

      var constraints: List[OProb] = toOProb(not(less(n0,const(0)))) ++: Nil
      println(s"more: ${IR.termToString(IR.select(store,IR.const(more)))}")
      val cv = simplify(IR.select(store,IR.const(more)))(constraints)

      constraints ++= toOProb(simplify(not(less(fixindex(n0.toString, cv),n0)))(constraints))

      // FIXME: is it still necessary? Should be handle by simplification step.
      // store = subst(store,less(fixindex(n0.toString, cv),n0),const(0)) // i <= n-1
      // store = subst(store,less(n0,const(0)),const(0)) // 0 <= i

      println(s"Store after iter: ${IR.termToString(store)}")
      // store = simplify(store)(constraints)
      // println(s"Store after simplifications: ${IR.termToString(store)}")

      println("trip count: "+termToString(fixindex(n0.toString, cv)))


      val afterB = store

      // inside the loop we know the check succeeded.
      // val next = subst(afterB,cv,const(1))

      val trueClauses = assumeTrue(cv)(constraints)
      println(s"TrueClauses:\n")
      printList(trueClauses)

      // FIXME: may be useful for complex form
      // var next = (afterB /: trueClauses) {
      //   case (agg, t) => subst(subst(agg, t, const(1)), not(t), const(0))
      // }

      constraints = (trueClauses flatMap(toOProb)) ++ constraints
      val next = simplify(afterB)(constraints)
      println(s"Store after simplifications: ${IR.termToString(next)}")

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
      println(s"Next new:\n${IR.termToString(nextNew)}")
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
        println(s"Store non simplify loop $loop: ${IR.termToString(tmp)}")
        store = simplify(tmp)(Nil)

        // wrap up
        println(s"} end loop $loop, trip count ${IR.termToString(nX)}, state")
        println(s"${IR.termToString(store)}")
        itvec = saveit
        println("======= Iteration Done =======\n")
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
    varCount = varCount0
    globalDefs = globalDefs0
    rebuildGlobalDefsCache()

    var fuel = 1*1000
    def consume(l: String, stop: Set[String], cont: Set[String]): Unit = {
      fuel -= 1; if (fuel == 0) {
        println(l,stop,cont,postDom(l))
        throw new Exception("XXX consume out of fuel")
      }

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

      // Some complication: the immediate post-dominator
      // of a loop header may be *inside* the loop.
      // Need to consume rest of loop body, too.
      val isLoop = loopHeaders contains l
      if (isLoop) {
        handleLoop(l) {
          evalBody(idomIn, cont + l)
          if (idomIn.nonEmpty) // continue consuming loop body
            consume(idomIn.head, idom, cont + l)
        }
      } else {
        evalBody(idom, cont)
      }

      if (idom.nonEmpty)
        consume(idom.head, stop, cont)
    }
    time{consume(entryLabel, Set.empty, Set.empty)}

    val store2 = simplify(store)(Nil)
    println("## term:")
    val out = IR.termToString(store2)
    println(out)
    store2
  }

}
