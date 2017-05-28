package analysis

import java.io.{PrintStream,File,FileInputStream,FileOutputStream,ByteArrayOutputStream}

/* 
  make loop ranges explicit, reason about
  an infinite number of memory addresses
  (allocation site indexed by loop iteration)

  TODO -- WORK IN PROGRESS

  TODO/DONE: 
  + switch to optimistic? (done) 
      can we even talk about opt/pess here? 
      yes, see testProg1c: indirect store updates in
      loops rely on the address being loop invariant
  + make sense of inequalities/recurrences (mostly done)
  + allocations in loops: treat as arrays
      if we're storing the address, the loop variable
      may escape. is that a problem? (skolemize?)
  - towards lancet integration: unstructured control flow
      do we need arbitrary jumps? at least loops with
      several exits (no problem: just take fixindex
      of a different condition / cf. gated ssa).
  - normal and abnormal termination
      we need assert() to signal verification failures
*/

  object SimpleFrontend {
    import Test1._
    import Approx._

    // *** input language Exp

    val IR = IRD

    type Val = IR.From
    type Var = String
    type Addr = String
    type Alloc = String
    type Field = String

    def vref(x: String): Val = IR.const(x)

    abstract class Exp
    case class Const(x: Any) extends Exp
    case class Direct(x: Val) extends Exp
    case class Ref(x: Var) extends Exp
    case class Assign(x: Var, y: Exp) extends Exp
    case class Plus(x: Exp, y: Exp) extends Exp
    case class Times(x: Exp, y: Exp) extends Exp
    case class Less(x: Exp, y: Exp) extends Exp
    case class Equal(x: Exp, y: Exp) extends Exp
    case class NotEqual(x: Exp, y: Exp) extends Exp
    case class New(x: Alloc) extends Exp
    case class Get(x: Exp, f: Exp) extends Exp
    case class Put(x: Exp, f: Exp, y: Exp) extends Exp
    case class Assert(x: Exp) extends Exp
    case class If(c: Exp, a: Exp, b: Exp) extends Exp
    case class While(c: Exp, b: Exp) extends Exp
    case class Block(xs: List[Exp]) extends Exp {
      override def toString = "{\n  " + xs.map(_.toString).mkString("\n").replace("\n","\n  ") + "\n}"
    }

    // *** evaluator: Exp -> IR

    val trackValid = false

    val store0 = if (trackValid) GConst(Map(GConst("valid") -> GConst(1))) else GConst(Map())

    val itvec0 = IR.const("top")

    var store: Val = store0
    var itvec: Val = itvec0

    def eval(e: Exp): Val = e match {
      case Const(x)    => IR.const(x)
      case Direct(x)   => IR.const(x)
      case Ref(x)      => IR.select(IR.select(store,IR.const("&"+x)), IR.const("val"))
      case Assign(x,y) => 
        val v = eval(y)
        store = IR.update(store, IR.const("&"+x), IR.update(IR.const(Map()), IR.const("val"), v))
        IR.const(())
      case Plus(x,y)      => IR.plus(eval(x),eval(y))
      case Times(x,y)     => IR.times(eval(x),eval(y))
      case Less(x,y)      => IR.less(eval(x),eval(y))
      case Equal(x,y)     => IR.equal(eval(x),eval(y))
      case NotEqual(x,y)  => IR.not(IR.equal(eval(x),eval(y)))
      case New(x) => 
        val a = IR.pair(IR.const(x),itvec)
        store = IR.update(store, a, IR.const(Map()))
        a
      case Get(x, f) => 
        val x1 = eval(x)
        val f1 = eval(f)
        IR.select(IR.select(store, x1), f1)
      case Put(x, f, y) => 
        val x1 = eval(x)
        val f1 = eval(f)
        val y1 = eval(y)
        val old = IR.select(store, x1) // must exist, do not merge
        store = IR.update(store, x1, IR.update(old, f1, y1))
        IR.const(())
      case Assert(c) =>
        val c1 = eval(e)
        val old = IR.select(store, IR.const("valid"))
        store = IR.update(store, IR.const("valid"), IR.times(old,c1)) // IR.times means IR.and
        IR.const(())
      case If(c,a,b) => 
        val c1 = eval(c)
        //if (!mayZero(c1)) eval(a) else if (mustZero(c1)) eval(b) else {
          val save = store
          //assert(c1)
          val e1 = eval(a)
          val s1 = store
          store = save
          //assertNot(c1)
          val e2 = eval(b)
          val s2 = store
          store = IR.iff(c1,s1,s2)
          IR.iff(c1,e1,e2)
        //}
      case While(c,b) =>  

        /* Example:
            var y = 0
            while (y < 100) {
              if (y < 0)
                y -= 1
              else
                y += 1
            }
          Note that the behavior crucially depends on the initial condition.

            (0) Assume ŷ(i) = 0
                Evaluate loop body
                  z(i) = if (0 < i) { if (ŷ(i-1) < 0) ŷ(i-1)-1 else ŷ(i-1)+1 } else 0
                       = if (0 < i) { if (0 < 0) 0-1 else 0+1 } else 0
                       = if (0 < i) 1 else 0
                Detect conflict: ŷ(i) = 0 can't be true
                Generalize!

              --> for all i is misleading. just do
              y0 = 0 (assume)
              y1 = if (y0 < 0) y0-1 else y0+1
                 = if (0 < 0) 0-1 else 0+1
                 = 1
              pick ŷ(i) so that it fits ŷ(0)=y0, ŷ(1)=y1 and extrapolate the rest 
                                                   ^ why 1, really?

                ŷ(i) = if (0 < i) i else 0

              assume y0' = ŷ(i-1) = if (0 < i-1) i-1 else 0

              y1' = if (y0 < 0) y0-1 else y0+1
                  = if ((if (0 < i-1) i-1 else 0) < 0) y0-1 else y0+1
                  = ...

            (1) Naive iteration: ŷ(i) = if (0 < i) 1 else 0
                This won't terminate because we'll end up with:
                ŷ(i) = if (0 < i) if (0 < i-1) 2 else 1 else 0

            (2) Generalize: ŷ(i) = if (0 < i) i else 0
        */

        import IR._
        val saveit = itvec

        val loop = GRef(freshVar)
        val n0 = GRef(freshVar)

        val before = store

        itvec = pair(itvec,n0)

        println(s"begin loop f(n)=$loop($n0), iteration vector $itvec {")

        println(s"initial assumption: f(0)=$before, f($n0)=$before, f($n0+1)=$before")

        var init = before
        var path = Nil: List[GVal]

        var iterCount = 0
        def iter: GVal = {
          println(s"## iteration $iterCount, f(0)=$before, f($n0)=$init")
          assert(!path.contains(init), "hitting recursion: "+(init::path))
          path = init::path

          store = init

          //store = subst(store,less(n0,const(0)),const(0)) // 0 <= i

          val cv = eval(c)

          //store = subst(store,cv,const(1)) // assertTrue

          val afterC = store

          eval(b)

          store = subst(store,less(n0,const(0)),const(0)) // 0 <= i
          store = subst(store,less(fixindex(n0.toString, cv),n0),const(0)) // i <= n-1

          println("trip count: "+termToString(fixindex(n0.toString, cv)))

          val afterB = store

          //val next = IR.iff(cv,afterB,afterC)
          // inside the loop we know the check succeeded.
          val next = subst(afterB,cv,const(1))

          // generalize init/next based on previous values
          // and current observation
          println(s"approx f(0)=$before, f($n0)=$init, f($n0+1)=$next) = {")

          val (initNew,nextNew) = lub(before, init, next)(loop,n0)

          println(s"} -> f($n0)=$initNew, f($n0+1)=$nextNew")

          // are we done or do we need another iteration?
          if (init != initNew) { init = initNew; iterCount += 1; iter } else {
            // no further information was gained: go ahead
            // and generate the final (set of) recursive 
            // functions, or closed forms.
            println(s"create function def f(n) = $loop($n0) {")

            // given f(n+1) = nextNew, derive formula for f(n)
            val body = iff(less(const(0),n0),
                          subst(nextNew,n0,plus(n0,const(-1))),
                          before)

            // Note that body should be the same as initNew,
            // except when we're giving up and generating
            // a recursive function. In that case, init would
            // have an infinite loop and body contains the
            // loop body unfolded once.

            // Note that currently, body also may include
            // explicit checks like if (0 < n0) n0 else 0.
            // These could be optimized to just n0 if we had
            // a contract that such functions can only be
            // called with argument >= 0.

            /*if (initNew != body) {
              println(s"init: $loop = {$n0 => ${termToString(initNew)}}")
              println(s"body: $loop = {$n0 => ${termToString(body)}}")
            }*/

            // create function definition, which we call below
            lubfun(loop,n0,body)

            println("}")

            // compute trip count
            val nX = fixindex(n0.toString, cv)

            // invoke computed function at trip count
            store = call(loop,nX)

            // A note about the intended semantics:
            // Elem i is the value _after i iterations_,
            // i.e. the value _before iteration i_.
            // An alternative, based on the analogy of 
            // modeling values computed in loops
            // as arrays indexed by iteration count would
            // suggest the meaning 'computed in iteration i'.
            // This also works. We would change the default
            // recursive case to call f(n-1) directly, then
            // use nextNew as the body without modification,
            // and finally select nX - 1.
            // With this model, we'd have f(i) = i+1 for a
            // simple counting loop, which is somewhat
            // less intuitive.
            // On the other hand, for dynamic allocations, 
            // we'd get f(i) = new A_i, which makes sense
            // intuitively.


            // wrap up
            itvec = saveit
            
            println(s"} end loop $loop, trip count $nX, state $store")

            IR.const(())
          }
        }

        iter

      case Block(Nil) => IR.const(())
      case Block(xs) => xs map eval reduceLeft ((a,b) => b)
    }

  }

  object Main {
    import Test1._
    import SimpleFrontend._
    // *** run and test

    def run(testProg: Exp): Unit = runAndCheck(testProg)

    def runAndCheck(testProg: Exp): String = {
      println("# prog: " + testProg)
      store = store0
      itvec = itvec0
      varCount = varCount0
      globalDefs = globalDefs0
      rebuildGlobalDefsCache()

      println("# eval:")
      val res = eval(testProg)
      
      println("# result:")
      println("res: " + res)
      println("store: " + store)
      val store2 = store//IR.iterateAll(store)
      println("transformed: " + store2)

      println("## sched:")
      val sched = IR.schedule(store2)
      sched.foreach(IR.printStm)

      println("## term:")
      val out = IR.termToString(store2)
      println(out)

      println("# done")
      out
    }
  }
