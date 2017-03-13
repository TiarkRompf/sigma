package analysis

import java.io.{PrintStream,File,FileInputStream,FileOutputStream,ByteArrayOutputStream}

/* 
  make loop ranges explicit, reason about
  an infinite number of memory addresses
  (allocation site indexed by loop iteration)

  TODO -- WORK IN PROGRESS

  TODO/DONE: 
  - switch to optimistic? (done) 
      can we even talk about opt/pess here? 
      yes, see testProg1c: indirect store updates in
      loops rely on the address being loop invariant
  - make sense of inequalities/recurrences (mostly done)
  - allocations in loops: treat as arrays
      if we're storing the address, the loop variable
      may escape. is that a problem? (skolemize?)
  - towards lancet integration: unstructured control flow
      do we need arbitrary jumps? at least loops with
      several exits (no problem: just take fixindex
      of a different condition / cf. gated ssa).
  - normal and abnormal termination
      we need assert() to signal verification failures
*/

  object Frontend {
    import Test1._

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
    case class If(c: Exp, a: Exp, b: Exp) extends Exp
    case class While(c: Exp, b: Exp) extends Exp
    case class Block(xs: List[Exp]) extends Exp {
      override def toString = "{\n  " + xs.map(_.toString).mkString("\n").replace("\n","\n  ") + "\n}"
    }

    // *** evaluator: Exp -> IR

    val store0 = IR.const(Map())
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
      case NotEqual(x,y)  => IR.notequal(eval(x),eval(y))
      case New(x) => 
        val a = IR.pair(IR.const(x),itvec)
        store = IR.update(store, a, IR.const(Map()))
        a
      case Get(x, f) => 
        IR.select(IR.select(store, eval(x)), eval(f))
      case Put(x, f, y) => 
        val a = eval(x)
        val old = IR.select(store, a)
        store = IR.update(store, a, IR.update(old, eval(f), eval(y)))
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

        var init = before
        var path = Nil: List[GVal]

        println(s"begin loop f(n)=$loop($n0), iteration vector $itvec {")

        var iterCount = 0
        def iter: GVal = {
          println(s"## iteration $iterCount, f(0)=${termToString(before)}, f(n)=${termToString(init)}")
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

          println(s"state after loop $afterB")

          //val next = IR.iff(cv,afterB,afterC)
          // inside the loop we know the check succeeded.
          // TODO: need to worry about boundary cases!
          val next = subst(afterB,cv,const(1))

          // generalize init/next based on previous values
          // and current observation
          println(s"approx f(0)=$before, f(n)=$init, f(n+1)=g(n)=$next) = {")

          val (initNew,nextNew) = lub(before, init, next)(loop,n0)

          println(s"} -> f(n)=$initNew, f(n+1)=g(n)=$nextNew")

          // are we done or do we need another iteration?
          if (init != initNew) { init = initNew; iterCount += 1; iter } else {
            // no further information was gained: go ahead
            // and generate the final (set of) recursive 
            // functions, or closed forms.
            store = lubfun(before, nextNew)(loop,n0)

            // XXX why not just nextNew ??? 
            // need to define functions that are called from nextNew
            //store = nextNew

            // TODO: clarify intended semantics!
            // Is elem 0 the value after 0 iterations,
            // or the value computed in iteration 0?
            // The analogy of modeling values computed in
            // loops as arrays indexed by iteration would
            // suggest the meaning 'computed in iteration i'.
            // But then the value before the loop has index -1.
            // Need to investigate whether this is a problem.
            // It seems like we can avoid referring to -1
            // by proper index handling after the loop.

            // store at this point describes result *after* iteration i
            //  1 + (if (0<x) f(x-1) else 0)  =   if (0<x) f(x-1) + 1 else 1
            // but what we want for the function body:
            //  if (0<x) f(x-1) + 1 else 0
            // we rely on propagation of conditions to get there:

            //store = iff(less(const(0), n0), store, before)

            // The alternative would be to make f(i) denote
            // the computed element in iteration i, and then pick
            // element n-1 after the loop.
            // It may seem unintuitive that f(i) = i+1 for a
            // simple counting loop and we might want to fix
            // it up with rewriting.
            // On the other hand, for dynamic allocations, 
            // we get f(i) = new A_i, which makes a lot of
            // sense.
            //store = init
            cv
          }
        }

        val cv = iter

        if (findDefinition(loop.toString) == None) // ensure we have a top-level function
          fun(loop.toString, n0.toString, store)

        val nX = fixindex(n0.toString, cv) // TODO: check this ...
        println(s"fixindex: $nX")

        // TODO: if (0 < nX) !
        store = call(loop,plus(nX,const(-1)))
        //val cv1 = eval(c)
        //store = subst(store,cv1,const(0)) // assertFalse

        itvec = saveit
        
        println(s"} end loop $loop, trip count $nX, state $store")

        IR.const(())

      case Block(Nil) => IR.const(())
      case Block(xs) => xs map eval reduceLeft ((a,b) => b)
    }

  }

  object Main {
    import Test1._
    import Frontend._
    // *** run and test

    def run(testProg: Exp): Unit = runAndCheck(testProg)("")

    def runAndCheck(testProg: Exp)(want: Any): Unit = {
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

      def clean(s: String) = s.replaceAll("\"","").replaceAll("\n","").replaceAll(" +","")

      if (want != "")
        assert(clean(want.toString) == clean(out)) //sanitize...

      //store.printBounds
      println("# done")
    }
  }
