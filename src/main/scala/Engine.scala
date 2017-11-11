package analysis

import java.io.{PrintStream,File,FileInputStream,FileOutputStream,FileNotFoundException,ByteArrayOutputStream}


  object Util {

    // *** util

    def time[S](block: =>S): S = {
      val t0 = System.currentTimeMillis
      try block finally {
        val t1 = System.currentTimeMillis
        println(s"took ${t1-t0}ms")
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
    def captureOutput(func: => Unit): String = {
      val bstream = new ByteArrayOutputStream
      withOutput(new PrintStream(bstream))(func)
      bstream.toString
    }
    def captureOutputResult[A](func: => A): (String,A) = {
      import java.io._
      val bstream = new ByteArrayOutputStream
      val r = withOutput(new PrintStream(bstream))(func) //func
      (bstream.toString, r)
    }
    def withOutput[A](out: java.io.PrintStream)(func: => A): A = {
      //val oldStdOut = System.out
      //val oldStdErr = System.err
      try {
        //System.setOut(out)
        //System.setErr(out)
        scala.Console.withOut(out)(scala.Console.withErr(out)(func))
      } finally {
        out.flush()
        out.close()
        //System.setOut(oldStdOut)
        //System.setErr(oldStdErr)
      }
    }

    val debugF = false
    def debug(s: => String) = if (debugF) println("DEBUG: " + s)
  }


  object Test1 {
    import Util._

    // *** intermediate language / IR interfaces

    abstract class GVal {
      override def toString: String = this match {
        case GRef(s)   => s
        case GConst(x: String) => "\""+x+"\""
        case GConst(x) => s"$x"
        case GError => "<error>"
      }
    }

    case class GRef(s: String) extends GVal
    case class GConst(x: Any) extends GVal
    case object GError extends GVal

    object GType {
      val int = GConst("int")
      val string = GConst("string")
      val void = GConst("void")
      def pointer(x: GConst) = x match {
        case GConst(tpe) => GConst(tpe+" *")
      }

      def apply(s: String) = GConst(s)
    }

    abstract class Def {
      override def toString: String = mirrorDef(this, DString)
    }

    case class DMap(m: Map[GVal,GVal]) extends Def
    case class DUpdate(x: GVal, f: GVal, y: GVal) extends Def
    case class DSelect(x: GVal, f: GVal) extends Def
    case class DPlus(x: GVal, y: GVal) extends Def
    case class DTimes(x: GVal, y: GVal) extends Def
    case class DLess(x: GVal, y: GVal) extends Def
    case class DEqual(x: GVal, y: GVal) extends Def
    case class DNot(x: GVal) extends Def
    case class DPair(x: GVal, y: GVal) extends Def
    case class DIf(c: GVal, x: GVal, y: GVal) extends Def
    case class DSum(n: GVal, x: String, c: GVal) extends Def
    case class DCollect(n: GVal, x: String, c: GVal) extends Def
    case class DFixIndex(x: String, c: GVal) extends Def
    case class DCall(f: GVal, x: GVal) extends Def
    case class DFun(f: String, x: String, y: GVal) extends Def
    case class DOther(s: String) extends Def
    case class DHasField(x: GVal, f: GVal) extends Def

    def mirrorDef(d: Def, dst: DIntf { type From >: GVal }): dst.To = d match {
      case DMap(m)                                  => dst.map(m.asInstanceOf[Map[dst.From, dst.From]])
      case DUpdate(x: GVal, f: GVal, y: GVal)       => dst.update(x,f,y)
      case DSelect(x: GVal, f: GVal)                => dst.select(x,f)
      case DPlus(x: GVal, y: GVal)                  => dst.plus(x,y)
      case DTimes(x: GVal, y: GVal)                 => dst.times(x,y)
      case DLess(x: GVal, y: GVal)                  => dst.less(x,y)
      case DEqual(x: GVal, y: GVal)                 => dst.equal(x,y)
      case DNot(x: GVal)                            => dst.not(x)
      case DPair(x: GVal, y: GVal)                  => dst.pair(x,y)
      case DIf(c: GVal, x: GVal, y: GVal)           => dst.iff(c,x,y)
      case DSum(n: GVal, x: String, c: GVal)        => dst.sum(n,x,c)
      case DCollect(n: GVal, x: String, c: GVal)    => dst.collect(n,x,c)
      case DFixIndex(x: String, c: GVal)            => dst.fixindex(x,c)
      case DCall(f: GVal, x: GVal)                  => dst.call(f,x)
      case DFun(f: String, x: String, y: GVal)      => dst.fun(f,x,y)
      case DOther(s: String)                        => dst.other(s)
      case DHasField(x: GVal, f: GVal)              => dst.hasfield(x,f)
    }

    trait DIntf {
      type From
      type To
      def map(m: Map[From,From]): To
      def update(x: From, f: From, y: From): To
      def select(x: From, f: From): To
      def plus(x: From, y: From): To
      def times(x: From, y: From): To
      def less(x: From, y: From): To
      def equal(x: From, y: From): To
      def not(x: From): To
      def pair(x: From, y: From): To
      def iff(c: From, x: From, y: From): To
      def sum(n: From, x: String, c: From): To
      def collect(n: From, x: String, c: From): To
      def fixindex(x: String, c: From): To
      def call(f: From, x: From): To
      def fun(f: String, x: String, y: From): To
      def other(s: String): To
      def hasfield(x: From, f: From): To
    }

    object DString extends DIntf {
      type From = Any
      type To = String
      def map(m: Map[From,From])                   = s"$m"
      def update(x: From, f: From, y: From)        = s"$x + ($f -> $y)"
      def select(x: From, f: From)                 = s"$x($f)"
      def plus(x: From, y: From)                   = s"$x + $y"
      def times(x: From, y: From)                  = s"$x * $y"
      def less(x: From, y: From)                   = s"$x < $y"
      def equal(x: From, y: From)                  = s"$x == $y"
      def not(x: From)                             = s"!($x)"
      def pair(x: From, y: From)                   = s"($x,$y)"
      def iff(c: From, x: From, y: From)           = s"if ($c) $x else $y"
      def sum(n: From, x: String, c: From)         = s"sum($n) { $x => $c }"
      def collect(n: From, x: String, c: From)     = s"collect($n) { $x => $c }"
      def fixindex(x: String, c: From)             = s"fixindex { $x => $c }"
      def call(f: From, x: From)                   = s"$f($x)"
      def fun(f: String, x: String, y: From)       = s"{ $x => $y }"
      def other(s: String)                         = s
      def hasfield(x: From, f: From)               = s"$x contains $f"
    }

    object DDef extends DIntf {
      type From = GVal
      type To = Def
      def map(m: Map[From,From])                   = DMap(m)
      def update(x: From, f: From, y: From)        = DUpdate(x,f,y)
      def select(x: From, f: From)                 = DSelect(x,f)
      def plus(x: From, y: From)                   = DPlus(x,y)
      def times(x: From, y: From)                  = DTimes(x,y)
      def less(x: From, y: From)                   = DLess(x,y)
      def equal(x: From, y: From)                  = DEqual(x,y)
      def not(x: From)                             = DNot(x)
      def pair(x: From, y: From)                   = DPair(x,y)
      def iff(c: From, x: From, y: From)           = DIf(c,x,y)
      def sum(n: From, x: String, c: From)         = DSum(n,x,c)
      def collect(n: From, x: String, c: From)     = DCollect(n,x,c)
      def fixindex(x: String, c: From)             = DFixIndex(x,c)
      def call(f: From, x: From)                   = DCall(f,x)
      def fun(f: String, x: String, y: From)       = DFun(f,x,y)
      def other(s: String)                         = DOther(s)
      def hasfield(x: From, f: From)               = DHasField(x,f)
    }

    trait DXForm extends DIntf {
      type From
      type To
      val next: DIntf
      def pre(x: From): next.From
      def post(x: next.To): To
      def map(m: Map[From,From])                   = post(next.map(m.map(kv=>pre(kv._1)->pre(kv._2))))
      def update(x: From, f: From, y: From)        = post(next.update(pre(x),pre(f),pre(y)))
      def select(x: From, f: From)                 = post(next.select(pre(x),pre(f)))
      def plus(x: From, y: From)                   = post(next.plus(pre(x),pre(y)))
      def times(x: From, y: From)                  = post(next.times(pre(x),pre(y)))
      def less(x: From, y: From)                   = post(next.less(pre(x),pre(y)))
      def equal(x: From, y: From)                  = post(next.equal(pre(x),pre(y)))
      def not(x: From)                             = post(next.not(pre(x)))
      def pair(x: From, y: From)                   = post(next.pair(pre(x),pre(y)))
      def iff(c: From, x: From, y: From)           = post(next.iff(pre(c),pre(x),pre(y)))
      def sum(n: From, x: String, c: From)         = post(next.sum(pre(n),x,pre(c)))
      def collect(n: From, x: String, c: From)     = post(next.collect(pre(n),x,pre(c)))
      def fixindex(x: String, c: From)             = post(next.fixindex(x,pre(c)))
      def call(f: From, x: From)                   = post(next.call(pre(f),pre(x)))
      def fun(f: String, x: String, y: From)       = post(next.fun(f,x,pre(y)))
      def other(s: String)                         = post(next.other(s))
      def hasfield(x: From, f: From)               = post(next.hasfield(pre(x),pre(f)))
    }



    // state: reflect/reify

    val varCount0 = 0
    var varCount = varCount0

    val globalDefs0 = Nil
    var globalDefs: List[(String,Def)] = globalDefs0

    var globalDefsRhs: Map[String,Def] = Map()
    var globalDefsLhs: Map[Def,String] = Map()

    def rebuildGlobalDefsCache() = { globalDefsRhs = globalDefs.reverse.toMap; globalDefsLhs = globalDefs.reverse.map(kv => (kv._2,kv._1)).toMap }

    def freshVar = { varCount += 1; "x"+(varCount - 1) }

    def reflect(x: String, s: String): String = { println(s"val $x = $s"); x }

    def reflect(s: String): String = { val x = freshVar; println(s"val $x = $s"); x }
    def reify(x: => String): String = captureOutputResult(x)._1

    def findDefinition(s: String): Option[Def] = globalDefsRhs.get(s)
      //globalDefs.reverse.collectFirst { case (`s`,d) => d }

    def dreflect(x0: => String, s: Def): GVal = globalDefsLhs.get(s).map(GRef).getOrElse {
      val x = x0;
      globalDefs = (x->s)::globalDefs
      globalDefsRhs = globalDefsRhs + (x->s)
      globalDefsLhs = globalDefsLhs + (s->x)
      println(s"val $x = $s")
      GRef(x)
    }
    //globalDefs.collect { case (k,`s`) => GRef(k) }.headOption getOrElse {
    //val x = x0; globalDefs = globalDefs :+ (x->s); println(s"val $x = $s"); GRef(x) }
    def dreflect(s: Def): GVal = dreflect(freshVar,s)


    // pretty printing

    object IRS extends DXForm {
      type From = String
      type To = String
      val next = DString
      def const(x: Any) = s"$x"
      def pre(x: String) = x
      def post(x: String): String = reflect(x)
      override def fun(f: String, x: String, y: From) = reflect(f,next.fun(f,x,pre(y)))
    }
    object IRS_Term extends DXForm {
      type From = GVal
      type To = String
      val next = DString
      def const(x: Any) = s"$x"
      def pre(x: GVal) = findDefinition(x.toString).map(d=>mirrorDef(d,this)).getOrElse(x.toString)
      def preBlock(x: GVal) = {
        val s = pre(x)
        if (s startsWith "if") s"{\n  ${s.replace("\n","\n  ")}\n}"
        else s
      }
      def post(x: String): String = x
      var rec: List[String] = Nil
      def reset = rec = Nil // HACK
      def scope[T](a: =>T): T = { reset; a }
      override def fun(f: String, x: String, y: From) = if (rec contains f) f else {
        rec ::= f; reflect(f,next.fun(f,x,pre(y)))
      }
      override def iff(c: From, x: From, y: From) = post(next.iff(pre(c),preBlock(x),preBlock(y)))
    }


    // main IR rewriting engine

    object IRD extends DXForm {
      type From = GVal
      type To = GVal
      val next = DDef
      //def const(x: Any) = GConst(x)
      def pre(x: GVal) = x
      def post(x: Def): GVal = dreflect(x)
      //override def fun(f: String, x: String, y: From) = dreflect(f,next.fun(f,x,pre(y)))

      object Def {
        def unapply(x:GVal): Option[Def] = x match {
          case GConst(_) => None
          case GRef(s)   => findDefinition(s)
          case GError => None
        }
      }

      // dependencies / schedule
      def syms(d: Def): List[String] = {
        var sl: List[String] = Nil
        object collector extends DXForm {
          type From = GVal
          type To = String // ignore
          val next = DString
          def pre(x: GVal) = x match { case GRef(s) => sl ::= s; s case _ => "" }
          def post(x: String) = x
          //override def fun(f: String,x: String,y: GVal) = ""
        }
        mirrorDef(d,collector)
        sl
      }
      def boundSyms(d: Def): List[String] = d match { case DFun(f,x,y) => List(f,x) case _ => Nil }
      def deps(st: List[String]): List[(String,Def)] =
        globalDefs.filter(p=>st contains p._1) // TODO: opt
      def schedule(x: GVal) = {
        val start = x match { case GRef(s) => List(s) case _ => Nil }
        val xx = GraphUtil.stronglyConnectedComponents[(String,Def)](deps(start), t => deps(syms(t._2)))
        xx.flatten.reverse
      }

      def printStm(p: (String,Def)) = println(s"val ${p._1} = ${p._2}")
      def termToString(p: GVal) = captureOutput(print(IRS_Term.scope(IRS_Term.pre(p))))
      def printTerm(p: GVal) = println(termToString(p))

      // does a depend on b? potentially expensive
      def dependsOn(a: GVal, b: GVal) = schedule(a).exists(p => GRef(p._1) == b || syms(p._2).contains(b.toString))

      def mkey(f: GVal, x: GVal): GVal = x match {
        case GConst(s) => GRef(f+"_"+s)
        case GRef(s) => GRef(f+"_"+s)
      }

      // evaluate with substitution, i.e. compute trans closure of subst
      def substTrans(env0: Map[GVal,GVal]): Map[GVal,GVal] = {
        var env = env0
        object XXO extends DXForm {
          type From = GVal
          type To = GVal
          val next = IRD
          def pre(x: GVal) = {/*println(s"pre $x / $env");*/ env.getOrElse(x,x) }
          def post(x: GVal) = x
          override def fun(f: String, x: String, y: From) = {
            //println(s"not changing fundef $f $x $y -> ${pre(y)}")
            GRef(f) // don't transform fundef
          }
        }
        for ((e,d) <- globalDefs.reverse) {
          val e2 = mirrorDef(d,XXO)
          //println(s"$e -> $e2 = $d")
          if (e2 != GRef(e))
            env = env + (GRef(e) -> e2)
        }
        // need to iterate because of sched order
        if (env == env0) env else substTrans(env)
      }

      // subst a -> b in term x. we perform hereditary substition,
      // i.e. normalize/optimize on the fly. of particular concern
      // are conditionals (if/else)
      def subst(x: GVal, a: GVal, b: GVal): GVal = a match {
        case Def(DNot(a))        => subst(x,a,not(b))
        case _                   => subst1(x,a,b)
      }
      def subst1(x: GVal, a: GVal, b: GVal): GVal = x match {
        case `a`                 => b
        case GConst(_)           => x
        case Def(DUpdate(x,f,y)) => update(subst(x,a,b),subst(f,a,b),subst(y,a,b))
        case Def(DSelect(x,f))   => select(subst(x,a,b),subst(f,a,b))
        case Def(DMap(m))        =>

          // TODO: what if stuff is substituted to the same key??
          map(m.map(kv => subst(kv._1,a,b) -> subst(kv._2,a,b)))

        case Def(dd@DIf(c@Def(o@DEqual(u,v)),x,y)) =>
          // in general, if a implies c we can take branch x; if a refutes c, y.
          // if a & c implies that something is a constant, propagate that
          a match {
            case Def(p@DEqual(`u`,s)) =>
              //println(s"another == flying by: $o, $p -> $b")
              if (b == const(1)) { // u == s
                if (equal(s,v) == const(1))      // u == s && s == v --> u == v:
                  return subst(x,c,const(1))
                else if (equal(s,v) == const(0)) // u == s && s != v --> u != v:
                  return subst(y,c,const(0))
              }
              if (b == const(0)) { // u != s
                if (equal(s,v) == const(1))      // u != s && s == v --> u != v:
                  return subst(y,c,const(0))
                //else if (equal(s,v) == const(0)) // u != s && s != v --> u == v:
                //  return subst(x,c,const(1))
              }
            case _ =>
          }
          iff(subst(c,a,b),subst(x,a,b),subst(y,a,b))
        case Def(dd@DIf(c@Def(o@DLess(u,v)),x,y)) =>
          // in general, if a implies c we can take branch x; if a refutes c, y.
          // if a & c implies that something is a constant, propagate that
          a match {
            case Def(p@DLess(`u`,s)) =>
              // evaluate u < v  given that u < s or ¬(u < s)
              //println(s"another < flying by: $o, $p -> $b")
              // look for: a < x && !(a < x-1) ---> x == 1
              if (s == plus(v,const(-1))) { // other constants?
                if (b == const(1)) {
                  println(s"hit: $u<$v-1 implies $u<$v in $dd")
                  return subst(x,a,b)
                }
                if (b == const(0)) {
                  println(s"¬$u<$v-1 and $u<$v implies $u=$v-1 in $dd")
                  if (u.isInstanceOf[GConst])
                    return iff(subst(c,a,b),subst(x,s,plus(u,const(1))),subst(y,a,b))
                  else
                    return iff(subst(c,a,b),subst(x,u,s),subst(y,a,b))
                }
              }
              if (v == plus(s,const(-1))) { // other constants?
                if (b == const(0)) {
                  println(s"hit2: ¬$u<$s refutes $u<$s-1 in $dd")
                  return subst(y,a,b)
                }
                if (b == const(1)) {
                  println(s"hit2: $u<$s and ¬$u<$s-1 implies $u=$s-1 in $dd")
                  if (u.isInstanceOf[GConst])
                    return iff(subst(c,a,b),subst(x,a,b),subst(y,s,plus(u,const(1))))
                  else
                    return iff(subst(c,a,b),subst(x,a,b),subst(y,u,s))
                }
              }

            // look for: 0 < x6 && !(0 < x6 + -1) ---> x6 == 1
                // if (0 < x6) if (0 < x6 + -1) if (0 < x6 + -2) if (x6 < 102) if (x6 < 101) x100 + 1
                // else x100 else x100 else x100 + 1 else x100 + 1 else 0

            case Def(p@DLess(`v`,s)) =>
              // !(x9 < 100) && (0 < 100) --> !(0<x9)
              // !(s,u)
              if (less(u,s) == const(1) && b == const(0)) {
                println(s"hit3: $v<$s=$b && $u<$s=${less(u,s)} --> $u<$v=0")
                // !(s < u) && (s < v) ---> (u < v)
                return subst(x,a,b)
              }

            case _ =>
          }
          iff(subst(c,a,b),subst(x,a,b),subst(y,a,b))
        case Def(DIf(c,x,y))     => iff(subst(c,a,b),subst(x,a,b),subst(y,a,b))
        case Def(DPair(x,y))     => pair(subst(x,a,b),subst(y,a,b))
        case Def(DPlus(x,y))     => plus(subst(x,a,b),subst(y,a,b))
        case Def(DTimes(x,y))    => times(subst(x,a,b),subst(y,a,b))
        case Def(o@DLess(u,v))     =>
          a match { // TODO
            case Def(p@DLess(`u`,s)) =>
              //if (v == s || less(s,v) == const(1)) return const(1)
            case _ =>
          }
          less(subst(u,a,b),subst(v,a,b))
        case Def(DEqual(x,y))    => equal(subst(x,a,b),subst(y,a,b))
        case Def(DNot(x))        => not(subst(x,a,b))
        case Def(DCall(f,y))     => call(subst(f,a,b),subst(y,a,b))
        case Def(DFun(f,x1,y))   => x//subst(y,a,b); x // binding??
        case Def(DSum(n,x,y))    => sum(subst(n,a,b),x,subst(y,a,b))
        case Def(DCollect(n,x,y))=> collect(subst(n,a,b),x,subst(y,a,b))
        case Def(DFixIndex(x,y)) => fixindex(x,subst(y,a,b))
        case Def(DHasField(x,y)) => hasfield(subst(x,a,b), subst(y,a,b))
        case Def(d)              => println("no subst: "+x+"="+d); x
        case _                   => x // TOOD
      }


      // smart constructors

      def const(x: Any) = x match {
        case x: Double if x.toInt.toDouble == x => GConst(x.toInt)
        // case x: Double if x.toInt.toDouble == x => GConst(Map("value" -> x.toInt, "type" -> GType.int))
        // case x: Int => GConst(Map("value" -> x, "type" -> GType.int))
        // case x: String => GConst(Map("value" -> x, "type" -> GType.string))
        case _ => GConst(x)
      }
      // like update, but accept map to be empty/undefined
      // must be invoked as update(x,u,merge(select(x,u),v,y))
      def merge(x: From, f: From, y: From): From = x match {
        case GError => update(dreflect(DMap(Map())),f,y) // caveat: f may be non-const ?
        case _ => update(x,f,y)
      }
      override def update(x: From, f: From, y: From): From = x match {
        case GError => x // undefined
        //case GConst("undefined") => update(dreflect(DMap(Map())),f,y) // f may be non-const
        //case GConst("undefined") => x
        case GConst(m:Map[GVal,GVal] @unchecked) /*if m.isEmpty*/ => update(dreflect(DMap(m)),f,y) // f may be non-const -- problem?
        case Def(DMap(m)) =>
          f match {
            case GConst((u,v)) => update(x,const(u),merge(select(x,const(u)),const(v),y)) // store path!!
            case GConst(_) => map(m + (f -> y)) // TODO: y = DIf ??
            case Def(DIf(c,u,v)) => iff(c,update(x,u,y),update(x,v,y))
            case Def(DPair(u,v)) =>
              debug(s"m - $m")
              debug(s"u - ${termToString(u)}")
              debug(s"v - ${termToString(v)}")
              debug(s"y - ${termToString(y)}")
              update(x,u,merge(select(x,u),v,y)) // store path!!
            case _ =>
              // It would be nice to use f as a key even if it
              // is not a constant:
              //    map(m + (f -> y))
              // At present it is not quite clear under what conditions
              // this would work. Clearly, all keys in the map must
              // be statically known to be definitely different.
              debug(s"default 1 - ${termToString(f)}")
              super.update(x,f,y)
          }
        // TODO: DUpdate
        // case Def(DUpdate(x2,f2,y2)) => if (f2 == f) y2 else select(x2,f)
        case Def(DUpdate(x2,f2,y2)) if f2 == f => update(x2,f,y) // this one is conservative: m + (f -> y1) + (f -> y2)   --->  m + (f -> y2)  TODO: more aggressive, e.g. remove f in m, too?
        case Def(DIf(c,u,v)) => iff(c,update(u,f,y),update(v,f,y))
        case Def(DPair(u,v)) =>
          debug(s"u - ${termToString(u)}")
          debug(s"v - ${termToString(v)}")
          debug(s"f - ${termToString(f)}")
          ??? // update(x,u,merge(select(x,u),v,y))
        case _ =>
          debug(s"default 2\n- ${termToString(x)}\n- ${termToString(f)})")
          super.update(x,f,y)
      }
      override def select(x: From, f: From): From          = x match {
        // TODO: should we really say "undefined".x = "undefined" ?
        case GError => GError
        case GConst(m:Map[From,From]) =>
          f match {
            case GConst(_) =>
              m.getOrElse(f, GError)
            case _ =>
              var res: From = GError
              for ((k,v) <- m) {
                res = iff(equal(f,k), v, res)
              }
              res
          }

        case Def(DMap(m)) =>
          f match {
            case GConst((u,v)) => select(select(x,const(u)),const(v))
            case GConst(_) => m.getOrElse(f, GError)
            case Def(DIf(c,u,v)) => iff(c,select(x,u),select(x,v))
            case Def(DPair(u,v)) => select(select(x,u),v)
            case _ =>
              var res: GVal = GError
              for ((k,v) <- m) {
                res = iff(equal(f,k), v, res)
              }
              res
              //return super.select(x,f)
              //m.getOrElse(f, GConst("undefined"))
          }
        case Def(DUpdate(x2,f2,y2)) => iff(equal(f2,f), y2, select(x2,f))
        case Def(DIf(c,x,y)) => iff(c,select(x,f),select(y,f))
        case Def(DPair(u,v)) =>
          debug(s"u - ${termToString(u)}")
          debug(s"v - ${termToString(v)}")
          debug(s"f - ${termToString(v)}")
          // ???
          select(u, select(v,f))  // FIXMEGreg: I don't understand that case
        case Def(DCollect(n,x,c)) => subst(c,GRef(x),f)// FIXME: check bounds!!
        case _ => super.select(x,f)
      }
      override def hasfield(x: From, f: From) = x match {
        case GError => const(0)
        case GConst(m:Map[From,From]) =>
          f match {
            case GConst(_) => const(if (m.contains(f)) 1 else 0)
            case _ =>
              var res: From = const(0)
              for ((k,v) <- m) {
                res = times(equal(f,k), res)
              }
              res
          }
        case Def(DMap(m)) =>
          f match {
            case GConst((u,v)) => times(hasfield(x, const(u)), hasfield(select(x,const(u)),const(v)))
            case GConst(_) => const(if (m.contains(f)) 1 else 0)
            case Def(DIf(c,u,v)) => iff(c,hasfield(x,u),hasfield(x,v))
            case Def(DPair(u,v)) => times(hasfield(x, u), hasfield(select(x,u),v))
            case _ =>
              var res: GVal = const(0)
              for ((k,v) <- m) {
                res = iff(equal(f,k), const(1), res)
              }
              res
              //return super.select(x,f)
              //m.getOrElse(f, GConst("undefined"))
          }
        case Def(DUpdate(x2,f2,y2)) => iff(equal(f2,f), const(1), hasfield(x2,f))
        case Def(DIf(c,x,y)) => iff(c,hasfield(x,f),hasfield(y,f))
        case Def(DCollect(n,x,c)) => const(1) // FIXME: check bounds!!
        case Def(DPair(u,v)) => times(hasfield(v, f), hasfield(u, select(v,f)))  // FIXMEGreg: I don't understand that case
        case _ => super.hasfield(x, f)
      }
      override def plus(x: From, y: From)            = (x,y) match {
        case (GConst(x:Int),GConst(y:Int))       => const(x+y)
        case (GConst(x:Double),GConst(y:Int))    => const(x+y)
        case (GConst(x:Int),GConst(y:Double))    => const(x+y)
        case (GConst(x:Double),GConst(y:Double)) => const(x+y)
        case (GConst(0),_) => y
        case (_,GConst(0)) => x
        case (GError,_) => GError
        case (_,GError) => GError
        case (Def(DIf(c,x,z)),_) => iff(c,plus(x,y),plus(z,y))
        // random simplifications ...
        case (GConst(c),b:GRef) => plus(b,const(c)) // CAVE: non-int consts!
        case (Def(DPlus(a,b)),_) => plus(a,plus(b,y))
        case (a,Def(DTimes(a1,GConst(-1)))) if a == a1 => const(0) // a + (a * -1) --> 0
        case (Def(DTimes(a1,GConst(-1))),a) if a == a1 => const(0) // (a * -1) + a --> 0
        case (a,Def(DPlus(Def(DTimes(a1,GConst(-1))),c))) if a == a1 => c // a + (a * -1) + c --> c
        case (Def(DTimes(a1,GConst(-1))),Def(DPlus(a,c))) if a == a1 => c // (a * -1) + a + c --> c
        case (Def(DTimes(a1,GConst(c1:Int))),Def(DTimes(a2,GConst(c2:Int)))) if a1 == a2 => times(a1,const(c1+c2)) // (a * c1) + (a * c2) --> a * (c1 + c2)
        case (Def(DTimes(a1,GConst(c1:Int))),Def(DPlus(Def(DTimes(a2,GConst(c2:Int))),r))) if a1 == a2 => plus(times(a1,const(c1+c2)),r) // (a * c1) + (a * c2) + r --> a * (c1 + c2) + r
        //case (Def(DTimes(a,GConst(-1))),GConst(c:Int)) => plus(a,GConst(-c)) //(-a+c)=-(-c+a)
        // special case for address-tuples... HACK TODO: proper diff operator!!
        case (Def(DPair(u1,u2)), Def(DPair(v1,v2))) => pair(plus(u1,v1),plus(u2,v2))
        case (GConst((u1,u2)), GConst((v1,v2))) => pair(plus(const(u1),const(v1)),plus(const(u2),const(v2)))
        case (Def(DPair(u1,u2)), GConst((v1,v2))) => pair(plus(u1,const(v1)),plus(u2,const(v2)))
        case _ => super.plus(x,y)
      }
      override def times(x: From, y: From)            = (x,y) match {
        case (GConst(x:Int),GConst(y:Int))       => const(x*y)
        case (GConst(x:Double),GConst(y:Int))    => const(x*y)
        case (GConst(x:Int),GConst(y:Double))    => const(x*y)
        case (GConst(x:Double),GConst(y:Double)) => const(x*y)
        case (GConst(0),_) => GConst(0)
        case (_,GConst(0)) => GConst(0)
        case (GConst(1),_) => y
        case (_,GConst(1)) => x
        case (GError,_) => GError
        case (_,GError) => GError
        case (Def(DIf(c,x,z)),_) => iff(c,times(x,y),times(z,y))
        // random simplifications ...
        case (GConst(c),b:GRef) => times(b,const(c)) // CAVE: non-int consts!
        case (Def(DTimes(a,b)),_) => times(a,times(b,y))
        case (Def(DPlus(a,b)),c) => plus(times(a,c), times(b,c))
        case (a,Def(DPlus(b,c))) => plus(times(a,b), times(a,c))
        // special case for address-tuples... (u,v) * -1
        case (Def(DPair(u1,u2)), y) => pair(times(u1,y),times(u2,y))
        case (GConst((u1,u2)), y) => pair(times(const(u1),y),times(const(u2),y))
        case (x,GConst((v1,v2))) => pair(times(x,const(v1)),times(x,const(v2)))
        case _ => super.times(x,y)
      }
      override def less(x: From, y: From)            = (x,y) match {
        case (GConst(x:Int),GConst(y:Int)) => GConst(if (x < y) 1 else 0)
        case (Def(DIf(c,x,z)),_) => iff(c,less(x,y),less(z,y))
        case (_,Def(DIf(c,y,z))) => iff(c,less(x,y),less(x,z))
        // random simplifications ...
        case (GConst(0),Def(DPlus(a,GConst(b:Int)))) if b < 0 =>  less(const(-b),a)
        // 0 < -a + b  -->  a < b
        case (GConst(0),Def(DPlus(Def(DTimes(a,GConst(-1))),GConst(b:Int)))) =>  less(a,const(b))
        case (Def(DPlus(a,GConst(b:Int))),c) =>  less(a,plus(c,const(-b)))
        case _ if x == y => const(0)
        // case (GConst(0),Def(DPlus())) => y
        case _ => super.less(x,y)
      }
      override def equal(x: From, y: From)           = (x,y) match {
        case (GConst(x),GConst(y)) => GConst(if (x == y) 1 else 0)
        case (GConst(x:Int),Def(DPair(_,_))) => const(0)
        case (GConst(x:String),Def(DPair(_,_))) => const(0)
        case (Def(DPair(_,_)),GConst(x:Int)) => const(0)
        case (Def(DPair(_,_)),GConst(x:String)) => const(0)
        case (Def(DIf(c,x,z)),_) => iff(c,equal(x,y),equal(z,y))
        case (_,Def(DIf(c,y,z))) => iff(c,equal(x,y),equal(x,z))
        case (Def(DMap(m)), Def(DMap(n))) if m.keySet != n.keySet => const(0)
        case (Def(DMap(m)), Def(DMap(n))) =>
          (m :\ (const(1): To)) {
            case ((k1,v1), inner) =>
              times(equal(v1, n(k1)), inner)
          }
        case _ if x == y => const(1)
        case _ => super.equal(x,y)
      }
      override def not(e: From)                      = e match {
        case GConst(0) => GConst(1)
        case GConst(1) => GConst(0)
        case Def(DNot(x)) => x
        case Def(DEqual(GConst(x),GConst(y))) => GConst(if (x == y) 0 else 1)
        case Def(DEqual(GConst(x:Int),Def(DPair(_,_)))) => const(1)
        case Def(DEqual(GConst(x:String),Def(DPair(_,_)))) => const(1)
        case Def(DEqual(Def(DPair(_,_)),GConst(x:Int))) => const(1)
        case Def(DEqual(Def(DPair(_,_)),GConst(x:String))) => const(1)
        case Def(DEqual(Def(DPair(GConst(u1),_)),GConst((v1,v2)))) if u1 != v1 => const(1) // generalize?
        case Def(DEqual(Def(DIf(c,x,z)),y)) => iff(c,not(equal(x,y)),not(equal(z,y)))
        case Def(DEqual(x,Def(DIf(c,y,z)))) => iff(c,not(equal(x,y)),not(equal(x,z)))
        case Def(DEqual(x,y)) if x == y => const(0)
        case _ => super.not(e)
      }
      override def pair(x: From, y: From)            = (x,y) match {
        case (GConst(x),GConst(y)) => const((x,y))
        case _ => super.pair(x,y)
      }
      override def iff(c: From, x: From, y: From):GVal = c match {
        case GConst(0) => y
        case GConst(_) => x
        case Def(DNot(c)) => iff(c,y,x)
        case Def(DIf(c1,x1,y1)) => iff(c1,iff(x1,x,y),iff(y1,x,y))
        case _ if (x,y) == (GConst(1),GConst(0)) => c
        case _ if (x,y) == (GConst(0),GConst(1)) => not(c)
        case _ if x == y => x
        // case Def(DMap(d)) if d.contains(GConst("value")) =>
        //   iff(select(c, GConst("value")), x, y)
        // TODO: if (1 < x6) x6 < 100 else true = x6 < 100
        // Taking the else branch: x6 <= 1 implies x6 < 100, so both branches
        // would return true, ergo condition is redundant.
        // This is a bit of a hack:
        case Def(DLess(GConst(a:Int),xx)) if { x match {
          case Def(DLess(`xx`, GConst(b:Int))) => a < b && y == const(1) case _ => false }} => x
        // Another, similar case: if (1<x6) u-x6 else u-1 =
        // Here we extend to if (0<x6) u-x6 else u-1 in the hope that the condition
        // becomes redundant later
        case Def(DLess(GConst(1),xx)) if subst(x,xx,const(1)) == y => iff(less(const(0),xx),x,y)
        case _ =>
          (x,y) match {
            case (Def(DMap(m1)), Def(DMap(m2))) =>
              // push inside maps
              map((m1.keys++m2.keys) map { k => k -> iff(c,m1.getOrElse(k,const("nil")),m2.getOrElse(k,const("nil")))} toMap)
            case _ =>
              // generate node, but remove nested tests on same condition
              val thenp = subst(x,c,GConst(1))
              val elsep = subst(y,c,GConst(0))

              // maybe we don't need conditional:
              /*val thenpTry = subst(x,c,GConst(0))
              val elsepTry = subst(y,c,GConst(1))

              if (thenp == elsepTry && elsep == thenpTry) {
                println(s"### strange if $c $x $y")
                return x
              }*/
              if (thenp == elsep) thenp
              else if (thenp == const(1) && elsep == const(0)) c
              else super.iff(c,thenp,elsep)
          }
      }

      // LowBound(lowVal,lowBound,highBound,highVal) (not used!)
      object LowBound {
        def unapply(x: GVal): Option[(GVal,GVal,GVal,GVal)] = {
          x match {
            case Def(DIf(Def(DLess(lb,hb)), lv, hv)) => Some(lv,lb,hb,hv)
            case _ => None
          }
        }
      }

      override def sum(n: From, x: String, c: From) = c match {
        case _ =>
          super.sum(n,x,c) //subst(c,less(const(0),GRef(x)),const(1)))
      }
      override def collect(n: From, x: String, c: From) = c match {
        case _ =>
          super.collect(n,x,c) //subst(c,less(const(0),GRef(x)),const(1)))
      }

      override def fixindex(x: String, c: From)       = c match {
        case GConst(0) => const(0)
        //case GConst(1) => const("infty")
        case Def(DLess(GRef(`x`),u)) => u
        case Def(DNot(Def(DEqual(GRef(`x`),u)))) => u
        case Def(DNot(Def(DEqual(u,GRef(`x`))))) => u
        // case Def(DMap(d)) if d.contains(GConst("value")) => fixindex(x, select(c, GConst("value")))
        case _ =>
          super.fixindex(x,c)
      }

      override def call(f: From, x: From)            = f match {
        // inline calls to non-recursive functions
        case Def(DFun(f1,x1,y1)) if !dependsOn(y1,f) =>
          //println(s"*** will inline call $f($x1) = $y1 / $x1 -> $x")
          val res = subst(y1,GRef(x1),x)
          //println(s"**** inlined $f($x1)=$y1 --> $f($x)=$res")
          res
        case _ =>
          super.call(f,x)
      }

      override def fun(f: String, x: String, y: From) = y match {
        // (0)
        // f(x) = if (0 < x) f(x-1) + d else z    --->    f(x) = x * d + z
        // f(x) = if (0 < x) f(x-1)     else z    --->    f(x) = z
        //
        // (1)
        // f(x) = if (0 < x)
        //            if (f(x-1) < u) f(x-1) + d else f(x-1)
        //        else z                          --->    ?
        // (tricky because of recursion in condition: first
        // transform to non-recursive condition using monotonicity?)
        //
        // (1b)
        // f(x) = if (0 < x)
        //            if (f(x-1) == c) f(x-1) else f(x-1) + d
        //        else z                          --->    ?
        //
        // TODO:
        // (2)
        // f(x) = if (0 < x)
        //            f(x-1) + x * c + d
        //        else z                          --->    ?
        // summing the loop variable
        // (extension: e.g.  f(x-1) + k * x  )
        case Def(DIf(zc @ Def(DLess(GConst(0),GRef(`x`))),
            incRes, zeroRes)) =>

          // alt: calc y - subst(y,x,x-1) and see if it depends on x ...
          val prevx = plus(GRef(x),const(-1))
          val prevRes = call(GRef(f),prevx)

          incRes match {
            case `prevRes` =>
              fun(f,x,zeroRes)

            case Def(DPlus(`prevRes`, d)) if true && !dependsOn(d,GRef(x)) =>
              println(s"invariant stride $d")
              println(s"result = $zeroRes + $x * $d")
              val y0 = plus(times(GRef(x),d), zeroRes)
              // Q: do we ever access below-zero values? need > 0 condition?
              val y1 = iff(zc, y0, zeroRes) // CAREFUL!!
              fun(f,x,y1)

            /*case d @ GConst(_) if !dependsOn(d,GRef(x)) =>  // error in iterateAll if not a const ??
              // Q: do we need this case ?? it doesn't seem to do anything
              println(s"invariant res $d")
              println(s"result = $d")
              val y1 = iff(zc,d,zeroRes)
              fun(f,x,y1)*/

            case Def(DIf(Def(DLess(`prevRes`, uprBound)), // (1)
              Def(DPlus(`prevRes`, GConst(1))),  // TODO: non-unit stride
              `prevRes`)) =>
              println(s"upper bounded result")
              println(s"result = $uprBound")
              val y0 = plus(times(GRef(x),const(1)), zeroRes)
              val y1 = iff(less(GRef(x),uprBound), y0, uprBound)
              // Q: do we ever access below-zero values? need > 0 condition?
              val y2 = iff(zc, y1, zeroRes)
              fun(f,x,y2)

            case Def(DIf(Def(DEqual(`prevRes`, uprBound)), // (1b)
              `prevRes`,
              Def(DPlus(`prevRes`, GConst(1))))) =>  // TODO: non-unit stride
              println(s"upper bounded result")
              println(s"result = $uprBound")
              val y0 = plus(times(GRef(x),const(1)), zeroRes)
              val y1 = iff(less(GRef(x),uprBound), y0, plus(y0,const(-1))) // -1 after uprBound
              // Q: do we ever access below-zero values? need > 0 condition?
              val y2 = iff(zc, y1, zeroRes)
              fun(f,x,y2)

            case Def(DPlus(`prevRes`,  // (2)
              Def(DPlus(Def(DTimes(GRef(`x`), GConst(-1))), GConst(d))))) if true =>
              println(s"summing the loop var: -$x+$d")
              println(s"result = - $x * ($x + 1)/2 + $x*$d")
              // (0 to n).sum = n*(n+1)/2
              val xx = GRef(x)
              val y0 = times(times(xx,plus(xx,const(1))),const(-0.5))
              val y1 = plus(y0, times(xx,const(d)))
              val y2 = iff(zc, y1, zeroRes)
              fun(f,x,y2)
              // test case result: 405450
            case _ =>
              dreflect(f,next.fun(f,x,pre(y)))
          }

        case _ =>
          dreflect(f,next.fun(f,x,pre(y))) // reuse fun sym (don't call super)
      }

    }
  }


  // *** polynomial approximation / lub computation for while loops

  object Approx {
    import Test1._
    import IRD._

      // 1) if the type is non-primitive (i.e. Map), break into components
      // 2) when updating a structure at the loop index: assume we're building an array
      // 3) for primitives: compute diff d = f(n+1) - f(n)
      //    a) if expression for d is defined piecewise (i.e. if (n < c) ...), break into segments
      //    b) for each segment:
      //         identify polynomial degree of d
      //         integrate (with starting value f(0) = a) to derive new formula for f(n) and f(n+1))

      // signature:
      // a: value before loop. b0: value before iteration. b1: value after iteration.
      // returns: new values before,after
      def lub(a: GVal, b0: GVal, b1: GVal)(fsym: GVal, n0: GVal): (GVal, GVal) = { println(s"lub_$fsym($a,$b0,$b1)"); (a,b0,b1) } match {
        case (a,b0,b1) if a == b1 => (a,a)
        case (_, _, Def(DMap(m2))) =>
          val m = (m2.keys) map { k => (k, lub(select(a,k),select(b0,k),select(b1,k))(mkey(fsym,k),n0)) }
          println(m)
          (map(m.map(kv=>(kv._1,kv._2._1)).toMap), map(m.map(kv=>(kv._1,kv._2._2)).toMap))
        case (a,b0, Def(DUpdate(bX, `n0`, y))) if bX == b0 || (bX == map(Map()) && b0 == GError) => // array creation
          IRD.printTerm(a)
          IRD.printTerm(b0)
          IRD.printTerm(b1)
          //use real index var !!
          val nX = mkey(fsym,n0)
          println(s"hit update at loop index -- assume collect")
          val r = collect(plus(n0,const(1)), nX.toString, subst(y,n0,nX))
          (r, r)
        case (a/*@Def(DPair(a1,a2))*/,b0/*@Def(DPair(b01,b02))*/,Def(DPair(_,_)) | GConst(_: Tuple2[_,_]))
          if !plus(b1,times(b0,const(-1))).isInstanceOf[GConst] => // XXX diff op should take precedence
          // example: (A,1), (B,(1,i)) TODO: safe?? // test 6B1
          IRD.printTerm(a)
          IRD.printTerm(b0)
          IRD.printTerm(b1)
          println(s"hit pair -- assume only 0 case differs (loop peeling)")
          val b0X = subst(b1,n0,plus(n0,const(-1)))
          (iff(less(const(0),n0),b0X,a), iff(less(const(0),n0),b1,a))
          //(iff(less(const(0),n0),b0X,a), b1) XX FIXME?
        case (a/*@Def(DPair(a1,a2))*/,b0/*@Def(DPair(b01,b02))*/,b1@Def(DIf(Def(DLess(`n0`,u1)),b10,b20)))
          // dual example: (B,(1,i)),(A,1)
          if !dependsOn(u1,n0) => // test 6C2
          IRD.printTerm(a)
          IRD.printTerm(b0)
          IRD.printTerm(b1)
          println(s"hit if dual -- assume only last case differs")
          val b10X = subst(b10,n0,plus(n0,const(-1)))
          val b20X = subst(b20,n0,plus(n0,const(-1)))
          (iff(less(plus(n0,const(-1)),u1),b10X,b20X), b1)
          //(iff(less(const(0),n0),b0X,a), b1) XX FIXME?

          // XXXXX FIXME / TODO
          // PROBLEM: boundary may change with each iteration!!!

        case _ =>
          // value after the loop (b) does depend on loop index and differs from val before loop.
          // handle in
          // TODO: case for alloc in loop -- x(0)=(A,1), x(i>0)=(B,(1,i))
          // (trying to handle this one above...)

          println(s"numerical diff d=f($n0+1)-f($n0) = ${IRD.termToString(b1)} - ${IRD.termToString(b0)} = {")

          // look at numeric difference. see if symbolic values before/after are generalized in a corresponding way.
          // widen: compute new symbolic val before from symbolic val after (e.g. closed form)
          // if that's not possible, widen to explicit recursive form.
          //val b0 = iff(less(const(0), n0), subst(subst(b,less(const(0),n0),const(1)),n0,plus(n0,const(-1))), a) // take from 'init'?
          //val b1 = iff(less(const(0), n0), b, a)
          val d1 = plus(b1,times(b0,const(-1)))

          println("} = " + IRD.termToString(d1))

          if (d1 != GError) { // do we have an integer?

            def poly(x: GVal): List[GVal] = x match {
              case `n0` => List(const(0),const(1))
              case Def(DTimes(`n0`,y)) =>
                val py = poly(y)
                if (py.isEmpty) Nil else const(0)::py
              case Def(DPlus(a,b)) =>
                val (pa,pb) = (poly(a),poly(b))
                if (pa.isEmpty || pb.isEmpty) Nil else {
                  val degree = pa.length max pb.length
                  (pa.padTo(degree,const(0)),pb.padTo(degree,const(0))).zipped.map(plus)
                    .reverse.dropWhile(_ == const(0)).reverse // dropRightWhile
                }
              case _ if !IRD.dependsOn(x, n0) => List(x)
              case _ => Nil // marker: not a simple polynomial
            }

            /*
              piecewise composition, multiple intervals.

              input:
                (value at start index, start index, end index, value increment)
              output:
                (value before iteration, value after iteration, value at end index)

              current iteration is assumed to be between start and end index
            */
            val fail = new Exception
            def break(ulo: GVal, nlo: GVal, nhi: GVal, d: GVal): (GVal,GVal,GVal) = d match {
              // XX now handled in poly case below
              // loop invariant stride, i.e. constant delta i.e. linear in loop index
              // case d if !IRD.dependsOn(d, n0) && d != const("undefined") =>
              //   println(s"confirmed iterative loop, d = $d")
              //   // before: ul + n * d
              //   // after:  ul + (n+1) * d
              //   val dn = plus(n0,times(nlo,const(-1)))
              //   val dh = plus(nhi,times(nlo,const(-1)))
              //   (plus(ulo,times(dn,d)),
              //    plus(ulo,times(plus(dn,const(1)),d)),
              //    plus(ulo,times(dh,d)))
              // piece-wise linear, e.g. if (n < 18) 1 else 0
              case Def(DIf(Def(DLess(`n0`, up)), dx, dy))
                if !IRD.dependsOn(up, n0) =>
                val dn = plus(nhi,times(nlo,const(-1)))
                println(s"split range of $n0 at $up: dx=$dx dy=$dy ulo=$ulo nlo=$nlo nhi=$nhi")
                val (u0,u1,uhi) = break(ulo,nlo,up,dx)
                val (v0,v1,vhi) = break(uhi,up,nhi,dy)
                println(s"before ($u0,$v0), after ($u1,$v1)")
                val (r0,r1) = (iff(less(n0,up), u0, v0), iff(less(n0,up), u1, v1))
                IRD.printTerm(r0)
                IRD.printTerm(r1)
                (r0,r1,vhi)
              case Def(DLess(`n0`, up)) // short cut
                if !IRD.dependsOn(up, n0) =>
                val (u0,u1,uhi) = break(ulo,nlo,up,const(1))
                val (v0,v1,vhi) = break(uhi,up,nhi,const(0))
                (iff(less(n0,up), u0, v0), iff(less(n0,up), u1, v1), vhi)
              case _ =>

                val pp = poly(d)
                println("poly: " + pp)
                pp match {
                  case List(coeff0) =>
                    val d = coeff0
                    println(s"confirmed iterative loop, d = $d")
                    // before: ul + n * d
                    // after:  ul + (n+1) * d
                    val dn = plus(n0,times(nlo,const(-1)))
                    val dh = plus(nhi,times(nlo,const(-1)))
                    (plus(ulo,times(dn,d)),
                     plus(ulo,times(plus(dn,const(1)),d)),
                     plus(ulo,times(dh,d)))

                  case List(coeff0, coeff1) =>
                    println(s"found 2nd order polynomial: f'($n0)=$coeff1*$n0+$coeff0 -> f($n0)=$coeff1*$n0/2($n0+1)+$coeff0*$n0")

                    // f(n) = c1 * n/2*(n+1) + c0 * n + ul   <--- ul not added here but below
                    def eval(nX: GVal) =
                      plus(times(times(times(nX,plus(nX,const(-1))),const(0.5)), coeff1), times(nX, coeff0))

                    val r0 = eval(n0)
                    val r1 = eval(plus(n0,const(1)))
                    val rh = eval(nhi)

                    // sanity check that we get the same diff
                    IRD.printTerm(r0)
                    IRD.printTerm(r1)
                    val dd = plus(r1,times(r0, const(-1)))
                    IRD.printTerm(dd)
                    val pp2 = poly(dd)
                    println("poly2: " + pp2)
                    assert(pp == pp2)

                    (plus(ulo,r0), plus(ulo,r1), plus(ulo,rh))

                  case _ =>
                    println("giving up for term:")
                    IRD.printTerm(d)
                    throw fail
                }
            }

            try {
              val (u0,u1,uhi) = break(a,const(0),n0,d1)
              return (u0,u1)
            } catch {
              case `fail` =>
            }
          }

          // fall-through case
          println(s"recursive fun $fsym (init $a)")

          def wrapZero(x: GVal): GVal = x//iff(less(const(0), n0), x, a)

          (wrapZero(call(fsym,plus(n0,const(0)))),
           b1)//wrapZero(call(fsym,n0)))
      }


      // generate function definitions for recursive functions (even if not required)

      // b: loop body

      def lubfun(fsym: GVal, n0: GVal, b: GVal): GVal = b match {
        case Def(DMap(m2)) =>
          val m = (m2.keys) map { k => k -> lubfun(mkey(fsym,k),n0,select(b,k)) }
          val b1 = map(m.toMap)
          fun(fsym.toString, n0.toString, b1)
          call(fsym,n0)
        case _ =>
          fun(fsym.toString, n0.toString, b)
          call(fsym,n0)
      }


  }
