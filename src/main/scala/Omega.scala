package analysis

import scala.math._
import scala.util.Random
import scala.collection._

import CBase._
import CtoCFG._
import CFGtoEngine._
import CFrontend2._
import Test1._
import IRD._

object DebugOmg {
  val debug = false
}

import DebugOmg._

object Utils {

  private def gcd_aux(a: Int, b: Int): Int = {
    assert(a >= 0 && b >= 0)
    if (b == 0) a else gcd_aux(b, a % b)
  }

  def gcd(a: Int, b: Int): Int = {
    val a1 = if (a < 0) abs(a) else a
    val b1 = if (b < 0) abs(b) else b
    gcd_aux(a1, b1)
  }

  def gcd(ints: List[Int]): Int = {
    if (ints.length == 0) 1
    else if (ints.length == 1) gcd(ints.head, ints.head)
    else ints.reduce((x, y) => gcd(x, y))
  }

  def sign(x: Int): Int = {
    if (x > 0) 1
    else if (x < 0) -1
    else 0
  }

  def int_div(a: Int, b: Int): Int = {
    assert(b > 0)
    if (a > 0) a / b
    else -((-a + b - 1) / b)
  }

  /* This version is extracted from the C/C++ implementation of omega */
  def mod_hat2(a: Int, b: Int): Int = {
    assert(b > 0)
    val r = a - b * int_div(a, b)
    //if (r > -(r-b)) r - b
    if (r >= -(r-b)) r - b // a slightly change to make mod_hat behaves as the paper
    else r
  }

  /* This version follows the description of original paper */
  def mod_hat(a: Int, b: Int): Int = {
    assert(b > 0)
    if (a % b > b / 2) a % b
    else (a % b) - b
  }
}

trait Term {
  val coefficients: List[Int]
  val vars: List[String]

  override def toString(): String = {
    val s = coefficients.head.toString
    (coefficients.tail zip vars.tail).foldLeft(s)({
      case (acc, (c,v)) =>
        val cstr = if (c > 0) " + " + c.toString
                   else " - " + abs(c).toString
        val cvstr = cstr + v
        acc + cvstr
    })
  }
}

object Term {
  def newTerm(coefs: List[Int], variables: List[String]) = {
    new Term {
      val coefficients = coefs
      val vars = variables
    }
  }
}

object Constraint {
  val PConst = "_"

  def removeByIdx[T](lst: List[T], idx: Int): List[T] = {
    lst.take(idx) ++ lst.drop(idx+1)
  }

  def minWithIndex[T](lst: List[T])(implicit ordering: Ordering[T]): (T,Int) = {
    assert(lst.nonEmpty)
    lst.zipWithIndex.reduce[(T,Int)]({
      case ((minv,mini), (x,i)) => if (ordering.lt(x,minv)) (x,i) else (minv, mini)
    })
  }

  def removeZeroCoef(coefs: List[Int], vars: List[String]): (List[Int], List[String]) = {
    val cvpairs = for ((c, v) <- (coefs zip vars) if !(c == 0 && v != PConst)) yield (c, v)
    // TODO: may refactor this to only use one pass
    (cvpairs.map(_._1), cvpairs.map(_._2))
  }

  /* Combines like terms and reorder the variables alphabetically, also
   * removes variables whose coefficient is zero.
   * The constant term placed at the first position.
   */
  def reorder(coefficients: List[Int], vars: List[String]): (List[Int], List[String]) = {
    val g = (coefficients zip vars).groupBy(_._2).values.map({
      cvs => cvs.reduce((acc, cv) => (acc._1 + cv._1, cv._2))
    }).toList.sortWith(_._2 < _._2)
    removeZeroCoef(g.map(_._1), g.map(_._2))
  }

  def scale(coefficients: List[Int], x: Int): List[Int] = { coefficients.map(_ * x) }
}

import Term._
import Utils._
import Constraint._

trait Constraint[C <: Constraint[C]] extends Term {
  assert(coefficients.length == vars.length)
  assert(vars(0) == PConst)

  def normalize(): Option[Constraint[C]]

  /* negation returns a List of List of GEQs, which stands for
   * disjunction of conjunction of GEQs.
   */
  def negation(): List[List[GEQ]]

  def subst(x: String, term: Term): C

  def trivial: Boolean

  def getVars = vars.tail

  def hasVars = getVars.nonEmpty

  def getConstant = coefficients.head

  def getCoefficients = coefficients.tail

  def containsVar(x: String) = vars.contains(x)

  def getCoefficientByVar(x: String): Int = {
    coefficients(vars.indexOf(x))
  }

  def getVarByIdx(i: Int): String = { vars(i) }

  def removeVar(x: String): (List[Int], List[String]) = {
    removeVarByIdx(vars.indexOf(x))
  }

  def removeVarByIdx(idx: Int): (List[Int], List[String]) = {
    val newCoefs = removeByIdx(coefficients, idx)
    val newVars = removeByIdx(vars, idx)
    (newCoefs, newVars)
  }

  //TODO: better rename this function
  def _subst(x: String, term: Term): (List[Int], List[String]) = {
    if (!vars.contains(x)) {
      return (coefficients, vars)
    }
    val c = getCoefficientByVar(x)
    val (oldCoefs, oldVars) = removeVar(x)
    val newVars = term.vars
    val newCoefs = term.coefficients.map(_ * c)
    reorder(oldCoefs++newCoefs, oldVars++newVars)
  }

  /* Finds the minimum absolute value of coefficient, except the constant term.
   * Returns ((value, var) index).
   */
  def minCoef(): ((Int, String), Int) = {
    val (v, idx) = minWithIndex(coefficients.tail)(Ordering.by((x:Int) => abs(x)))
    ((v, getVarByIdx(idx+1)), idx+1)
  }

  def minCoefUnprotected(pvars: List[String]): ((Int, String), Int) = {
    val (v, idx) = minWithIndex(coefficients.tail.filter(!pvars.contains(_)))(Ordering.by((x:Int) => abs(x)))
    ((v, getVarByIdx(idx+1)), idx+1)
  }

  def noZeroCoef(): Boolean = { !coefficients.tail.contains(0) }
}

object EQ {
  def create(lhs: List[(Int, String)], rhs: List[(Int, String)]): EQ = {
    val (coefs, vars) = reorder(0::lhs.map(_._1)++scale(rhs.map(_._1), -1), PConst::lhs.map(_._2)++rhs.map(_._2))
    EQ(coefs, vars)
  }
}

/* Linear Equality: \Sigma a_i x_i = 0 where x_0 = 1,
 * Here always uses "_" stands for x_0.
 */
case class EQ(coefficients: List[Int], vars: List[String]) extends Constraint[EQ] {

  /* Normalize the coefficients, which makes the gcd of coefficients
   * is 1. If the constant term a_0 can not be evenly divided by g,
   * then there is no integer solution, returns None.
   * Also remove items whose coefficient is 0.
   */
  override def normalize(): Option[EQ] = {
    val g = gcd(coefficients.tail)
    if (coefficients.head % g == 0) {
      val coefs = coefficients.map(_ / g)
      // Also remove items whose coefficient is 0
      val (newCoefs, newVars) = removeZeroCoef(coefs, vars)
      Some(EQ(newCoefs, newVars))
    }
    else None
  }

  override def toString(): String = { super.toString + " = 0" }

  /* Decides whether an inequality trivially holds, i.e., not variable involves,
   * and constant term is equal than 0.
   */
  def trivial: Boolean = {
    vars.length == 1 && coefficients.length == 1 && coefficients.head == 0
  }

  /* Get the first atomic variable.
   * An atmoic variable has coefficient of 1 or -1.
   * Returns (index, var)
   */
  def getAtomicVar(pvars: List[String] = List()): Option[(String, Int)] = {
    for (((c,x), idx) <- (coefficients.tail zip vars.tail).zipWithIndex) {
      if (abs(c) == 1 && !pvars.contains(x)) return Some((x, idx+1))
    }
    return None
  }

  def getUnprotectedVars(pvars: List[String]): List[(Int, String)] = {
    (coefficients.tail zip vars.tail).filter({ case cv: (Int, String) => !pvars.contains(cv._2) })
  }

  /* Get the equation for an atomic variable x_k,
   * where x_k = a_i * x_i.
   * Returns a list of integers for a_i, and a list
   * of strings for x_i.
   */
  def getEquation(x: String): Term = {
    getEquation(vars.indexOf(x))
  }

  def getEquation(idx: Int): Term = {
    assert(idx != 0)
    assert(abs(coefficients(idx)) == 1)
    val (coefs, vars) = removeVarByIdx(idx)
    if (coefficients(idx) > 0) newTerm(coefs.map(_ * -1), vars)
    else newTerm(coefs, vars)
  }

  override def subst(x: String, term: Term): EQ = {
    val (c, v)= _subst(x, term)
    EQ(c, v)
  }

  def negation(): List[List[GEQ]] = {
    NEQ(coefficients, vars).toGEQ
  }
}

/* Linear Inequality: \Sigma a_i x_i >= 0 where x_0 = 1
 */
case class GEQ(coefficients: List[Int], vars: List[String]) extends Constraint[GEQ] {

  override def toString(): String = { super.toString + " >= 0" }

  /* Normalize the coefficients, which makes the gcd of coefficients
   * is 1. If the constant term a_0 can not be evenly divided by g,
   * then take floors of a_0/g, which tightens the inequality.
   * Also remove items whose coefficient is 0.
   */
  override def normalize(): Option[GEQ] = {
    val g = gcd(coefficients.tail)
    val coefs = if (coefficients.head % g == 0) { coefficients.map(_ / g) }
    else {
      //val a0 = coefficients.head / g
      val a0 = floor(coefficients.head.toDouble / g).toInt
      a0::coefficients.tail.map(_ / g)
    }
    val (newCoefs, newVars) = removeZeroCoef(coefs, vars)
    Some(GEQ(newCoefs, newVars))
  }

  /* Substitute a variable with a linear term, which the term is a list
   * of integers (coefficients) and a list of strings (variables).
   */
  override def subst(x: String, term: Term): GEQ = {
    val (c, v) = _subst(x, term)
    GEQ(c, v)
  }

  /* Check if two geqs are contradictory.
   * e.g.,
   * -2 + 2x + 3y >= 0,  0 - 2x - 3y >= 0 are contraWithory, but
   *  0 + 2x + 3y >= 0,  2 - 2x - 3y >= 0 are not.
   * -5 + 2x + 3y >= 0, -9 - 2x - 3y >= 0 are contraWithory, but
   *  9 + 2x + 3y >= 0, -5 - 2x - 3y >= 0 are not.
   */
  def contraWith(that: GEQ): Boolean = {
    assert(noZeroCoef && that.noZeroCoef)

    val thisConst = coefficients.head
    val thatConst = that.coefficients.head
    val coefss = coefficients.tail zip that.coefficients.tail
    // variables of two inequalities should be the same
    vars == that.vars &&
    // coefficients of two inequalities should be additive inversed
    coefss.foldLeft(true)({
      case (b, (c1,c2)) => b && abs(c1)==abs(c2) && (sign(c1)+sign(c2)==0)
    }) &&
    // constant term should be consistant
    (-thisConst) > thatConst
  }

  /* If two geqs can form a tight equality, then return the equality,
   * otherwise returns None.
   * e.g., given 2x + 3y >= 6 and 2x + 3y <= 6, returns 2x + 3y = 6.
   */
  def tighten(that: GEQ): Option[EQ] = {
    assert(noZeroCoef && that.noZeroCoef)

    val canMerge = (vars == that.vars) &&
      (coefficients zip that.coefficients).foldLeft(true)({
        case (b, (c1,c2)) => b && abs(c1)==abs(c2) && (sign(c1)+sign(c2)==0)
      })
    if (canMerge) Some(EQ(coefficients, vars)) else None
  }

  /* If two geqs can be simplified as one, or say one can be inferred
   * from another then returns Some(c), otherwise returns None
   * e.g., given x >= 5 and x >= 0, then return x >= 5
   * TODO: this requires two inequalities have the same coefficients,
   *       need to think about other cases
   */
  def subsume(that: GEQ): Option[GEQ] = {
    assert(noZeroCoef && that.noZeroCoef)

    val thisConst = coefficients.head
    val thatConst = that.coefficients.head
    if ((vars == that.vars) && (coefficients.tail == that.coefficients.tail))
      Some(GEQ(min(thisConst, thatConst)::coefficients.tail, vars))
    else None
  }

  /* Decides whether an inequality trivially holds, i.e., not variable involves,
   * and constant term is greater or equal than 0.
   */
  def trivial: Boolean = {
    vars.length == 1 && coefficients.length == 1 && coefficients.head >= 0
  }

  /* Join two inequalities and eliminate variable x.
   * The two inequalities should be a pair of upper bound and
   * lower bound of x, otherwise return None.
   */
  def join(that: GEQ, x: String): Option[GEQ] = {
    assert(containsVar(x) && that.containsVar(x))
    assert(noZeroCoef && that.noZeroCoef)

    val (thisCoefs, thisVars) = this.removeVar(x)
    val (thatCoefs, thatVars) = that.removeVar(x)
    val thisXCoef = this.getCoefficientByVar(x)
    val thatXCoef = that.getCoefficientByVar(x)

    assert(thisXCoef != 0 && thatXCoef != 0)

    val (newCoefs, newVars) = if (thatXCoef < 0 && thisXCoef > 0) {
      /* this is a lower bound; that is an upper bound */
      reorder(scale(thisCoefs, -1*thatXCoef)++scale(thatCoefs, thisXCoef), thisVars++thatVars)
    } else if (thisXCoef < 0 && thatXCoef > 0) {
      /* this is an upper bound; that is a lower bound */
      reorder(scale(thisCoefs, thatXCoef)++scale(thatCoefs, -1*thisXCoef), thisVars++thatVars)
    } else return None

    Some(GEQ(newCoefs, newVars))
  }

  def tightJoin(that: GEQ, x: String): Option[GEQ] = {
    assert(containsVar(x) && that.containsVar(x))
    assert(noZeroCoef && that.noZeroCoef)

    val (thisCoefs, thisVars) = this.removeVar(x)
    val (thatCoefs, thatVars) = that.removeVar(x)
    val thisXCoef = this.getCoefficientByVar(x)
    val thatXCoef = that.getCoefficientByVar(x)

    assert(thisXCoef != 0 && thatXCoef != 0)

    val m = (thisXCoef - 1) * (thatXCoef - 1)
    val (newCoefs, newVars) = if (thatXCoef < 0 && thisXCoef > 0) {
      /* this is an upper bound; that is a lower bound */
      reorder(m::scale(thisCoefs, -1*thatXCoef)++scale(thatCoefs, thisXCoef), PConst::thisVars++thatVars)
    } else if (thisXCoef < 0 && thatXCoef > 0) {
      /* this is a lower bound; that is an upper bound */
      reorder((-m)::scale(thisCoefs, thatXCoef)++scale(thatCoefs, -1*thisXCoef), PConst::thisVars++thatVars)
    } else return None

    Some(GEQ(newCoefs, newVars))
  }

  def isLowerBound(x: String): Boolean = {
    val c = getCoefficientByVar(x)
    assert(c != 0)
    containsVar(x) && c > 0
  }

  def isUpperBound(x: String): Boolean = {
    val c = getCoefficientByVar(x)
    assert(c != 0)
    containsVar(x) && c < 0
  }

  def negation(): List[List[GEQ]] = {
    List(LT(coefficients, vars).toGEQ)
  }
}

case class GT(coefficients: List[Int], vars: List[String]) {
  /* Transforms \Sigma a_i x_i > 0 to \Sigma a_i x_i >= 1
   */
  def toGEQ: List[GEQ] = {
    val (newCoefs, newVars) = reorder(-1::coefficients, PConst::vars)
    List(GEQ(newCoefs, newVars))
  }

  def negation: List[List[GEQ]] = {
    List(LEQ(coefficients, vars).toGEQ)
  }
}

object LT {
  def create(lhs: List[(Int, String)], rhs: List[(Int, String)]): LT = {
    val (coefs, vars) = reorder(0::lhs.map(_._1)++scale(rhs.map(_._1), -1), PConst::lhs.map(_._2)++rhs.map(_._2))
    LT(coefs, vars)
  }

}

case class LT(coefficients: List[Int], vars: List[String]) {
  /* Transforms \Sigma a_i x_i < 0 to \Sigma -1 * a_i x_i >= 1
   */
  def toGEQ: List[GEQ] = {
    val (newCoefs, newVars) = reorder(-1::scale(coefficients, -1), PConst::vars)
    List(GEQ(newCoefs, newVars))
  }

  def negation: List[List[GEQ]] = {
    List(List(GEQ(coefficients, vars)))
  }
}

case class LEQ(coefficients: List[Int], vars: List[String]) {
  /* Transforms \Sigma a_i x_i <= 0 to \Sigma -1 * a_i x_i >= 0
   */
  def toGEQ: List[GEQ] = {
    List(GEQ(scale(coefficients, -1), vars))
  }

  def negation: List[List[GEQ]] = {
    List(GT(coefficients, vars).toGEQ)
  }
}

case class NEQ(coefficients: List[Int], vars: List[String]) {
  /* Transforms \Sigma a_i x_i =/= 0 to \Sigma a_i x_i >= 1 or \Sigma a_i x_i <= -1.
   * The result is a disjunction of conjunction of GEQs.
   */
  def toGEQ: List[List[GEQ]] = {
    val (coefs1, vars1) = reorder(-1::coefficients, PConst::vars)
    val (coefs2, vars2) = reorder(-1::scale(coefficients, -1), PConst::vars)
    List(List(GEQ(coefs1, vars1)), List(GEQ(coefs2, vars2)))
  }

  def negation: EQ = {
    EQ(coefficients, vars)
  }
}

object Problem {
  var varIdx = 0
  val greeks = List("α", "β", "γ", "δ", "ϵ", "ζ", "η", "θ", "ι", "κ", "λ", "μ",
                    "ν", "ξ", "ο", "π", "ρ", "σ", "τ", "υ", "ϕ", "χ", "ψ", "ω")

  def partition(cs: List[Constraint[_]]): (List[EQ], List[GEQ]) = {
    val (eqs, geqs) = cs.partition(_.isInstanceOf[EQ])
    (eqs.asInstanceOf[List[EQ]], geqs.asInstanceOf[List[GEQ]])
  }

  def generateNewVar(): String = {
    val idx = varIdx
    varIdx += 1

    if (idx < greeks.length) greeks(idx)
    else if (idx < (greeks.length * greeks.length)) {
      val n = idx / greeks.length
      val m = idx % greeks.length
      greeks(n) + m
    }
    else { greeks(0) + idx }
  }

  val TRUE = EQ(List(0), List(PConst))
  val FALSE = EQ(List(1), List(PConst))

  val PTRUE = Problem(List(TRUE))
  val PFALSE = Problem(List(FALSE))
}

import Problem._

case class Subst(x: String, term: Term) {
  override def toString: String = {
    x + " = " + term
  }
}

case class Problem(cs: List[Constraint[_]], pvars: List[String] = List(), substs: List[Subst] = List()) {
  val (eqs, geqs) = partition(cs)

  def getEqs= eqs

  def getGeqs = geqs

  def hasEq = eqs.size != 0

  def hasProtectedVars = pvars.nonEmpty

  def getVars: Set[String] = cs.map(_.getVars).flatten.toSet

  val numVars = cs.map(_.getVars).flatten.toList.size

  def hasMostOneVar = cs.map(_.getVars).flatten.toList.size <= 1

  def containsVar(x: String): Boolean =
    cs.foldLeft(false)((acc, c) => acc || c.containsVar(x))

  override def toString(): String = {
    if (substs.isEmpty) {
      "{ " + cs.mkString(", ") + " }"
    }
    else {
      "{ " + cs.mkString(", ")  + "\n" + substs.mkString(", ") + " }"
    }
  }

  /* Returns a disjunction of problems */
  def negation(): List[Problem] = {
    val negs: List[List[GEQ]] = cs.map(_.negation).flatten
    negs.map(Problem(_))
  }

  /* A constraint is normalized if all coefficients are integers, and the
   * greatest common divisor of the coefficients (not including a_0) is 1.
   */
  def normalize(): Option[Problem] = {
    val newCs = mutable.Set[Constraint[_]]()
    for (c <- cs) {
      if (c.hasVars) {
        c.normalize match {
          case Some(cn) => newCs += cn
          case None => return None
        }
      }
      else { if (!c.trivial) return None }
    }
    Some(copy(newCs.toList))
  }

  /* Elminates the equalities in the problem, returns a new problem that
   * not contains equalities.
   */
  def elimEq(): Option[Problem] = {

    def eliminate(eqs: List[EQ], geqs: List[GEQ], substs: List[Subst]): Option[Problem] = {
      if (eqs.nonEmpty) {
        val eq = eqs.head
        if (debug) println("current constraints:")
        if (debug) { for (eq <- (eqs++geqs)) { println(s"  $eq") } }

        if (eq.vars.length == 1) {
          if (eq.trivial) return eliminate(eqs.tail, geqs, substs)
          else return None
        }

        val unpVars = eq.getUnprotectedVars(pvars)
        if (debug) println(s"unprotected vars: $unpVars")

        val g = if (unpVars.isEmpty) 0 else gcd(unpVars.map(_._1))
        if (g <= 1) {
          /* If unpVars is empty(g == 0), there is no unprotected variables
           * in this equality, but we have to eliminate the equality anyway.
           * Just eliminate as normal, but need to record the substitution.
           * If g == 1 then do standard elimination on an unprotected variable.
           */
          val variable = if (unpVars.isEmpty) eq.getAtomicVar() else eq.getAtomicVar(pvars)
          variable match {
            case Some((x, idx)) =>
              val term = eq.getEquation(idx)
              val newSubsts = if (g == 0) {
                Subst(x,term)::substs
              } else { substs }
              /* Debug */
              if (debug) {
                println(s"[g=$g]choose xk: $x")
                println(s"[g=$g]subst: $x = ${term}")
              }
              /* Debug */
              eliminate(eqs.tail.map(_.subst(x, term)), geqs.map(_.subst(x, term)), newSubsts)
            case None =>
              val ((ak, xk), idx) = eq.minCoef
              val sign_ak = sign(ak)
              val m = abs(ak) + 1
              val v = generateNewVar
              val (coefs, vars) = eq.removeVarByIdx(idx)
              val newCoefs = coefs.map((c: Int) => sign_ak * (mod_hat2(c, m))) ++ List(-1*sign_ak*m)
              val newVars = vars ++ List(v)
              val substTerm = newTerm(newCoefs, newVars)

              val newSubsts = if (g == 0) {
                Subst(xk,substTerm)::substs
              } else { substs }

              /* Debug */
              if (debug) {
                println(s"[g=$g]choose ak: $ak, xk: $xk")
                println(s"[g=$g]subst: $xk = ${substTerm}")
              }
              /* Debug */

              eliminate(eq.subst(xk, substTerm).normalize.get::eqs.tail.map(_.subst(xk, substTerm)),
                        geqs.map(_.subst(xk, substTerm)), newSubsts)
          }

        }
        else {
          val modCoefs = eq.coefficients.head::eq.coefficients.tail.map(mod_hat2(_, g))
          val newVar = generateNewVar
          val (newCoefs, newVars) = reorder(-1*g::modCoefs, newVar::eq.vars)
          val newEQ = EQ(newCoefs, newVars)
          if (debug) println(s"[g=$g]add new eq: $newEQ")
          Problem(newEQ::(eqs.tail)++geqs, newVar::pvars, substs).elimEq
        }
      }
      else { Some(Problem(geqs, pvars, substs)) }
    }

    eliminate(getEqs, getGeqs, List())
  }

  /* Returns None if found contradictions,
   * Otherwise return a problem contains simpler/tigher constraints
   */
  def reduce(): Option[Problem] = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)

    //Use Set to remove identical items
    val cons = mutable.Set[Constraint[_]]()
    val junks = mutable.Set[Constraint[_]]()

    for (Seq(c1, c2) <- getGeqs.combinations(2)) {
      if (c1.contraWith(c2)) {
        if (debug) println(s"contra: $c1, $c2")
        return None
      }
      c1.subsume(c2) match {
        case Some(c) =>
          if (debug) println(s"subsume: $c1, $c2 => $c")
          cons += c
          junks += (if (c == c1) c2 else c1)
        case None => c1.tighten(c2) match {
          case Some(c) =>
            if (debug) println(s"tighten: $c1, $c2 => $c")
            cons += c
            junks += c1 += c2
          case None => cons += c1 += c2
        }
      }
    }

    // println(s"constraints: $cons")
    // println(s"junks: $junks")
    Some(this.copy((cons -- junks).toList))
  }

  def allTrivial(): Boolean = cs.foldLeft(true)((b, c) => b && c.trivial)

  def upperBounds(x: String) = { getGeqs.filter(_.isUpperBound(x)) }

  def lowerBounds(x: String) = { getGeqs.filter(_.isLowerBound(x)) }

  def hasIntSolutions(): Boolean = {
    normalize match {
      case Some(p) if p.cs.isEmpty => true
      case Some(p) if p.hasEq =>
        p.elimEq match {
          case Some(p) => p.hasIntSolutions
          case None => false
        }
      case Some(p) if p.hasMostOneVar => return p.reduce.nonEmpty
      case Some(p) =>
        p.reduce match {
          case Some(p) if p.hasEq =>
            p.elimEq match {
              case Some(p) => p.hasIntSolutions
              case None => false
            }
          case Some(p) if p.numVars > 1 =>
            val x0 = p.chooseVar()
            val realSet = p.realShadowSet(x0)
            val darkSet = p.darkShadowSet(x0)
            if (realSet == darkSet) { p.copy(realSet.toList).hasIntSolutions } // exact elimination
            else if (! p.copy(realSet.toList).hasIntSolutions) false
            else if (p.copy(darkSet.toList).hasIntSolutions) true       // inexact elimination
            else {
              /* real shadow has int solution; but dark shadow does not */
              val x = p.chooseVarMinCoef()
              /* m is the most negative coefficient of x */
              val m = (for (c <- p.cs if c.containsVar(x)) yield {
                c.getCoefficientByVar(x)
              }).sorted.head

              for (lb <- p.lowerBounds(x)) {
                val coefx = lb.getCoefficientByVar(x)
                val j = (floor(abs(m * coefx) - abs(m) - coefx) / abs(m)).toInt
                if (debug) println(s"### x: $x m: $m, j: $j, coefx: $coefx ###")
                for (j <- 0 to j) {
                  val (newCoefs, newVars) = reorder((-1*j)::lb.coefficients, PConst::lb.vars)
                  if (p.copy(EQ(newCoefs, newVars)::p.cs).hasIntSolutions) return true
                }
              }
              // TODO: There is another step desribed in conference paper but not in journal paper,
              //       it is may not necessay, but need to carefully think about it
              false
            }
          case Some(p) => p.hasIntSolutions
          case None => false
        }
      case None => false
    }
  }

  /* Split the inequalities list into two, the first list contains
   * variable x, while the second one not.
   */
  private def partitionGEQs(x: String): (List[GEQ], List[GEQ]) = {
    geqs.partition(_.containsVar(x))
  }

  /* We choose the variable that minimizes the number of constraints
   * resulting from the combination of upper and lower bounds, which
   * is the variable who has minimum frequency.
   * Used for getting real shadow.
   */
  private def chooseVar(): String = {
    val allVars = cs.map(_.getVars).flatten.groupBy(x=>x).toSeq
                    .sortBy(_._2.length)
    allVars.head._1
  }

  /* Same as method chooseVar, but the variable is not contained
   * in protected variables.
   */
  private def chooseUnprotectedVar(): Option[String] = {
    val allVars = cs.map(_.getVars).flatten.groupBy(x=>x).toSeq
                    .sortBy(_._2.length)
                    .filter(!pvars.contains(_))
    if (allVars.nonEmpty) Some(allVars.head._1)
    else None
  }

  /* Perform a classical Fourier-Motzkin variable elimination,
   * and obtain a new constraint set called real shadow.
   * See section 2.3.1 of paper The Omega Test in CACM.
   */
  def realShadow(): Problem = { copy(realShadowSet.toList) }

  def realShadowSet(): mutable.Set[Constraint[_]] = {
    val x = chooseVar()
    if (debug) println(s"real shadow chooses var: $x")
    realShadowSet(x)
  }

  def realShadowSet(x: String): mutable.Set[Constraint[_]] = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)

    val (ineqx, ineqnox) = partitionGEQs(x)
    val cons = mutable.Set[Constraint[_]]()
    cons ++= ineqnox

    for (Seq(ineq1, ineq2) <- ineqx.combinations(2)) {
      ineq1.join(ineq2, x) match {
        case Some(ineq) if ineq.trivial => /* trivially holds, no need to add to new constraints */
        case Some(ineq) =>
          if (debug) println(s"real shadow eliminating [$x] $ineq1, $ineq2 => $ineq")
          cons += ineq
        case None =>
          /* In this case, ineq1 and ineq2 are not an upper/lower bound pair,
           * presumably should not happen since the reduce/subsume should
           * be able to eliminate redundant constraints.
           */
      }
    }
    //println(s"${cons.size}, ${getGeqs.size}")
    cons
  }

  /* Choose the variable that has coefficient as close to zero as possible.
   * Used for getting dark shadow.
   */
  def chooseVarMinCoef(): String = {
    val ((c, x), _) = minWithIndex(cs.map(_.minCoef._1))(Ordering.by({
      case x: (Int,String) => abs(x._1)
    }))
    x
  }

  /* Same as chooseVarMinCoef, but the variable is not contained in
   * protected variables.
   */
  def chooseUnprotectedVarMinCoef(): Option[String] = {
    val coefVars = cs.map(_.minCoef._1).filter({ case cv: (Int,String) => !pvars.contains(cv._2) })
    if (coefVars.nonEmpty) {
      val ((c, x), _) = minWithIndex(coefVars)(Ordering.by({
        case x: (Int,String) => abs(x._1)
      }))
      Some(x)
    }
    else None
  }

  def darkShadow(): Problem = { copy(darkShadowSet.toList) }

  def darkShadowSet(): mutable.Set[Constraint[_]] = {
    var x = chooseVarMinCoef()
    if (debug) println(s"dark shadow chooses var: $x")
    darkShadowSet(x)
  }

  /* Perform a variant Fourier-Motzkin variable elimination.
   */
  def darkShadowSet(x: String): mutable.Set[Constraint[_]] = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)

    val (ineqx, ineqnox) = partitionGEQs(x)
    val cons = mutable.Set[Constraint[_]]()
    cons ++= ineqnox

    for (Seq(ineq1, ineq2) <- ineqx.combinations(2)) {
      ineq1.tightJoin(ineq2, x) match {
        case Some(ineq) if ineq.trivial =>
        case Some(ineq) =>
          if (debug) println(s"dark shadow eliminating [$x] $ineq1, $ineq2 => $ineq")
          cons += ineq
        case None =>
      }
    }

    cons
  }

  /* Simplify the problem with protected variables, returns Some(p)
   * if the problem has integer solution where `p` is the simplified form;
   * returns None if the problem has no integer solutions.
   */
  def simplify(): Option[Problem] = {
    if (debug) {
      println(s"protected variables: $pvars")
      println(s"problem variables: ${getVars}")
    }

    normalize match {
      case Some(p) if p.getVars.subsetOf(p.pvars.toSet) =>
        if (p.hasIntSolutions) Some(p) else None
      case Some(p) if p.hasEq =>
        p.elimEq match {
          case Some(p) => p.simplify
          case None => None
        }
      case Some(p) =>
        p.reduce match {
          case Some(p) if p.hasEq =>
            p.elimEq match {
              case Some(p) => p.simplify
              case None => None
            }
          case Some(p) if p.numVars > 1 =>
            val x0 = p.chooseVar()
            val realSet = p.realShadowSet(x0)
            val darkSet = p.darkShadowSet(x0)
            if (realSet == darkSet) { p.copy(realSet.toList).simplify } // exact elimination
            else if (p.copy(realSet.toList).simplify.isEmpty) None
            else {
              val pd = p.copy(darkSet.toList).simplify
              if (pd.nonEmpty) pd
              else {
                /* real shadow has int solution; but dark shadow does not */
                val x = p.chooseVarMinCoef()
                /* m is the most negative coefficient of x */
                val m = (for (c <- p.cs if c.containsVar(x)) yield {
                  c.getCoefficientByVar(x)
                }).sorted.head

                for (lb <- p.lowerBounds(x)) {
                  val coefx = lb.getCoefficientByVar(x)
                  val j = (floor(abs(m * coefx) - abs(m) - coefx) / abs(m)).toInt
                  if (debug) println(s"### x: $x m: $m, j: $j, coefx: $coefx ###")
                  for (j <- 0 to j) {
                    val (newCoefs, newVars) = reorder((-1*j)::lb.coefficients, PConst::lb.vars)
                    val newP = p.copy(EQ(newCoefs, newVars)::p.cs).simplify
                    if (newP.nonEmpty) return newP
                  }
                }
                None
              }
            }
          case Some(p) => p.simplify
          case None => None
        }
      case None => None
    }
  }

  def simplify(pvars: List[String]): Option[Problem] = {
    Problem(cs, pvars).simplify
  }

  def implies(p: Problem): Boolean = {
    if (hasIntSolutions) return Problem(cs++p.cs).hasIntSolutions
    true
  }
}

abstract class OStruct {
  def negation: OStruct
}

case class OProb(p: Problem) extends OStruct {
  override def toString: String = { p.toString }
  override def negation: OStruct = {
    val negs = p.negation.map(OProb(_))
    if (negs.length <= 1) negs(0)
    else negs.reduceLeft(((acc: OStruct, x) => ODisj(acc, x)))
  }
}

case class OConj(lhs: OStruct, rhs: OStruct) extends OStruct {
  override def toString: String = {
    s"($lhs && $rhs)"
  }

  override def negation: OStruct = {
    ODisj(lhs.negation, rhs.negation)
  }
}

case class ODisj(lhs: OStruct, rhs: OStruct) extends OStruct {
  override def toString: String = {
    s"($lhs || $rhs)"
  }

  override def negation: OStruct = {
    OConj(lhs.negation, rhs.negation)
  }
}

case class OImplies(cnd: OStruct, thn: OStruct) extends OStruct {
  override def toString: String = {
    cnd.toString + " ==> " + thn.toString
  }

  override def negation: OStruct = {
    val negCnd = cnd.negation
    OConj(negCnd, thn)
  }
}

object Omega {
  def verify(os: OStruct, const: List[OProb] = List()): Boolean = {
    def inject(os: OStruct, extCs: List[Constraint[_]]): OStruct = {
      os match {
        case OProb(p) => OProb(p.copy(p.cs++extCs))
        case OConj(lhs, rhs) => OConj(inject(lhs, extCs), inject(rhs, extCs))
        case ODisj(lhs, rhs) => ODisj(inject(lhs, extCs), inject(rhs, extCs))
        case OImplies(cnd, thn) => OImplies(inject(cnd, extCs), inject(thn, extCs))
      }
    }
    val extCs: List[Constraint[_]] = const.flatMap(_.p.cs)
    if (debug) println(s"Omega query $os under $const")
    for (p <- flatten(inject(os, extCs))) {
      val result = p.hasIntSolutions
      if (debug) println(s"  verifying $p[$result]")
      if (result) return true
    }
    return false
  }

  def flatten(os: OStruct): List[Problem] = {
    os match {
      case OProb(p) => List(p)
      case OConj(lhs, rhs) =>
        val lhsP = flatten(lhs)
        val rhsP = flatten(rhs)
        (for (l <- lhsP; r <- rhsP) yield {
          Problem(l.cs ++ r.cs)
        }).toList
      case ODisj(lhs, rhs) =>
        flatten(lhs) ++ flatten(rhs)
      case OImplies(cnd, thn) =>
        /*
        flatten(cnd).flatMap(_.negation) ++
        (for (cp <- flatten(cnd); tp <- flatten(thn)) yield {
          Problem(cp.cs ++ tp.cs)
        }).toList
        */
        val cndP = flatten(cnd)
        (for (cp <- cndP; thnP <- flatten(thn)) yield {
          if (cp.hasIntSolutions) List(Problem(cp.cs ++ thnP.cs))
          else cp.negation
        }).flatten
    }
  }

  def verify_aux(os: OStruct, accCs: List[Constraint[_]] = List()): (Boolean, List[Constraint[_]]) = {
    os match {
      case OProb(p) =>
        val newP = p.copy(p.cs++accCs)
        if (newP.hasIntSolutions) (true, newP.cs)
        else (false, accCs)
      case OConj(lhs, rhs) =>
        val (lhsB, lhsCS) = verify_aux(lhs, accCs)
        if (lhsB) verify_aux(rhs, lhsCS)
        else verify_aux(rhs, accCs)
      case ODisj(lhs, rhs) =>
        val (lhsB, lhsCS) = verify_aux(lhs, accCs)
        if (lhsB) (lhsB, lhsCS)
        else verify_aux(rhs, accCs)
      case OImplies(cnd, thn) =>
        val (cndB, cndCs) = verify_aux(cnd, accCs)
        if (cndB) verify_aux(thn, cndCs)
        else (true, accCs)
    }
  }

  /*
  def translate(e: GVal): OStruct = {
    e match {
      case GConst(1) => OProb(PTRUE)
      case GConst(0) => OProb(PFALSE)
      case GRef(x) if x.endsWith("?") => translateBoolExpr(e)
      case GRef(s) => findDefinition(s) match {
        case Some(d) => translate(d)
        case None => println(s"Missing variable: $s"); ???
      }
      case _ => println(s"Missing $e"); ???
    }
  }

  def translate(e: Def): OStruct = {
    e match {
      case DIf(cnd, thn, els) =>
        val cndProb = translateBoolExpr(cnd)
        val thnProb = translate(thn)
        val elsProb = translate(els)
        OConj(OImplies(cndProb, thnProb),
              OImplies(cndProb.negation, elsProb))
      case le: DLess => translateBoolExpr(le)
      case eq: DEqual => translateBoolExpr(eq)
      case n: DNot => translateBoolExpr(n)
      case m: DTimes => translateBoolExpr(m)
      case _ => println(s"Missing $e"); ???
    }
  }
  */

  def translateBoolExpr(e: GVal): OStruct = {
    e match {
      case GError => OProb(PFALSE)
      case GConst(1) => OProb(PTRUE)
      case GConst(0) => OProb(PFALSE)
      case GRef(x) if x.endsWith("?") => OProb(Problem(List(EQ(List(-1, 1), List(PConst, x))))) // x == 1
      case GRef(x) => findDefinition(x) match {
        case Some(DMap(m)) => translateBoolExpr(m(GConst("$value")))
        case Some(d) => translateBoolExpr(d)
        case None => println(s"Missing variable: $x"); ???
      }
    }
  }

  def translateBoolExpr(e: Def): OStruct = {
    e match {
      case DLess(x, y) =>
        val lhs = translateArithExpr(x)
        val rhs = translateArithExpr(y)
        OProb(Problem(LT.create(lhs, rhs).toGEQ))
      case DEqual(x, y) =>
        val lhs = translateArithExpr(x)
        val rhs = translateArithExpr(y)
        OProb(Problem(List(EQ.create(lhs, rhs))))
      case DNot(x) => negBoolExpr(x) //TODO need test this case
      case DTimes(x, y) => OConj(translateBoolExpr(x), translateBoolExpr(y))
      case DIf(cnd, thn, els) =>
        val cndProb = translateBoolExpr(cnd)
        val thnProb = translateBoolExpr(thn)
        val elsProb = translateBoolExpr(els)
        //OConj(OImplies(cndProb, thnProb),
        ODisj(OConj(cndProb, thnProb),
              OConj(cndProb.negation, elsProb))
      case _ => println(e); ???
    }
  }

  def negBoolExpr(e: GVal): OStruct = {
    e match {
      case GConst(1) => OProb(PFALSE)
      case GConst(0) => OProb(PTRUE)
      case GRef(x) if x.endsWith("?") =>
        val geqs = NEQ(List(-1, 1), List(PConst, x)).toGEQ
        assert(geqs.length == 2)
        ODisj(OProb(Problem(geqs(0))), OProb(Problem(geqs(1)))) //x =/= 1
      case GRef(x) => findDefinition(x) match {
        case Some(DMap(m)) => negBoolExpr(m(GConst("$value")))
        case Some(d) => negBoolExpr(d)
        case None => println(s"Missing variable: $x"); ???
      }
    }
  }

  def negBoolExpr(e: Def): OStruct = {
    e match {
      case DLess(x, y) =>
        val lhs = translateArithExpr(x)
        val rhs = translateArithExpr(y)
        val neg = LT.create(lhs, rhs).negation
        assert(neg.length == 1)
        OProb(Problem(neg(0)))
      case DEqual(x, y) =>
        val lhs = translateArithExpr(x)
        val rhs = translateArithExpr(y)
        val neg = EQ.create(lhs, rhs).negation
        assert(neg.length == 2)
        ODisj(OProb(Problem(neg(0))), OProb(Problem(neg(1))))
      case DNot(x) => translateBoolExpr(x)
      case DTimes(x, y) =>
        val lhs = translateBoolExpr(x)
        val rhs = translateBoolExpr(y)
        OConj(lhs, rhs).negation
      case DIf(cnd, thn, els) =>
        val cndProb = negBoolExpr(cnd)
        val thnProb = negBoolExpr(thn)
        val elsProb = negBoolExpr(els)
        //OConj(OImplies(cndProb, thnProb),
        OConj(ODisj(cndProb, thnProb),
              ODisj(cndProb.negation, elsProb))
      case _ => println(e); ???
    }
  }

  def translateArithExpr(e: GVal): List[(Int, String)] = {
    e match {
      case GConst(n: Int) => List((n, PConst))
      case GRef(x) if x.endsWith("?") => List((1, x))
      case GRef(x) => findDefinition(x) match {
        case Some(gval) => translateArithExpr(gval)
        case None => println(s"Missing variable $x"); ???
      }
      case _ => println(s"Missing $e"); ???
    }
  }

  def translateArithExpr(e: Def): List[(Int, String)]= {
    e match {
      case DPlus(x, y) => translateArithExpr(x) ++ translateArithExpr(y)
      case DTimes(GConst(x: Int), GConst(y: Int)) => List(((x*y), PConst))
      case DTimes(GConst(x: Int), y) =>
        val rhs = translateArithExpr(y)
        rhs.map({ case t: (Int,String) => (t._1 * x, t._2) })
      case DTimes(x, GConst(y: Int)) =>
        val lhs = translateArithExpr(x)
        lhs.map({ case t: (Int,String) => (t._1 * y, t._2) })
      case DTimes(GRef(x), GRef(y)) if (x.endsWith("?") && y.endsWith("?")) =>
        // TODO: two variables multiplication
        // Idea: Instantiate one variable within its constraint, bounded check if we
        //       can have integer solutions, if found one, then return yes, otherwise
        //       check other concrete number within its constraint until bound met.
        // Idea: If we know x > 1, then could infer that x^2 > 1
        //       If we know x > n && y > m (n>0&&m>0), then could infer that x*y > n*m
        println(s"A Missing $e")
        List((1, s"$x*$y"))   //FIXME
      case DCall(f, x) =>
        println(s"B Missing $e")
        List((1, s"$f($x)")) //FIXME
      case DFixIndex(_, _) => ???
      case _ => println(s"C Missing $e"); ??? // FIXME
    }
  }
}

object OmegaTest {
  def test() {
    println("Omega Test")

    println("3 / 2 = " + Utils.int_div(3, 2))
    println("5 / 2 = " + Utils.int_div(5, 2))
    println("-5 / 2 = " + Utils.int_div(-5, 2))

    println("3 mod_hat2 2 = " + Utils.mod_hat2(3, 2))
    println("5 mod_hat2 2 = " + Utils.mod_hat2(5, 2))
    println("-5 mod_hat2 2 = " + Utils.mod_hat2(-5, 2))

    println("12 mod_hat2 8 = " + Utils.mod_hat2(12, 8))
    println("12 mod_hat 8 = " + Utils.mod_hat(12, 8))

    ///////////////////////////////

    val eq1 = EQ(List(1, 2, -3),
                 List("_", "a", "b"))
    val eq2 = EQ(List(3, 1, 5),
                 List("_", "b", "a"))
    val p1 = Problem(List(eq2, eq1))
    println(p1)
    //val p1elim = p1.elimEq
    //println("after elimination: " + p1elim)

    ///////////////////////////////

    val eq3 = EQ(List(-17, 7, 12, 31), List(PConst, "x", "y", "z"))
    val eq4 = EQ(List(-7,  3, 5,  14), List(PConst, "x", "y", "z"))

    val p2 = Problem(List(eq3, eq4)).normalize.get
    println(p2)
    val p2elim = p2.elimEq
    println(s"eq eliminated: $p2elim")

    val ineq1 = GEQ(List(-1, 1), List(PConst, "x"))
    val ineq2 = GEQ(List(40, -1), List(PConst, "x"))
    //println(ineq2.normalize.get)
    val ineq3 = GEQ(List(50, 1), List(PConst, "y"))
    val ineq4 = GEQ(List(50, -1), List(PConst, "y"))
    val p3 = Problem(List(eq3, eq4, ineq1, ineq2, ineq3, ineq4))
    println(p3)

    val p3elim = p3.elimEq.get.normalize.get
    val p3reduced = p3elim.reduce.get
    val p3ans = p3.hasIntSolutions
    assert(p3ans)

    println(s"p3 has integer solutions: ${p3ans}")

    val ineq5 = GEQ(List(11, 13), List(PConst, "a")).normalize.get
    println(ineq5)
    val ineq6 = GEQ(List(28, -13), List(PConst, "a")).normalize.get
    println(ineq6)

    ///////////////////////////////

    val ineq7 = GEQ(List(-2, 3, 5), List(PConst, "x", "y"))
    val ineq8 = GEQ(List(0, -3,-5), List(PConst, "x", "y"))

    println(ineq7.contraWith(ineq8))

    assert(GEQ(List(-5, 2, 3), List(PConst, "a", "b"))
              .contraWith(GEQ(List(-9, -2, -3), List(PConst, "a", "b"))))

    assert(!GEQ(List(9, 2, 3), List(PConst, "a", "b"))
               .contraWith(GEQ(List(-5, -2, -3), List(PConst, "a", "b"))))

    assert(!GEQ(List(0, 2, 3), List(PConst, "a", "b"))
                .contraWith(GEQ(List(2, -2, -3), List(PConst, "a", "b"))))


    ///////////////////////////////

    println(s"can be merged: ${GEQ(List(-6, 2, 3), List(PConst, "a", "b"))
                        .tighten(GEQ(List(6, -2, -3), List(PConst, "a", "b")))}")

    val p4 = Problem(List(GEQ(List(-6, 2, 3), List(PConst, "a", "b")),
                          GEQ(List(6, -2, -3), List(PConst, "a", "b")),
                          GEQ(List(-5, 2, 3), List(PConst, "a", "c")),
                          GEQ(List(-10, 2, 3), List(PConst, "a", "c"))))
    println(p4)
    val p4reduced = p4.reduce.get
    println(p4reduced)

    println(s"num of vars: ${p4reduced.numVars}")

    ///////////////////////////////

    val ineq9 = GEQ(List(0, 3, 2), List(PConst, "x", "y"))
    val ineq10 = GEQ(List(5, -2, 4), List(PConst, "x", "y"))
    println(ineq9.join(ineq10, "x")) // 15 + 16y >= 0
    println(ineq10.join(ineq9, "x")) // 15 + 16y >= 0

    println(GEQ(List(-3, 1), List(PConst, "x")).join(GEQ(List(5, -1), List(PConst, "x")), "x")) // 2 >= 0
    println(GEQ(List(5, -1), List(PConst, "x")).join(GEQ(List(-3, 1), List(PConst, "x")), "x")) // 2 >= 0


    ///////////////////////////////

    val p5 = Problem(List(GEQ(List(7, -3, -2), List(PConst, "x", "y")),  // 7 - 3x - 2y >= 0
                          GEQ(List(15, -6, -4), List(PConst, "x", "y")), // 15 - 6x - 4y >= 0
                          GEQ(List(1, 1), List(PConst, "x")),            // 1 + x >= 0
                          GEQ(List(0, 2), List(PConst, "y"))))           // 0 + 2y >= 0

    val v = p5.chooseVarMinCoef
    assert(v == "x")
    println(s"p5 var with min ceof: ${v}") //x
    val p5ans = p5.hasIntSolutions
    assert(p5ans)
    println(s"p5 has integer solutions: ${p5ans}")


    val p5_sim = p5.simplify(List("x"))
    assert(p5_sim.nonEmpty)
    println(s"p5 simplified: $p5_sim")

    val p6 = Problem(List(GEQ(List(4, -3, -2), List(PConst, "x", "y")),  // 4 - 3x - 2y >= 0
                          GEQ(List(-1, 1), List(PConst, "x")),           // -1 + x >= 0
                          GEQ(List(-1, 1), List(PConst, "y"))))          // -1 + y >= 0
    println(s"p6 normalized: ${p6.normalize}")
    val p6ans = p6.hasIntSolutions
    assert(!p6ans)
    assert(p6.simplify.isEmpty)
    println(s"p6 has integer solutions: ${p6ans}")
    println("---")

    assert(Problem(List(GEQ(List(10, 1), List(PConst, "x")))).hasIntSolutions)
    assert(Problem(List(GEQ(List(-10, 1), List(PConst, "x")))).hasIntSolutions)

    ///////////////////////////////

    println(GEQ(List(10, -1, 5), List(PConst, "x", "y"))
            .tightJoin(GEQ(List(-12, 1, 8), List(PConst, "x", "y")), "x"))
    println(GEQ(List(-12, 1, 8), List(PConst, "x", "y"))
            .tightJoin(GEQ(List(10, -1, 5), List(PConst, "x", "y")), "x"))

    val p7 = Problem(List(GEQ(List(10, -1, 5), List(PConst, "x", "y")),
                          GEQ(List(-12, 1, 8), List(PConst, "x", "y"))))

    assert(p7.realShadowSet("x") == p7.darkShadowSet("x"))
    println(p7.realShadowSet("x"))
    println(p7.darkShadowSet("x"))

    /* a =/= b can be transformed to a >= b + 1 /\ a <= b -1 */
    /* 1 + 2m =/= 2n => 1 + 2m - 2n =/= 0
       1 + 2m >= 2n + 1 => 2m - 2n >= 0
       1 + 2m <= 2n - 1 => -2m + 2n - 2 >= 0
     */
    val p8_1 = Problem(NEQ(List(1, 2, -2), List(PConst, "m", "n")).toGEQ(0))
    println(s"p8_1: $p8_1")
    val p8_1ans = p8_1.hasIntSolutions
    assert(p8_1ans)
    println(p8_1.simplify.nonEmpty)
    println(s"p8_1 has integer solutions: ${p8_1ans}")

    val p8_2 = Problem(NEQ(List(1, 2, -2), List(PConst, "m", "n")).toGEQ(1))
    println(s"p8_2: $p8_2")
    val p8_2ans = p8_2.hasIntSolutions
    assert(p8_2ans)
    assert(p8_2.simplify.nonEmpty)
    println(s"p8_2 has integer solutions: ${p8_2ans}")
    println("---")

    println("an omega test nightmare")
    /* 45 - 11x - 13y >= 0
     * -27 + 11x + 13y >= 0
     *  4 + -7x + 9y >= 0
     *  10 + 7x - 9y >= 0
     */
    val p9 = Problem(List(GEQ(List(45, -11, -13), List(PConst, "x", "y")),
                          GEQ(List(-27, 11, 13), List(PConst, "x", "y")),
                          GEQ(List(4, -7, 9), List(PConst, "x", "y")),
                          GEQ(List(10, 7, -9), List(PConst, "x", "y"))))
    val t0 = System.nanoTime()
    val p9ans = p9.hasIntSolutions
    val t1 = System.nanoTime()

    assert(!p9ans)
    assert(p9.simplify.isEmpty)
    println(s"p9 has integer solution: ${p9ans}. time: ${(t1-t0)/1000000000.0}s")
    println("---")

    val p10 = Problem(List(EQ(List(0, -1, 10, 25), List(PConst, "a", "b", "c")),
                          GEQ(List(-13, 1), List(PConst, "a"))))
    val p10ans = p10.hasIntSolutions
    assert(p10ans)
    println("---")
    println(p10.simplify(List("a")))
    println("---")
    println(p10.simplify(List("a", "b")))
    println("---")

    assert(Problem(List(GEQ(List(-10, 1), List(PConst, "x")),
                        GEQ(List(-20, 1), List(PConst, "x")))).hasIntSolutions)

    println(Problem(List(GEQ(List(-10, 1), List(PConst, "x")),
                         GEQ(List(-20, 1), List(PConst, "x")))).simplify(List("x")))

    println(Problem(List(GEQ(List(-10, 1), List(PConst, "x")),
                         GEQ(List(-20, 1), List(PConst, "x")))).reduce)

    assert(Problem(List(GEQ(List(10), List(PConst)))).hasIntSolutions)
    assert(Problem(List(EQ(List(0), List(PConst)))).hasIntSolutions)
    assert(!Problem(List(EQ(List(1), List(PConst)))).hasIntSolutions)
    assert(!Problem(List(GEQ(List(-10), List(PConst)))).hasIntSolutions)

    val p11s = Problem(List(EQ(List(1, 2, -2), List(PConst, "m", "n")))).negation
    println(s"p11s: $p11s")

    val o1 = OConj(OProb(Problem(List(GEQ(List(-5, 1), List(PConst, "x"))))),
                   OProb(Problem(List(GEQ(List(4, -1), List(PConst, "x"))))))
    assert(!Omega.verify(o1))

    // x >= 5 => 4 >= x
    val o2 = OImplies(OProb(Problem(List(GEQ(List(-5, 1), List(PConst, "x"))))),
                      OProb(Problem(List(GEQ(List(4, -1), List(PConst, "x"))))))
    println(Omega.flatten(o2))
    assert(!Omega.verify(o2))

    // x >= 5 && (x >= 10 || x <= 4)
    val o3 = OConj(OProb(Problem(List(GEQ(List(-5, 1), List(PConst, "x"))))),
                   ODisj(OProb(Problem(List(GEQ(List(-10, 1), List(PConst, "x"))))),
                         OProb(Problem(List(GEQ(List(4, -1), List(PConst, "x")))))))
    println(s"o3: $o3")
    assert(Omega.verify(o3))

    // x >= 5 && (x <= 0 || x <= 4)
    val o4 = OConj(OProb(Problem(List(GEQ(List(-5, 1), List(PConst, "x"))))),
                   ODisj(OProb(Problem(List(GEQ(List(0, -1), List(PConst, "x"))))),
                         OProb(Problem(List(GEQ(List(4, -1), List(PConst, "x")))))))
    assert(!Omega.verify(o4))

    // x == 0, x <= 4
    val p12 = Problem(List(EQ(List(0, 1), List(PConst, "x")),
                           GEQ(List(4, -1), List(PConst, "x"))))
    assert(p12.hasIntSolutions)

    // x == 1 under x >= 0 && x <= 4
    val o5 = OProb(Problem(List(GEQ(List(0, 1), List(PConst, "x")))))
    val o6 = OProb(Problem(List(GEQ(List(4, -1), List(PConst, "x")))))
    var result = Omega.verify(OProb(Problem(List(EQ(List(-1, 1), List(PConst, "x"))))),
                             List(o5, o6))
    assert(result)

    // (x >= 2 || x <= 0)  under (x >= 0 && x <= 4)
    val o7 = OProb(Problem(List(EQ(List(-1, 1), List(PConst, "x"))))).negation
    println(o7)
    result = Omega.verify(o7, List(o5, o6))
    assert(result)

    // (x >= 5 || x <= 3)  under (x >= 0 && x <= 4)
    val o8 = OProb(Problem(List(EQ(List(-4, 1), List(PConst, "x"))))).negation
    println(o8)
    result = Omega.verify(o8, List(o5, o6))
    assert(result)

    // x == 5 under x >= 0 && x <= 4
    val o9 = OProb(Problem(List(EQ(List(-5, 1), List(PConst, "x")))))
    println(o9)
    result = Omega.verify(o9, List(o5, o6))
    assert(!result)

    // (x >= 5 || x <= 3)  && (x <= 4)
    val o10 = OConj(OProb(Problem(List(EQ(List(-4, 1), List(PConst, "x"))))).negation,
                    OProb(Problem(List(GEQ(List(4, -1), List(PConst, "x"))))))
    println(o10)
    result = Omega.verify(o10)
    assert(result)

    // (x >= 5 || x <= 3)  && (x == 4)
    val o11 = OConj(OProb(Problem(List(EQ(List(-4, 1), List(PConst, "x"))))).negation,
                    OProb(Problem(List(EQ(List(4, -1), List(PConst, "x"))))))
    println(o11)
    result = Omega.verify(o11)
    assert(!result)
  }
}
