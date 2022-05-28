package edu.cmu.cs.ls.keymaerax.btactics

import java.math.{MathContext, RoundingMode}

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr, Position, RenUSubst, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.tools.ext.QETacticTool
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols._

import scala.collection.immutable._

/** Interval Arithmetic
  *
  * @author Fabian Immler
  */
object IntervalArithmeticV2 {

  def mathematicaFriendly(d: BigDecimal) : Term =
    Times(Number(BigDecimal(d.bigDecimal.unscaledValue())), Power(Number(10), Number(-d.scale)))

  private def downContext(prec: Int) = new MathContext(prec, RoundingMode.FLOOR)
  private def upContext(prec: Int) = new MathContext(prec, RoundingMode.CEILING)

  type DecimalBounds = (HashMap[Term, BigDecimal], HashMap[Term, BigDecimal])
  def DecimalBounds(): DecimalBounds = (HashMap[Term, BigDecimal](), HashMap[Term, BigDecimal]())

  private def op_endpoints(f: (BigDecimal, BigDecimal, MathContext) => BigDecimal)
                          (prec: Int)
                          (bounds: DecimalBounds)
                          (lat: Term, uat: Term)
                          (lbt: Term, ubt: Term) : (BigDecimal, BigDecimal) = {
    val (la, ua1) = eval_ivl(prec)(bounds)(lat)
    val ua = if (lat == uat) ua1 else eval_ivl(prec)(bounds)(uat)._2
    val (lb, ub1) = eval_ivl(prec)(bounds)(lbt)
    val ub = if (lbt == ubt) ub1 else eval_ivl(prec)(bounds)(ubt)._2
    val pairs = (List(la, la, ua, ua), List(lb, ub, lb, ub)).zipped
    val lowers = pairs map ((a, b) => f(a, b, downContext(prec)))
    val uppers = pairs map ((a, b) => f(a, b, upContext(prec)))
    (lowers.reduceLeft(_.min(_)), uppers.reduceLeft(_.max(_)))
  }

  private def mult_endpoints(prec: Int)(bounds: DecimalBounds)(lat: Term, uat: Term)(lbt: Term, ubt: Term) : (BigDecimal, BigDecimal) =
    op_endpoints((a, b, c) => a.bigDecimal.multiply(b.bigDecimal, c))(prec)(bounds)(lat, uat)(lbt, ubt)
  private def divide_endpoints(prec: Int)(bounds: DecimalBounds)(lat: Term, uat: Term)(lbt: Term, ubt: Term) : (BigDecimal, BigDecimal) =
    op_endpoints((a, b, c) => a.bigDecimal.divide(b.bigDecimal, c))(prec)(bounds)(lat, uat)(lbt, ubt)

  private def power_endpoints(prec: Int)(bounds: DecimalBounds)(lat: Term, uat: Term)(n: Int) : (BigDecimal, BigDecimal) = {
    if (n >= 0) {
      val (la, _) = eval_ivl(prec)(bounds)(lat)
      val (_, ua) = eval_ivl(prec)(bounds)(uat)
      if (n == 0) {
        if (la > 0 || ua < 0) (1, 1)
        else throw new IllegalArgumentException("Power [" + la + ", " + ua + "]^0 is not defined")
      }
      val lower: BigDecimal =
        if (n % 2 == 1) la.bigDecimal.pow(n, downContext(prec))
        else {
          if (0 <= la) la.bigDecimal.pow(n, downContext(prec))
          else {
            if (ua <= 0) ua.bigDecimal.pow(n, downContext(prec))
            else 0
          }
        }
      val upper = (la.bigDecimal.pow(n, upContext(prec))) max (ua.bigDecimal.pow(n, upContext(prec)))
      (lower, upper)
    } else {
      val (l, u) = power_endpoints(prec)(bounds)(lat, uat)(-n)
      divide_endpoints(prec)(bounds)(Number(1), Number(1))(Number(l), Number(u))
    }
  }
  /** Compute interval bounds by recursing over the input term structure.
    * An environment of bounds for variables and function symbols can be provided, too.
    *
    * @param prec   decimal precision for numeric bounds
    * @param bounds environment of lower and upper bounds
    * @param t      input term
    * @return a tuple for lower and upper bounds on the term t
    */
  def eval_ivl(prec: Int)(bounds: DecimalBounds)(t: Term) : (BigDecimal, BigDecimal) = t match {
    case Plus(a, b) =>
      val (la, ua) = eval_ivl(prec)(bounds)(a)
      val (lb, ub) = eval_ivl(prec)(bounds)(b)
      (la.bigDecimal.add(lb.bigDecimal, downContext(prec)), ua.bigDecimal.add(ub.bigDecimal, upContext(prec)))
    case Minus(a, b) =>
      val (la, ua) = eval_ivl(prec)(bounds)(a)
      val (lb, ub) = eval_ivl(prec)(bounds)(b)
      (la.bigDecimal.subtract(ub.bigDecimal, downContext(prec)), ua.bigDecimal.subtract(lb.bigDecimal, upContext(prec)))
    case FuncOf(m, Pair(a, b)) if m == minF || m == maxF =>
      val (la, ua) = eval_ivl(prec)(bounds)(a)
      val (lb, ub) = eval_ivl(prec)(bounds)(b)
      if (m == minF) {
        (la.bigDecimal.min(lb.bigDecimal), ua.bigDecimal.min(ub.bigDecimal))
      } else {
        (la.bigDecimal.max(lb.bigDecimal), ua.bigDecimal.max(ub.bigDecimal))
      }
    case Neg(a) =>
      val (la, ua) = eval_ivl(prec)(bounds)(a)
      (-ua, -la)
    case Number(n) => (n.bigDecimal.round(downContext(prec)), n.bigDecimal.round(upContext(prec)))
    case Times(a, b) => mult_endpoints(prec)(bounds)(a,a)(b,b)
    case Divide(a, b) => divide_endpoints(prec)(bounds)(a,a)(b,b)
    case Power(a, Number(i)) if i.isValidInt => power_endpoints(prec)(bounds)(a, a)(i.toInt)
    case _ if bounds._1.isDefinedAt(t) && bounds._2.isDefinedAt(t) => (bounds._1(t), bounds._2(t))
    case _ => throw new RuntimeException("Unable to compute bounds for " + t)
  }

  def isNumeric(t: Term) : Boolean = t match {
    case t: BinaryCompositeTerm => isNumeric(t.left) && isNumeric(t.right)
    case t: UnaryCompositeTerm => isNumeric(t.child)
    case Number(_) => true
    case FuncOf(m, Pair(a, b)) if m == minF || m == maxF => isNumeric(a) && isNumeric(b)
    case _ => false
  }

  private def collect_bound(prec: Int)(fml: Formula, bounds: DecimalBounds): DecimalBounds = {
    fml match {
      case LessEqual(t, n) if isNumeric(n) =>
        (bounds._1, bounds._2.updated(t, eval_ivl(prec)(DecimalBounds())(n)._2))
      case LessEqual(n, t) if isNumeric(n) =>
        (bounds._1.updated(t, eval_ivl(prec)(DecimalBounds())(n)._1), bounds._2)
      case Less(t, n) if isNumeric(n) =>
        (bounds._1, bounds._2.updated(t, eval_ivl(prec)(DecimalBounds())(n)._2))
      case Less(n, t) if isNumeric(n) =>
        (bounds._1.updated(t, eval_ivl(prec)(DecimalBounds())(n)._1), bounds._2)
      case _ => bounds
    }
  }

  class StaticSingleAssignmentExpression[E <: Expression](e: E, prefix: String = "ssa") {

    private def nextVar(i: Int) = Variable(prefix + i + "_")

    private def insert(t: Term, m: Map[Term, Variable], nextIndex: Int) : (Variable, Map[Term, Variable], Int) = {
      m.get(t) match {
        case Some(v) => (v, m, nextIndex)
        case None =>
          val v = nextVar(nextIndex)
          (v, m.updated(t, v), nextIndex+1)
      }
    }

    private def collectSubterms(t: Term, m: Map[Term, Variable], i: Int) : (Variable, Map[Term, Variable], Int) = t match {
      case b: BinaryCompositeTerm =>
        val (lv, lm, li) = collectSubterms(b.left, m, i)
        val (rv, rm, ri) = collectSubterms(b.right, lm, li)
        insert(b.reapply(lv, rv), rm, ri)
      case u: UnaryCompositeTerm =>
        val (cv, cm, ci) = collectSubterms(u.child, m, i)
        insert(u.reapply(cv), cm, ci)
      // Binary function, e.g., min/max
      case FuncOf(f, Pair(l, r)) =>
        val (lv, lm, li) = collectSubterms(l, m, i)
        val (rv, rm, ri) = collectSubterms(r, lm, li)
        insert(FuncOf(f, Pair(lv, rv)), rm, ri)
      // Unary function, e.g., abs
      case FuncOf(f, c) if c.sort == Real =>
        val (cv, cm, ci) = collectSubterms(c, m, i)
        insert(FuncOf(f, cv), cm, ci)
      // Constant symbols
      case FuncOf(f, Nothing) => insert(t, m, i)
      case a: AtomicTerm => insert(a, m, i)
    }

    private def collectSubformulas(fml: Formula, m: Map[Term, Variable], i: Int) : (Formula, Map[Term, Variable], Int) = fml match {
      case b: ComparisonFormula =>
        val (lv, lm, li) = collectSubterms(b.left, m, i)
        val (rv, rm, ri) = collectSubterms(b.right, lm, li)
        (b.reapply(lv, rv), rm, ri)
      case b: BinaryCompositeFormula =>
        val (lv, lm, li) = collectSubformulas(b.left, m, i)
        val (rv, rm, ri) = collectSubformulas(b.right, lm, li)
        (b.reapply(lv, rv), rm, ri)
      case u: UnaryCompositeFormula =>
        val (cv, cm, ci) = collectSubformulas(u.child, m, i)
        (u.reapply(cv), cm, ci)
      case a: AtomicFormula => (a, m, i)
    }

    val (expression : E, abbrev : Map[Term, Variable]) = e match {
      case t: Term =>
        val (fml, unm, _) = collectSubterms(t, Map(), 0)
        (fml, unm)
      case fml: Formula =>
        val (fml2, unm, _) = collectSubformulas(fml, Map(), 0)
        (fml2, unm)
    }

    val unfoldMap : Map[Variable, Term] = abbrev.map{case (t, v) => (v, t)}

    def unfold(t: Term) : Term = t match {
      case v: Variable =>
        unfoldMap.get(v) match {
          case None => t
          case Some(b: BinaryCompositeTerm) => b.reapply(unfold(b.left), unfold(b.right))
          case Some(b: UnaryCompositeTerm) => b.reapply(unfold(b.child))
          case Some(FuncOf(f, Pair(l, r))) => FuncOf(f, Pair(unfold(l), unfold(r)))
          case Some(FuncOf(f, c)) if c.sort == Real => FuncOf(f, unfold(c))
          case Some(a) => a
          // Constant symbols
          case _ => t
      }
      case t => t
    }

    def unfold(fml: Formula) : Formula = fml match {
      case (b: BinaryCompositeFormula) => b.reapply(unfold(b.left), unfold(b.right))
      case (b: UnaryCompositeFormula) => b.reapply(unfold(b.child))
      case (b: ComparisonFormula) => b.reapply(unfold(b.left), unfold(b.right))
      case _ => fml
    }

  }

  /** Populate environment with bounds (only LessEqual are being considered)
    *
    * @param prec decimal precision
    * @param bounds the environment to populate
    * @param assms sequence of Formulas containing bounds
    * @return updated environment
    */
  def collect_bounds(prec: Int, bounds: DecimalBounds, assms: Seq[Formula]): DecimalBounds =
    assms.foldRight(bounds)(collect_bound(prec))
  def collect_bounds(prec: Int, assms: Seq[Formula]): DecimalBounds = collect_bounds(prec, DecimalBounds(), assms)


  private def eval_ivl_term_in_env(prec: Int)(bounds: DecimalBounds)(t: Term) : (Term, Term) = {
    val (l, u) = eval_ivl(prec)(bounds)(t)
    (mathematicaFriendly(l), mathematicaFriendly(u))
  }
  private def eval_ivl_term(prec: Int)(t: Term) : (Term, Term) = eval_ivl_term_in_env(prec)(DecimalBounds())(t)

  private val t_f = "f_()".asTerm
  private val t_g = "g_()".asTerm
  private val t_h = "h_()".asTerm
  private val t_ff = "ff_()".asTerm
  private val t_gg = "gg_()".asTerm
  private val t_F = "F_()".asTerm
  private val t_G = "G_()".asTerm

  // lemmas for extracting bounds
  private lazy val eqBound1 = proveBy("f_() = g_() ==> f_() <= g_()".asSequent, QE & done)
  private lazy val eqBound2 = proveBy("f_() = g_() ==> g_() <= f_()".asSequent, QE & done)
  private lazy val ltBound = proveBy("f_() < g_() ==> f_() <= g_()".asSequent, QE & done)
  private lazy val geBound = proveBy("f_() >= g_() ==> g_() <= f_()".asSequent, QE & done)
  private lazy val gtBound = proveBy("f_() > g_() ==> g_() <= f_()".asSequent, QE & done)

  private lazy val leRefl = proveBy("F_() <= F_()".asFormula,
    useAt(Ax.lessEqualRefl, PosInExpr(0::Nil))(1) & prop & done)
  private lazy val negDownSeq = proveBy("f_()<=F_() & (h_()<=-F_()<->true) ==> h_()<=-f_()".asSequent,
    useAt(Ax.intervalDownNeg, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val negUpSeq = proveBy("ff_()<=f_() & (-ff_()<=h_()<->true) ==> -f_()<=h_()".asSequent,
    useAt(Ax.intervalUpNeg, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val plusDownSeq = proveBy("(ff_()<=f_() & gg_()<=g_()) & (h_()<=ff_()+gg_()<->true) ==> h_()<=f_()+g_()".asSequent,
    useAt(Ax.intervalDownPlus, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val plusUpSeq = proveBy("(f_()<=F_() & g_()<=G_()) & (F_()+G_()<=h_()<->true) ==> f_()+g_()<=h_()".asSequent,
    useAt(Ax.intervalUpPlus, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val minusDownSeq = proveBy("(ff_()<=f_() & g_()<=G_()) & (h_()<=ff_()-G_()<->true) ==> h_()<=f_()-g_()".asSequent,
    useAt(Ax.intervalDownMinus, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val minusUpSeq = proveBy("(f_()<=F_() & gg_()<=g_()) & (F_()-gg_()<=h_()<->true) ==> f_()-g_()<=h_()".asSequent,
    useAt(Ax.intervalUpMinus, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val multUpSeq = proveBy(
    "(((ff_()<=f_() & f_()<=F_()) & gg_()<=g_() & g_()<=G_()) & ((ff_()*gg_()<=h_() & ff_()*G_()<=h_() & F_()*gg_()<=h_() & F_()*G_()<=h_())<->true)) ==> f_()*g_()<=h_()".asSequent,
    useAt(Ax.intervalUpTimes, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val multDownSeq = proveBy(
    "(((ff_()<=f_() & f_()<=F_()) & gg_()<=g_() & g_()<=G_()) & ((h_()<=ff_()*gg_() & h_()<=ff_()*G_() & h_()<=F_()*gg_() & h_()<=F_()*G_())<->true)) ==> h_()<=f_()*g_()".asSequent,
    useAt(Ax.intervalDownTimes, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val divideUpSeq = proveBy(("((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) &" +
    "((" +
    "  ( G_()<0 & (ff_()>=h_()*gg_() & ff_()>=h_()*G_() & F_()>=h_()*gg_() & F_()>=h_()*G_())) |" +
    "  (0<gg_() & (ff_()<=h_()*gg_() & ff_()<=h_()*G_() & F_()<=h_()*gg_() & F_()<=h_()*G_()))" +
    ")<->true) ==> f_()/g_()<=h_()").asSequent, QE & done)
  private lazy val divideDownSeq = proveBy(("((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) &" +
    "((" +
    "  (  G_()<0 & (h_()*gg_()>=ff_() & h_()*G_()>=ff_() & h_()*gg_()>=F_() & h_()*G_()>=F_())) |" +
    "  ( 0<gg_() & (h_()*gg_()<=ff_() & h_()*G_()<=ff_() & h_()*gg_()<=F_() & h_()*G_()<=F_()))" +
    ")<->true) ==> h_()<=f_()/g_()").asSequent,
    QE & done)
  private lazy val minUpSeq = proveBy("((f_()<=F_() & g_()<=G_()) & ((F_() <= h_() | G_()<=h_())<->true)) ==> min(f_(),g_())<=h_()".asSequent, useAt(Ax.intervalUpMin, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val minDownSeq = proveBy("((ff_()<=f_() & gg_()<=g_()) & ((h_() <= ff_() & h_()<=gg_())<->true)) ==> h_()<=min(f_(),g_())".asSequent, useAt(Ax.intervalDownMin, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val maxUpSeq = proveBy("((f_()<=F_() & g_()<=G_()) & ((F_() <= h_() & G_()<=h_())<->true)) ==> max(f_(),g_())<=h_()".asSequent, useAt(Ax.intervalUpMax, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val maxDownSeq = proveBy("((ff_()<=f_() & gg_()<=g_()) & ((h_() <= ff_() | h_() <= gg_())<->true))==>h_() <= max(f_(),g_())".asSequent, useAt(Ax.intervalDownMax, PosInExpr(1::Nil))(1) & prop & done)


  // Formulas
  private lazy val leBothSeq = proveBy(
    "((f_()<=F_() & gg_()<=g_()) & (F_() <= gg_()<->true)) ==> f_()<=g_()".asSequent,
    useAt(Ax.intervalLEBoth, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val ltBothSeq = proveBy(
    "((f_()<=F_() & gg_()<=g_()) & (F_() < gg_()<->true)) ==> f_()<g_()".asSequent,
    useAt(Ax.intervalLBoth, PosInExpr(1::Nil))(1) & prop & done)
  private lazy val geBothSeq = proveBy(
    "((g_()<=G_() & ff_()<=f_()) & (G_() <= ff_()<->true)) ==> f_()>=g_()".asSequent, QE & done)
  private lazy val gtBothSeq = proveBy(
    "((g_()<=G_() & ff_()<=f_()) & (G_() < ff_()<->true)) ==> f_()>g_()".asSequent, QE & done)

  private var powerDownCache = new HashMap[Int, ProvableSig]()
  private def powerDownSeq(n: Int): ProvableSig =
    powerDownCache.get(n) match {
      case Some(prv) => prv
      case None =>
        val prv: ProvableSig =
          if (n >= 0) {
            if (n % 2 == 0)
              proveBy(("((ff_()<=f_() & f_()<=F_()) &" +
                "((((0<=ff_() & h_()<=ff_()^" + n + ") | (F_()<=0 & h_()<=F_()^" + n + ") | (ff_() <= 0 & 0<= F_() & h_()<=0)))<->true))" +
                "==> h_()<=f_()^" + n).asSequent, QE & done)
            else
              proveBy(("((ff_()<=f_() & f_()<=F_()) & (((h_()<=ff_()^" + n + "))<->true)) ==> h_()<=f_()^" + n + "").asSequent, QE & done)
          } else {
            if (n % 2 == 0)
              proveBy(("((ff_()<=f_() & f_()<=F_()) &" +
                "((((0<ff_() & h_()*F_()^" + -n + "<=1) | (F_()<0 & h_()*ff_()^" + -n + "<=1)))<->true))" +
                "==> h_()<=f_()^" + n).asSequent, QE & done)
            else
              proveBy(("((ff_()<=f_() & f_()<=F_()) &" +
                "(((ff_()>0 & h_()*F_()^" + -n + "<=1) | (F_()<0 & h_()*F_()^" + -n + ">=1))<->true))" +
                "==> h_()<=f_()^" + n + "").asSequent, QE & done)
          }
        powerDownCache = powerDownCache.updated(n, prv)
        prv
    }
  private var powerUpCache = new HashMap[Int, ProvableSig]()
  private def powerUpSeq(n: Int): ProvableSig =
    powerUpCache.get(n) match {
      case Some(prv) => prv
      case None =>
        val prv: ProvableSig =
          if (n >= 0)
            proveBy(("((ff_()<=f_() & f_()<=F_()) & (((ff_()^" + n + " <= h_() & F_()^" + n + " <=h_()))<->true)) ==> f_()^" + n + " <=h_()").asSequent, QE & done)
          else if (n % 2 == 0) {
            proveBy(("((ff_()<=f_() & f_()<=F_()) &" +
              "(((ff_()>0 & 1 <=ff_()^" + -n + "*h_()) | (F_()<0 & 1 <=F_()^" + -n + "*h_()))<->true))" +
              "==> f_()^" + n + " <=h_()").asSequent, QE & done)
          } else {
            proveBy(("((ff_()<=f_() & f_()<=F_()) &" +
              "(((ff_()>0 & 1 <=ff_()^" + -n + "*h_()) | (F_()<0 & 1 >=ff_()^" + -n + "*h_()))<->true))" +
              "==> f_()^" + n + " <=h_()").asSequent, QE & done)
          }
        powerUpCache = powerUpCache.updated(n, prv)
        prv
    }

  /*
  fml |- P      G |- fml
  ----------------------
    G |- P
   */
  private def CutHide(fml: Formula)(prv: ProvableSig) = {
    requireOneSubgoal(prv, "CutHide")
    val seq = prv.subgoals(0)
    requireOneSucc(seq, "CutHide")
    (0 until seq.ante.length).foldLeft(prv.apply(Cut(fml), 0).apply(HideRight(SuccPos(0)), 1)) {
      (p, _) =>
        p.apply(HideLeft(AntePos(0)), 0)
    }
  }

  type BoundMap = HashMap[Term, ProvableSig]
  def BoundMap(): BoundMap = HashMap[Term, ProvableSig]()

  /**
    * prec: numerical precision
    * qeTool: QETool for ground numerical computations
    * assms: assumptions on variables - any (in)equality with a variable on one side and a numerical term on the other side
    * ssaMap: A map of abbreviations for subterms, used as keys, theorems proved with "expanded"
    * */
  private def recurse(prec: Int)
             (qeTool: QETacticTool)
             (assms: IndexedSeq[Formula])
             (lowers: BoundMap, uppers: BoundMap, ssaMap: Map[Variable, Term])
             (s: Term): (BoundMap, BoundMap)
  = {
    def unknown_bound(v: Term) : String = "\nCould not find bounds for " + v + ".\n" +
      "Both upper and lower bound are required and need to be separate formulas in the antecedent.\n" +
      "Bounds must be given with a number on one side of one of the comparison operators <,<=,=,>=,>.\n" +
      "Maybe try Propositional->Exhaustive (prop) first?"
    // TODO: if there is more like this, better use an [[ StaticSingleAssignment.unfoldMap]] throughout
    def intOfTerm(t: Term) : Option[Int] = t match {
      case Number(n) if n.isValidInt => Some(n.toIntExact)
      case v: Variable => ssaMap.get(v) match {
        case Some(Number(n)) => intOfTerm(Number(n))
        case _ => None
      }
      case _ => None
    }
    if (lowers.isDefinedAt(s) && uppers.isDefinedAt(s)) (lowers, uppers)
    else s match {
      case v : Variable => {
        ssaMap.get(v) match {
          case Some(rhs) =>
            val (lowers2, uppers2) = recurse(prec)(qeTool)(assms)(lowers, uppers, ssaMap)(rhs)
            val ff_prv = lowers2(rhs)
            val F_prv = uppers2(rhs)
            (lowers2.updated(v, ff_prv), uppers2.updated(v, F_prv))
          case None =>
            throw new InputFormatFailure(unknown_bound(v))
        }
      }
      case n: Number =>
        val refl = ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(n, n)))).
          apply(CoHideRight(SuccPos(0)), 0).
          apply(leRefl.apply(USubst(SubstitutionPair(t_F, n) :: Nil)), 0)
        (lowers.updated(n, refl), uppers.updated(n, refl))
      case Neg(a) =>
        val (lowers2, uppers2) = recurse(prec)(qeTool)(assms)(lowers, uppers, ssaMap)(a)
        val ff_prv = lowers2(a)
        val F_prv = uppers2(a)
        val ff_fml = ff_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val F_fml = F_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val f = ff_fml.right // @note: this can be different from [[a]], if a has been further resolved via the [[ssaMap]]
        val t = Neg(f)
        val ff = ff_fml.left
        val F = F_fml.right
        val (h, _) = eval_ivl_term(prec)(Neg(F))
        val (_, hH) = eval_ivl_term(prec)(Neg(ff))
        val negDown = negDownSeq.apply(USubst(
          SubstitutionPair(t_h, h) ::
            SubstitutionPair(t_f, f) ::
            SubstitutionPair(t_F, F) :: Nil))
        val negUp = negUpSeq.apply(USubst(
          SubstitutionPair(t_h, hH) ::
            SubstitutionPair(t_f, f) ::
            SubstitutionPair(t_ff, ff) :: Nil))

        val h_le = qeTool.qe(negDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
        val H_le = qeTool.qe(negUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

        val h_prv = (CutHide(negDown.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
          apply(negDown, 0).
          apply(AndRight(SuccPos(0)), 0).
          apply(CoHideRight(SuccPos(0)), 1).
          apply(h_le, 1).
          apply(F_prv, 0)
        val H_prv = (CutHide(negUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, hH)))))).
          apply(negUp, 0).
          apply(AndRight(SuccPos(0)), 0).
          apply(CoHideRight(SuccPos(0)), 1).
          apply(H_le, 1).
          apply(ff_prv, 0)
        (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
      case binop: BinaryCompositeTerm =>
        val a = binop.left
        val b = binop.right
        val (lowers1, uppers1) = recurse(prec)(qeTool)(assms)(lowers, uppers, ssaMap)(a)
        val (lowers2, uppers2) = recurse(prec)(qeTool)(assms)(lowers1, uppers1, ssaMap)(b)
        val ff_prv = lowers2(a)
        val gg_prv = lowers2(b)
        val F_prv = uppers2(a)
        val G_prv = uppers2(b)
        val ff_fml = ff_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val gg_fml = gg_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val F_fml = F_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val G_fml = G_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val f = ff_fml.right  /* @note: this can be different from [[f0]], if a has been further resolved via the [[ssaMap]] */
        val g = gg_fml.right /* @note: this can be different from [[g0]], if a has been further resolved via the [[ssaMap]] */
        val t = binop.reapply(f, g)
        val ff = ff_fml.left
        val gg = gg_fml.left
        val F = F_fml.right
        val G = G_fml.right
        binop match {
          case _: Plus =>
            val h = eval_ivl_term(prec)(Plus(ff, gg))._1
            val H = eval_ivl_term(prec)(Plus(F, G))._2
            val plusDown = plusDownSeq.apply(USubst(
              SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) :: Nil))
            val plusUp = plusUpSeq.apply(USubst(
              SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))

            val h_le = qeTool.qe(plusDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_le = qeTool.qe(plusUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

            val h_prv = (CutHide(plusDown.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(plusDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(gg_prv, 1).  // be stable by operating on last subgoal
              apply(ff_prv, 0)
            val H_prv = (CutHide(plusUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(plusUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(G_prv, 1).
              apply(F_prv, 0)
            (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
          case _: Minus =>
            val h = eval_ivl_term(prec)(Minus(ff, G))._1
            val H = eval_ivl_term(prec)(Minus(F, gg))._2
            val minusDown = minusDownSeq.apply(USubst(
              SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_G, G) :: Nil))
            val minusUp = minusUpSeq.apply(USubst(
              SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_gg, gg) :: Nil))

            val h_le = qeTool.qe(minusDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_le = qeTool.qe(minusUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

            val h_prv = (CutHide(minusDown.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(minusDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(G_prv, 1).  // be stable by operating on last subgoal
              apply(ff_prv, 0)
            val H_prv = (CutHide(minusUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(minusUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(gg_prv, 1).
              apply(F_prv, 0)
            (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
          case _: Times =>
            // Bounds
            val bnds = mult_endpoints(prec)(DecimalBounds)(ff, F)(gg, G)
            val h = mathematicaFriendly(bnds._1)
            val H = mathematicaFriendly(bnds._2)
            val multDown = multDownSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val h_le = qeTool.qe(multDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val ante = multDown.conclusion.ante(0)
            val ff_f_F_gg_g_G = ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(ante.asInstanceOf[And].left))).
              apply(AndRight(SuccPos(0)), 0).
              apply(AndRight(SuccPos(0)), 1).
              apply(G_prv, 2).
              apply(gg_prv, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)
            val h_prv = (CutHide(ante)(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(multDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(ff_f_F_gg_g_G, 0)

            val multUp = multUpSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val H_le = qeTool.qe(multUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_prv = (CutHide(multUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(multUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(ff_f_F_gg_g_G, 0)
            (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
          case _: Divide =>
            // Bounds
            val bnds = divide_endpoints(prec)(DecimalBounds())(ff, F)(gg, G)
            val h = mathematicaFriendly(bnds._1)
            val H = mathematicaFriendly(bnds._2)
            val divideDown = divideDownSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val h_le = qeTool.qe(divideDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val ante = divideDown.conclusion.ante(0)
            val ff_f_F_gg_g_G = ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(ante.asInstanceOf[And].left))).
              apply(AndRight(SuccPos(0)), 0).
              apply(AndRight(SuccPos(0)), 1).
              apply(G_prv, 2).
              apply(gg_prv, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)
            val h_prv = (CutHide(ante)(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(divideDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(ff_f_F_gg_g_G, 0)

            val divideUp = divideUpSeq.apply(USubst(
              SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_gg, gg) ::
                SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_g, g) ::
                SubstitutionPair(t_F, F) ::
                SubstitutionPair(t_G, G) :: Nil))
            val H_le = qeTool.qe(divideUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_prv = (CutHide(divideUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(divideUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(ff_f_F_gg_g_G, 0)
            (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
          case _ : Power if intOfTerm(b).isDefined =>
            // Lower Bound
            val n = intOfTerm(b).get
            val ivl = power_endpoints(prec)(DecimalBounds())(ff, F)(n)
            val h = mathematicaFriendly(ivl._1)
            val H = mathematicaFriendly(ivl._2)
            val powerDown = powerDownSeq(n).apply(USubst(
              SubstitutionPair(t_h, h) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_F, F) :: Nil))
            val h_le = qeTool.qe(powerDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val h_prv = (CutHide(powerDown.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
              apply(powerDown, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(h_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)

            // Upper Bound
            val powerUp = powerUpSeq(n).apply(USubst(
              SubstitutionPair(t_h, H) ::
                SubstitutionPair(t_ff, ff) ::
                SubstitutionPair(t_f, f) ::
                SubstitutionPair(t_F, F) :: Nil))
            val H_le = qeTool.qe(powerUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
            val H_prv = (CutHide(powerUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
              apply(powerUp, 0).
              apply(AndRight(SuccPos(0)), 0).
              apply(CoHideRight(SuccPos(0)), 1).
              apply(H_le, 1).
              apply(AndRight(SuccPos(0)), 0).
              apply(F_prv, 1).
              apply(ff_prv, 0)
            (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
          case _ =>
            throw new UnsupportedTacticFeature("\nUnable to compute bound for " + t + "\n" +
              "Binary operation " + t.getClass.getSimpleName + " not implemented.")
        }
      case FuncOf(m, Pair(a, b)) if m == minF || m == maxF =>
        val (lowers1, uppers1) = recurse(prec)(qeTool)(assms)(lowers, uppers, ssaMap)(a)
        val (lowers2, uppers2) = recurse(prec)(qeTool)(assms)(lowers1, uppers1, ssaMap)(b)
        val ff_prv = lowers2(a)
        val gg_prv = lowers2(b)
        val F_prv = uppers2(a)
        val G_prv = uppers2(b)
        val ff_fml = ff_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val gg_fml = gg_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val F_fml = F_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val G_fml = G_prv.conclusion.succ(0).asInstanceOf[LessEqual]
        val f = ff_fml.right // @note: this can be different from [[a]], if a has been further resolved via the [[ssaMap]]
        val g = gg_fml.right  // @note: this can be different from [[b]], if b has been further resolved via the [[ssaMap]]
        val t = FuncOf(m, Pair(f, g))
        val ff = ff_fml.left
        val gg = gg_fml.left
        val F = F_fml.right
        val G = G_fml.right

        val h = eval_ivl_term(prec)(FuncOf(m, Pair(ff, gg)))._1
        val H = eval_ivl_term(prec)(FuncOf(m, Pair(F, G)))._2
        if (m == minF) {
          val minDown = minDownSeq.apply(USubst(
            SubstitutionPair(t_h, h) ::
              SubstitutionPair(t_f, f) ::
              SubstitutionPair(t_g, g) ::
              SubstitutionPair(t_ff, ff) ::
              SubstitutionPair(t_gg, gg) :: Nil))
          val minUp = minUpSeq.apply(USubst(
            SubstitutionPair(t_h, H) ::
              SubstitutionPair(t_f, f) ::
              SubstitutionPair(t_g, g) ::
              SubstitutionPair(t_F, F) ::
              SubstitutionPair(t_G, G) :: Nil))

          val h_le = qeTool.qe(minDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
          val H_le = qeTool.qe(minUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

          val h_prv = (CutHide(minDown.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
            apply(minDown, 0).
            apply(AndRight(SuccPos(0)), 0).
            apply(CoHideRight(SuccPos(0)), 1).
            apply(h_le, 1).
            apply(AndRight(SuccPos(0)), 0).
            apply(gg_prv, 1).  // be stable by operating on last subgoal
            apply(ff_prv, 0)
          val H_prv = (CutHide(minUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
            apply(minUp, 0).
            apply(AndRight(SuccPos(0)), 0).
            apply(CoHideRight(SuccPos(0)), 1).
            apply(H_le, 1).
            apply(AndRight(SuccPos(0)), 0).
            apply(G_prv, 1).
            apply(F_prv, 0)
          (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
        } else /* max */ {
          val maxDown = maxDownSeq.apply(USubst(
            SubstitutionPair(t_h, h) ::
              SubstitutionPair(t_f, f) ::
              SubstitutionPair(t_g, g) ::
              SubstitutionPair(t_ff, ff) ::
              SubstitutionPair(t_gg, gg) :: Nil))
          val maxUp = maxUpSeq.apply(USubst(
            SubstitutionPair(t_h, H) ::
              SubstitutionPair(t_f, f) ::
              SubstitutionPair(t_g, g) ::
              SubstitutionPair(t_F, F) ::
              SubstitutionPair(t_G, G) :: Nil))

          val h_le = qeTool.qe(maxDown.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
          val H_le = qeTool.qe(maxUp.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact

          val h_prv = (CutHide(maxDown.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(h, t)))))).
            apply(maxDown, 0).
            apply(AndRight(SuccPos(0)), 0).
            apply(CoHideRight(SuccPos(0)), 1).
            apply(h_le, 1).
            apply(AndRight(SuccPos(0)), 0).
            apply(gg_prv, 1).  // be stable by operating on last subgoal
            apply(ff_prv, 0)
          val H_prv = (CutHide(maxUp.conclusion.ante(0))(ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(LessEqual(t, H)))))).
            apply(maxUp, 0).
            apply(AndRight(SuccPos(0)), 0).
            apply(CoHideRight(SuccPos(0)), 1).
            apply(H_le, 1).
            apply(AndRight(SuccPos(0)), 0).
            apply(G_prv, 1).
            apply(F_prv, 0)
          (lowers2.updated(s, h_prv), uppers2.updated(s, H_prv))
        }
      case _ =>
        throw new UnsupportedTacticFeature ("\nUnable to compute bound for " + s + "\n" +
          s.getClass.getSimpleName + " not implemented for Interval Arithmetic.")
    }
  }

  private def extract_bound(assms: IndexedSeq[Formula], index: Int, conclusion: Formula, rule: ProvableSig, instantiation: List[(Term, Term)]) =
    ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(conclusion))).
      apply(CoHide2(AntePos(index), SuccPos(0)), 0).
      apply(rule.apply(USubst(instantiation map (ab => SubstitutionPair(ab._1, ab._2)))), 0)

  private def collectBounds(assms: IndexedSeq[Formula])(lowers0: BoundMap, uppers0: BoundMap) : (BoundMap, BoundMap) =
  (assms,assms.indices).zipped.foldLeft(lowers0, uppers0) { (lue: (BoundMap, BoundMap), assmi) =>
    (lue, assmi) match {
      case ((lowers, uppers), (assm, i)) =>
        assm match {
          case LessEqual(t, n) if isNumeric(n) =>
            (lowers, uppers.updated(t, ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(assm))).apply(Close(AntePos(i), SuccPos(0)), 0)))
          case LessEqual(n, t) if isNumeric(n) =>
            (lowers.updated(t, ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(assm))).apply(Close(AntePos(i), SuccPos(0)), 0)), uppers)
          case Equal(t, n) if isNumeric(n) =>
            (lowers.updated(t, extract_bound(assms, i, LessEqual(n, t), eqBound2, (t_f, t) :: (t_g, n) :: Nil)),
              uppers.updated(t, extract_bound(assms, i, LessEqual(t, n), eqBound1, (t_f, t) :: (t_g, n) :: Nil)))
          case Equal(n, t) if isNumeric(n) =>
            (lowers.updated(t, extract_bound(assms, i, LessEqual(n, t), eqBound1, (t_f, n) :: (t_g, t) :: Nil)),
              uppers.updated(t, extract_bound(assms, i, LessEqual(t, n), eqBound2, (t_f, n) :: (t_g, t) :: Nil)))
          case Less(t, n) if isNumeric(n) =>
            (lowers, uppers.updated(t, extract_bound(assms, i, LessEqual(t, n), ltBound, (t_f, t) :: (t_g, n) :: Nil)))
          case Less(n, t) if isNumeric(n) =>
            (lowers.updated(t, extract_bound(assms, i, LessEqual(n, t), ltBound, (t_f, n) :: (t_g, t) :: Nil)), uppers)
          case Greater(t, n) if isNumeric(n) =>
            (lowers.updated(t, extract_bound(assms, i, LessEqual(n, t), gtBound, (t_f, t) :: (t_g, n) :: Nil)), uppers)
          case Greater(n, t) if isNumeric(n) =>
            (lowers, uppers.updated(t, extract_bound(assms, i, LessEqual(t, n), gtBound, (t_f, n) :: (t_g, t) :: Nil)))
          case GreaterEqual(t, n) if isNumeric(n) =>
            (lowers.updated(t, extract_bound(assms, i, LessEqual(n, t), geBound, (t_f, t) :: (t_g, n) :: Nil)), uppers)
          case GreaterEqual(n, t) if isNumeric(n) =>
            (lowers, uppers.updated(t, extract_bound(assms, i, LessEqual(t, n), geBound, (t_f, n) :: (t_g, t) :: Nil)))
          case _ =>
            (lowers, uppers)
        }
    }
  }


  /** Proves Bounds on all Subexpressions using Interval Arithmetic.
    *
    * @param prec          decimal precision
    * @param qeTool        Tool for QE, it will only be called on formulas without variables and without quantifiers
    * @param assms         list of constraints on variables, equalities can be used to abbreviate terms
    * @param include_assms if assms need to be added to lowers/uppers (False if re-using precomputed bounds)
    * @param lowers0       precomputed bounds (can be used for cacheing results)
    * @param uppers0       dito
    * @param terms         terms whose subexpressions shall be bounded
    * @return bounds on all subexpressions
    *
    * */
  def proveBounds(prec: Int)
                 (qeTool: QETacticTool)
                 (assms: IndexedSeq[Formula])
                 (include_assms: Boolean)
                 (lowers0: BoundMap, uppers0: BoundMap, ssaMap: Map[Variable, Term])
                 (terms: Seq[Term]): (BoundMap, BoundMap) = {
    // collect bounds from assms
    val (newlowers: BoundMap, newuppers: BoundMap) =
      if(!include_assms) (lowers0, uppers0)
      else collectBounds(assms)(lowers0, uppers0)
    // recurse over the structure of t and compute new bounds
    terms.foldLeft(newlowers, newuppers)((a, t: Term) => recurse(prec)(qeTool)(assms)(a._1, a._2, ssaMap)(t))
  }

  private def proveCompBoth(qeTool: QETacticTool, leBoth: ProvableSig, provable: ProvableSig, bound1: ProvableSig, bound2: ProvableSig) : Option[ProvableSig] = {
    val le_prv = qeTool.qe(leBoth.conclusion.ante(0).asInstanceOf[And].right.asInstanceOf[Equiv].left).fact
    le_prv.conclusion.succ(0) match {
      case Equiv(a, True) => Some(
        CutHide(leBoth.conclusion.ante(0))(provable).
          apply(AndRight(SuccPos(0)), 1).
          apply(CoHideRight(SuccPos(0)), 2).
          apply(le_prv, 2).
          apply(AndRight(SuccPos(0)), 1).
          apply(bound2, 2).
          apply(bound1, 1).
          apply(leBoth, 0)
      )
      case _ => None
    }
  }

  def proveComparison(prec: Int)
                 (qeTool: QETacticTool)
                 (assms: IndexedSeq[Formula])
                 (include_assms: Boolean)
                 (lowers0: BoundMap, uppers0: BoundMap, ssaMap: Map[Variable, Term])
                 (fml: ComparisonFormula): (BoundMap, BoundMap, Option[ProvableSig]) =
  {
    val a = fml.left
    val b = fml.right
    val (lowers, uppers) = proveBounds(prec)(qeTool)(assms)(include_assms)(lowers0, uppers0, ssaMap)(List(a, b))
    val ff_prv = lowers(a)
    val gg_prv = lowers(b)
    val F_prv = uppers(a)
    val G_prv = uppers(b)
    val gg_fml = gg_prv.conclusion.succ(0).asInstanceOf[ComparisonFormula]
    val ff_fml = ff_prv.conclusion.succ(0).asInstanceOf[ComparisonFormula]
    val F_fml = F_prv.conclusion.succ(0).asInstanceOf[ComparisonFormula]
    val G_fml = G_prv.conclusion.succ(0).asInstanceOf[ComparisonFormula]
    val f = ff_fml.right
    val g = gg_fml.right
    val ff = ff_fml.left
    val gg = gg_fml.left
    val F = F_fml.right
    val G = G_fml.right
    val provable = ProvableSig.startPlainProof(Sequent(assms, IndexedSeq(fml.reapply(f, g))))
    (lowers, uppers,
      fml match {
        case _: LessEqual =>
          proveCompBoth(qeTool,
            leBothSeq.apply(USubst((List(t_f, t_F, t_gg, t_g), List(f, F, gg, g)).zipped map SubstitutionPair)),
            provable, F_prv, gg_prv)
        case _: Less =>
          proveCompBoth(qeTool,
            ltBothSeq.apply(USubst((List(t_f, t_F, t_gg, t_g), List(f, F, gg, g)).zipped map SubstitutionPair)),
            provable, F_prv, gg_prv)
        case _: GreaterEqual =>
          proveCompBoth(qeTool,
            geBothSeq.apply(USubst((List(t_f, t_ff, t_G, t_g), List(f, ff, G, g)).zipped map SubstitutionPair)),
            provable, G_prv, ff_prv)
        case _: Greater =>
          proveCompBoth(qeTool,
            gtBothSeq.apply(USubst((List(t_f, t_ff, t_G, t_g), List(f, ff, G, g)).zipped map SubstitutionPair)),
            provable, G_prv, ff_prv)
      })
  }

  def proveBool(prec: Int)
               (qeTool: QETacticTool)
               (assms: IndexedSeq[Formula])
               (include_assms: Boolean)
               (lowers0: BoundMap, uppers0: BoundMap, ssa: StaticSingleAssignmentExpression[Formula])
               (fml: Formula): (BoundMap, BoundMap, Option[ProvableSig]) = fml match {
    case And(a, b) =>
      val (lowers1, uppers1, prv1o) = proveBool(prec)(qeTool)(assms)(include_assms)(lowers0, uppers0, ssa)(a)
      val (lowers2, uppers2, prv2o) = proveBool(prec)(qeTool)(assms)(include_assms)(lowers1, uppers1, ssa)(b)
      (prv1o, prv2o) match {
        case (Some(prv1), Some(prv2)) =>
          val fml1 = prv1.conclusion.succ(0)
          val fml2 = prv2.conclusion.succ(0)
          (lowers2, uppers2, Some(ProvableSig.startPlainProof(Sequent(assms,IndexedSeq(And(fml1, fml2))))(AndRight(SuccPos(0)), 0)(prv2, 1)(prv1, 0)))
        case _ => (lowers2, uppers2, None)
      }
    case Or(a, b) =>
      val (lowers1, uppers1, prv1o) = proveBool(prec)(qeTool)(assms)(include_assms)(lowers0, uppers0, ssa)(a)
      prv1o match {
        case Some(prv1) =>
          val fml1 = prv1.conclusion.succ(0)
          val fml2 = ssa.unfold(b)
          (lowers1, uppers1, Some(ProvableSig.startPlainProof(Sequent(assms,IndexedSeq(Or(fml1, fml2))))(OrRight(SuccPos(0)), 0)(HideRight(SuccPos(1)), 0)(prv1, 0)))
        case None =>
          val (lowers2, uppers2, prv2o) = proveBool(prec)(qeTool)(assms)(include_assms)(lowers1, uppers1, ssa)(b)
          prv2o match {
            case Some(prv2) =>
              val fml1 = ssa.unfold(a)
              val fml2 = prv2.conclusion.succ(0)
              (lowers2, uppers2, Some(ProvableSig.startPlainProof(Sequent(assms,IndexedSeq(Or(fml1, fml2))))(OrRight(SuccPos(0)), 0)(HideRight(SuccPos(0)), 0)(prv2, 0)))
          }
      }
    case cfml: ComparisonFormula =>
      proveComparison(prec)(qeTool)(assms)(include_assms)(lowers0, uppers0, ssa.unfoldMap)(cfml)
    case _ =>
      throw new TacticInapplicableFailure("intervalArithmeticBool requires conjunction, disjunction, or comparison")
  }

  private def requireOneSubgoal(prv: ProvableSig, who: String) : Unit =
    require(prv.subgoals.length == 1, who + " only works on one sequent at a time.")

  private def requireOneSucc(seq: Sequent, who: String) : Unit =
    require(seq.succ.length == 1, who + " requires exactly one formula in the succedent.")

  private lazy val equivIff = proveBy("(p()<->q())<->(p()&q())|(!p()&!q())".asFormula, prop & done)
  private lazy val equalIff = proveBy("(f()=g())<->f()<=g()&f()>=g()".asFormula, QE & done)
  private lazy val notEqual = proveBy("(!f()=g())<->f()<g()|f()>g()".asFormula, QE & done)

  private[btactics] def intervalArithmeticPreproc: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    def unsupportedError(e: Expression) = throw new TacticInapplicableFailure("Interval Arithmetic does not support " + e.getClass.getSimpleName)
    seq.sub(pos) match {
      case Some(e) =>
        e match {
          case And(f, g) =>
            intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
              intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
          case Or(f, g) =>
            intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
              intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
          case Imply(f, g) =>
            useAt(Ax.implyExpand, PosInExpr(0 :: Nil))(pos) &
              intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
              intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
          case Equiv(f, g) =>
            useAt(equivIff, PosInExpr(0 :: Nil))(pos) &
              intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
              intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
          case Equal(f, g) =>
            useAt(equalIff, PosInExpr(0 :: Nil))(pos)
          case Not(fml) =>
            fml match {
              case And(f, g) =>
                useAt(Ax.notAnd, PosInExpr(0 :: Nil))(pos) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
              case Or(f, g) =>
                useAt(Ax.notOr, PosInExpr(0 :: Nil))(pos) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
              case Imply(f, g) =>
                useAt(Ax.notImply, PosInExpr(0 :: Nil))(pos) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
              case Equiv(f, g) =>
                useAt(Ax.notEquiv, PosInExpr(0 :: Nil))(pos) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(0 :: Nil)) &
                  intervalArithmeticPreproc(pos ++ PosInExpr(1 :: Nil))
              case Not(f) =>
                useAt(Ax.doubleNegation, PosInExpr(0::Nil))(pos) &
                  intervalArithmeticPreproc(pos)
              case Equal(f, g) =>
                useAt(notEqual, PosInExpr(0 :: Nil))(pos)
              case Less(a, b) =>
                useAt(Ax.notLess, PosInExpr(0 :: Nil))(pos)
              case LessEqual(a, b) =>
                useAt(Ax.notLessEqual, PosInExpr(0 :: Nil))(pos)
              case Greater(a, b) =>
                useAt(Ax.notGreater, PosInExpr(0 :: Nil))(pos)
              case GreaterEqual(a, b) =>
                useAt(Ax.notGreaterEqual, PosInExpr(0 :: Nil))(pos)
              case _ => unsupportedError(fml)
            }
          case Less(a, b) => nil
          case LessEqual(a, b) => nil
          case Greater(a, b) => nil
          case GreaterEqual(a, b) => nil
          case e => unsupportedError(e)
        }
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  }

  private[btactics] def intervalArithmeticBool(precision: Int, qeTool: => QETacticTool, doSSA: Boolean = true) : BuiltInRightTactic =
    anon { (prv: ProvableSig, pos: SuccPosition) =>
      requireOneSubgoal(prv, "intervalArithmeticBool")
      pos.checkTop
      val seq = prv.subgoals(0)
      requireOneSucc(seq, "intervalArithmeticBool")
      val (ssa, fml) = if (doSSA) {
        val s = new StaticSingleAssignmentExpression(seq.succ(0))
        (s, s.expression)
      } else {
        (new StaticSingleAssignmentExpression[Formula](True), seq.succ(0))
      }
      proveBool(precision)(qeTool)(seq.ante)(true)(BoundMap, BoundMap, ssa)(fml) match {
        case (_, _, Some(prvIa)) =>
          prv(Cut(prvIa.conclusion.succ(0)), 0)(HideRight(SuccPos(0)), 1)(prvIa, 1)(Close(AntePos(seq.ante.length), SuccPos(0)), 0)
        case _ =>
          throw new TacticInapplicableFailure("Interval Arithmetic cannot close the goal.")
      }
    }

  @Tactic("Interval Arithmetic",
    displayLevel = "menu"
  )
  lazy val intervalArithmetic: BelleExpr = anon {
    val precision = 15 // @todo: precision as (optional) argument?
    SaturateTactic((orRi |! skip)) &
      intervalArithmeticPreproc(1) &
      intervalArithmeticBool(precision, ToolProvider.qeTool().get, true)(1)
  }

  def intervalCutTerms(terms: Seq[Term]): BuiltInTactic = anon ((provable: ProvableSig) => {
    requireOneSubgoal(provable, "intervalCutTerms")
    val sequent = provable.subgoals(0)
    val nantes = sequent.ante.length
    val prec = 5
    val qe = ToolProvider.qeTool().get
    val bnds = proveBounds(prec)(qe)(sequent.ante)(true)(BoundMap(), BoundMap(), Map())(terms.toIndexedSeq)
    val prvs = terms flatMap (t => List(bnds._1(t), bnds._2(t)))
    (prvs, prvs.indices).zipped.foldLeft(provable) {
      (result, prvi) => prvi match {
        case (prv: ProvableSig, i: Int) =>
        (0 until i).foldLeft(result.apply(Cut(prv.conclusion.succ(0)), 0).apply(HideRight(SuccPos(0)), 1)){
            (res, _) => res.apply(HideLeft(AntePos(nantes)), 1)
          }.apply(prv, 1)
      }
    }
  })

  @Tactic("Interval Arithmetic Cut",
    codeName = "intervalCutTerms" /* @todo old codeName */,
    // @TODO: closed premise
    premises = "Γ, lower(t)<=t, t<=upper(t) |- Δ",
    conclusion = "Γ |- Δ",
    displayLevel = "menu"
  )
  def intervalCutTerm(t: Term): InputTactic = inputanon { intervalCutTerms(Seq(t)) }

  private def terms_of(fml: Formula) : List[Term] = fml match {
    case fml: BinaryCompositeFormula => terms_of(fml.left) ++ terms_of(fml.right)
    case fml: UnaryCompositeFormula => terms_of(fml.child)
    case fml: PredOf => List(fml.child)
    case fml: PredicationalOf => terms_of(fml.child)
    case fml: ComparisonFormula => List(fml.left, fml.right)
    case _ => List()
  }

  @Tactic("Interval Arithmetic Cut",
    premises = "Γ, lower(t)<=t, t<=upper(t) |- Δ",
    conclusion = "Γ |- Δ",
    displayLevel = "internal"
  )
  val intervalCut : DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    seq.sub(pos) match {
      case Some(fml: Formula) => intervalCutTerms(terms_of(fml))
      case Some(t: Term) => intervalCutTerms(Seq(t))
      case Some(e) => throw new TacticInapplicableFailure("intervalCut only applicable to formulas or terms, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  }

  /** prove formula of the following shape
    * context |- \forall i1 i2 ((l1 <= i1 & i1 <= u1 & l2 <= i2 & i2 <= u2) -> (l <= op(i1, i2) & op(i1, i2) <= u))
    * */
  def proveBinop(qeTool: => QETacticTool)(prec: Int)(context: IndexedSeq[Formula])(op: (Term, Term) => Term)(l1: Term, u1: Term)(l2: Term, u2: Term) : (ProvableSig, Term, Term) = {
    val i1 = BaseVariable("i1_")
    val i2 = BaseVariable("i2_")
    val assms = IndexedSeq((l1, i1), (i1, u1), (l2, i2), (i2, u2)).map{case(l, u)=>LessEqual(l, u)}
    val t = op(i1, i2)
    // @todo: could be more efficient in caching bounds for context
    val (lowers, uppers) = IntervalArithmeticV2.proveBounds(prec)(qeTool)(context++assms)(true)(IntervalArithmeticV2.BoundMap(), IntervalArithmeticV2.BoundMap(), Map())(Seq(t))
    val lPrv = lowers(t)
    val uPrv = uppers(t)
    val l = lPrv.conclusion.succ(0).asInstanceOf[ComparisonFormula].left
    val u = uPrv.conclusion.succ(0).asInstanceOf[ComparisonFormula].right
    val fml =
      Forall(Seq(i1), Forall(Seq(i2),
        Imply(
          assms.reduceRight(And),
          And(LessEqual(l, t), LessEqual(t, u))
        )
      ))
    val offset = context.length
    (ProvableSig.startPlainProof(Sequent(context, IndexedSeq(fml))).
      apply(Skolemize(SuccPos(0)), 0).
      apply(Skolemize(SuccPos(0)), 0).
      apply(ImplyRight(SuccPos(0)), 0).
      apply(AndLeft(AntePos(offset + 0)), 0).
      apply(AndLeft(AntePos(offset + 1)), 0).
      apply(AndLeft(AntePos(offset + 2)), 0).
      apply(AndRight(SuccPos(0)), 0).
      apply(uPrv, 1).
      apply(lPrv, 0), l, u)
  }

  /** prove formula of the following shape
    * context |- \forall i1 ((l1 <= i1 & i1 <= u1) -> (l <= op(i1) & op(i1) <= u))
    * */
  def proveUnop(qeTool: => QETacticTool)(prec: Int)(context: IndexedSeq[Formula])(op: Term => Term)(l1: Term, u1: Term) : (ProvableSig, Term, Term) = {
    val i1 = BaseVariable("i1_")
    val assms = IndexedSeq((l1, i1), (i1, u1)).map{case(l, u)=>LessEqual(l, u)}
    val t = op(i1)
    val (lowers, uppers) = IntervalArithmeticV2.proveBounds(prec)(qeTool)(context++assms)(true)(IntervalArithmeticV2.BoundMap(), IntervalArithmeticV2.BoundMap(), Map())(Seq(t))
    val lPrv = lowers(t)
    val uPrv = uppers(t)
    val l = lPrv.conclusion.succ(0).asInstanceOf[ComparisonFormula].left
    val u = uPrv.conclusion.succ(0).asInstanceOf[ComparisonFormula].right
    val fml = Forall(Seq(i1),
      Imply(
        assms.reduceRight(And),
        And(LessEqual(l, t), LessEqual(t, u))
      ))
    val offset = context.length
    (ProvableSig.startPlainProof(Sequent(context, IndexedSeq(fml))).
      apply(Skolemize(SuccPos(0)), 0).
      apply(ImplyRight(SuccPos(0)), 0).
      apply(AndLeft(AntePos(offset + 0)), 0).
      apply(AndRight(SuccPos(0)), 0).
      apply(uPrv, 1).
      apply(lPrv, 0),
      l, u)
  }

  /** Tactics appear to be a bit slow */
  object Slow {

    def usubst_append(ts: List[(Term, Term)])(uso: Option[Subst]) = {
      val renUsubst = RenUSubst(USubst(ts.map(s => (SubstitutionPair(s._1, s._2)))))
      uso match {
        case Some(us) => us ++ renUsubst
        case None => renUsubst
      }
    }

    def negDown(bound: Term) =
      useAt(Ax.intervalDownNeg, PosInExpr(1::Nil), usubst_append((t_F, bound) :: Nil)(_))(1)

    def negUp(bound: Term) =
      useAt(Ax.intervalUpNeg, PosInExpr(1::Nil), usubst_append((t_ff, bound) :: Nil)(_))(1)

    def plusDown(bound1: Term, bound2: Term) =
      useAt(Ax.intervalDownPlus, PosInExpr(1::Nil), usubst_append((t_ff, bound1) :: (t_gg, bound2) :: Nil)(_))(1)

    def plusUp(bound1: Term, bound2: Term) =
      useAt(Ax.intervalUpPlus, PosInExpr(1::Nil), usubst_append((t_F, bound1) :: (t_G, bound2) :: Nil)(_))(1)

    def minusDown(bound1: Term, bound2: Term) =
      useAt(Ax.intervalDownMinus, PosInExpr(1::Nil), usubst_append((t_ff, bound1) :: (t_G, bound2) :: Nil)(_))(1)

    def minusUp(bound1: Term, bound2: Term) =
      useAt(Ax.intervalUpMinus, PosInExpr(1::Nil), usubst_append((t_F, bound1) :: (t_gg, bound2) :: Nil)(_))(1)

    def timesDown(ff: Term, F: Term, gg: Term, G: Term) =
      useAt(Ax.intervalDownTimes, PosInExpr(1::Nil),
        usubst_append((t_ff, ff) :: (t_F, F) :: (t_gg, gg) :: (t_G, G) :: Nil)(_))(1)

    def timesUp(ff: Term, F: Term, gg: Term, G: Term) =
      useAt(Ax.intervalUpTimes, PosInExpr(1::Nil),
        usubst_append((t_ff, ff) :: (t_F, F) :: (t_gg, gg) :: (t_G, G) :: Nil)(_))(1)

    def leBoth(F: Term, gg: Term) =
      useAt(Ax.intervalLEBoth, PosInExpr(1::Nil), usubst_append((t_F, F) :: (t_gg, gg) :: Nil)(_))(1)

    def lessBoth(F: Term, gg: Term) =
      useAt(Ax.intervalLBoth, PosInExpr(1::Nil), usubst_append((t_F, F) :: (t_gg, gg) :: Nil)(_))(1)

    //Note: Tactic previously named eqL2R_last
    def eqL2R_dep = anon { (pos: Position) =>
      eqL2R(pos.checkAnte)(1) // TODO: what about that subgoal 1?
    }

    //Note: Tactic previously slowIntervalArithmetic
    val intervalArithmetic = anon { seq: Sequent =>
      requireOneSucc (seq, "slowIntervalArithmetic")
      val prec = 5
      val bounds = collect_bounds(prec,DecimalBounds(), seq.ante)

      // TODO: should be cacheing bounds for subterms, but it seems we can easily afford excessive BigDecimal computations
      // recurse to find a lower bound for the expression on the rhs
      // Note: previously named "slowIntervalArithmetic.recurseLower"
      def recurseLower: BelleExpr = anon {
        seq: Sequent =>
          seq.succ(0) match {
            case LessEqual(_, Plus(a, b)) =>
              val aa = eval_ivl_term_in_env(prec)(bounds)(a)._1
              val bb = eval_ivl_term_in_env(prec)(bounds)(b)._1
              plusDown(aa, bb) & andR(1) & Idioms.<(andR(1) & Idioms.<(recurseLower, recurseLower), QE & done)
            case LessEqual(_, Minus(a, b)) =>
              val aa = eval_ivl_term_in_env(prec)(bounds)(a)._1
              val bB = eval_ivl_term_in_env(prec)(bounds)(b)._2
              minusDown(aa, bB) & andR(1) & Idioms.<(andR(1) & Idioms.<(recurseLower, recurseUpper), QE & done)
            case LessEqual(_, Neg(a)) =>
              val aA = eval_ivl_term_in_env(prec)(bounds)(a)._2
              negDown(aA) & andR(1) & Idioms.<(recurseUpper, QE & done)
            case LessEqual(_, Times(f, g)) =>
              val (ff, fF) = eval_ivl_term_in_env(prec)(bounds)(f)
              val (gg, gG) = eval_ivl_term_in_env(prec)(bounds)(g)
              timesDown(ff, fF, gg, gG) & andR(1) & Idioms.<(
                andR(1) & Idioms.<(andR(1)&Idioms.<(recurseLower, recurseUpper), andR(1)&Idioms.<(recurseLower, recurseUpper)),
                QE & done)
            case LessEqual(_, x) if bounds._1.isDefinedAt(x) => QE & done
            case LessEqual(_, n) if isNumeric(n) => QE & done
            case _ => throw new TacticInapplicableFailure("recurseLower went wrong")
          }
      }
      // recurse to find an upper bound for the expression on the lhs
      // Note: Previously named "slowIntervalArithmetic.recurseUpper"
      def recurseUpper: BelleExpr = anon {
        seq: Sequent =>
          seq.succ(0) match {
            case LessEqual(Plus(a, b), _) =>
              val aA = eval_ivl_term_in_env(prec)(bounds)(a)._2
              val bB = eval_ivl_term_in_env(prec)(bounds)(b)._2
              plusUp(aA, bB) & andR(1) & Idioms.<(andR(1) & Idioms.<(recurseUpper, recurseUpper), QE & done)
            case LessEqual(Minus(a, b), _) =>
              val aA = eval_ivl_term_in_env(prec)(bounds)(a)._2
              val bb = eval_ivl_term_in_env(prec)(bounds)(b)._1
              minusUp(aA, bb) & andR(1) & Idioms.<(andR(1) & Idioms.<(recurseUpper, recurseLower), QE & done)
            case LessEqual(Neg(a), _) =>
              val aa = eval_ivl_term_in_env(prec)(bounds)(a)._1
              negUp(aa) & andR(1) & Idioms.<(recurseLower, QE & done)
            case LessEqual(Times(f, g), _) =>
              val (ff, fF) = eval_ivl_term_in_env(prec)(bounds)(f)
              val (gg, gG) = eval_ivl_term_in_env(prec)(bounds)(g)
              //       h()<=f()*g()  <- (((ff()<=f() & f()<=F()) & (gg()<=g() & g()<=G())) & (h()<=ff()*gg() & h()<=ff()*G() & h()<=F()*gg() & h()<=F()*G()))
              timesUp(ff, fF, gg, gG) & andR(1) & Idioms.<(
                andR(1) & Idioms.<(andR(1)&Idioms.<(recurseLower, recurseUpper), andR(1)&Idioms.<(recurseLower, recurseUpper)),
                QE & done)
            case LessEqual(x, _) if bounds._1.isDefinedAt(x) => QE & done
            case LessEqual(n, _) if isNumeric(n) => QE & done
            case _ => throw new TacticInapplicableFailure("recurseUpper went wrong")
          }
      }
      // Note: previously named "slowIntervalArithmetic.recurseFormula"
      def recurseFormula: BelleExpr = anon {
        (seq: Sequent) =>
          (seq.succ(0) match {
            case And(_, _) => andR(1) & Idioms.<(recurseFormula, recurseFormula)
            case LessEqual(a, b) =>
              val aA = eval_ivl_term_in_env(prec)(bounds)(a)._2
              val bb = eval_ivl_term_in_env(prec)(bounds)(b)._1
              leBoth(aA, bb) & andR(1) & Idioms.<(andR(1) & Idioms.<(recurseUpper, recurseLower), QE & done)
            case Less(a, b) =>
              val aA = eval_ivl_term_in_env(prec)(bounds)(a)._2
              val bb = eval_ivl_term_in_env(prec)(bounds)(b)._1
              lessBoth(aA, bb) & andR(1) & Idioms.<(andR(1) & Idioms.<(recurseUpper, recurseLower), QE & done)
            case _ => throw new TacticInapplicableFailure("recurseFormula went wrong")
          })
      }
      recurseFormula
    }

  }

}
