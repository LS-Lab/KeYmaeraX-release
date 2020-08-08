package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BranchTactic, OnAll, SaturateTactic}
import edu.cmu.cs.ls.keymaerax.btactics.{Ax, DebuggingTactics, PolynomialArithV2, SimplifierV3, TacticFactory}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool

import scala.annotation.tailrec
import scala.collection.immutable.{HashSet, IndexedSeq}
import scala.collection.mutable.ListBuffer

/** Assesses dL terms and formulas for equality, equivalence, implication etc. with restricted automation. */
object AssessmentProver {

  /** Builtin assessment modes */
  object Modes {
    /** Equality of real values. */
    val VALUE_EQ: String = "valueeq"
    /** Syntactic equality. */
    val SYN_EQ: String = "syneq"
    /** Polynomial equality. */
    val POLY_EQ: String = "polyeq"
    /** Equivalent by QE. */
    val QE_EQUIV: String = "qeEquivalence"
    /** DI premise check. */
    val DI_PREMISE: String = "dipremise"
    /** DI with additional free variables check. */
    val DI: String = "di"
    /** Program equivalence. */
    val PRG_EQUIV = "prgequiv"
    /** Provable using a tactic. */
    val BELLE_PROOF: String = "prove"
    val modes: Set[String] = Set(SYN_EQ, POLY_EQ, BELLE_PROOF)
  }

  /** Assessment prover input artifacts (expressions, sequents etc.) */
  abstract class Artifact
  case class ExpressionArtifact(expr: Expression) extends Artifact
  case class ListExpressionArtifact(exprs: List[Expression]) extends Artifact
  case class SequentArtifact(goals: List[Sequent]) extends Artifact

  /** Proves equivalence of `a` and `b` by QE. */
  def qeEquivalence(a: Formula, b: Formula): ProvableSig = {
    KeYmaeraXProofChecker(5000)(QE)(Sequent(IndexedSeq.empty, IndexedSeq(Equiv(a, b))))
  }

  /** Compares terms `a` and `b` for having the same real values. */
  def valueEquality(a: Term, b: Term): ProvableSig = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(a, b))

  /** Compares terms in lists `a` and `b` pairwise for the same real value. */
  def valueEquality(a: List[Term], b: List[Term]): ProvableSig = {
    require(a.nonEmpty && a.length == b.length, "Same-length non-empty lists expected, but got " + a.mkString(",") + " vs. " + b.mkString(","))
    ProvableSig.proveArithmetic(BigDecimalQETool, a.zip(b).map({ case (a, b) => Equal(a, b) }).reduceRight(And))
  }

  /** Proves polynomial equality of `a` and `b`. */
  def polynomialEquality(a: Term, b: Term): ProvableSig = {
    KeYmaeraXProofChecker(5000)(PolynomialArithV2.equate(1))(Sequent(IndexedSeq.empty, IndexedSeq(Equal(a, b))))
  }

  /** Collects terms and compares for polynomial equality. Checks parent operators along the way. */
  def polynomialEquality(a: Formula, b: Formula, normalize: Boolean): ProvableSig = {
    val terms = ListBuffer.empty[(PosInExpr, Equal)]
    val doNormalize = new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
        if (e.isFOL) {
          Right(SimplifierV3.semiAlgNormalize(e)._1)
        } else Left(None)
      }
    }
    val na = if (normalize) ExpressionTraversal.traverse(doNormalize, a).get else a
    val nb = if (normalize) ExpressionTraversal.traverse(doNormalize, b).get else b

    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = {
        //@note avoids comparing sub-terms
        if (!terms.lastOption.exists({ case (last, _) => p.pos.startsWith(last.pos) })) {
          val f = nb.sub(p) match {
            case Some(t: Term) => t
            case t => throw new IllegalArgumentException("Formulas differ at position " + p.prettyString + ": expected " + e.prettyString + ", but got " + t.map(_.prettyString))
          }
          terms.append((p, Equal(e, f)))
        }
        Left(None)
      }
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
        require(nb.sub(p).map(_.getClass).contains(e.getClass), "Formula operators do not match at position '" + p.prettyString + "'; expected " + e.prettyString + " (" + e.getClass.getSimpleName + ") but got " + nb.sub(p).map(f => f.prettyString + " (" + f.getClass.getSimpleName + ")").getOrElse("none"))
        Left(None)
      }
      override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = {
        require(nb.sub(p).map(_.getClass).contains(e.getClass), "Program operators do not match at position '" + p.prettyString + "'; expected " + e.prettyString + " (" + e.getClass.getSimpleName + ") but got " + nb.sub(p).map(f => f.prettyString + " (" + f.getClass.getSimpleName + ")").getOrElse("none"))
        Left(None)
      }
    }, na)

    val (realTerms, otherTerms) = terms.partition({ case (_, Equal(l, r)) => l.sort == Real && r.sort == Real })
    require(otherTerms.forall({ case (_, Equal(l, r)) => l == r }), "Expected all non-Real terms to be syntactically equal, but got " + otherTerms.mkString(","))

    if (realTerms.nonEmpty) {
      val combined = realTerms.map(_._2).reduceRight(And)
      val lemmas = realTerms.map({ case (_, e) => polynomialEquality(e.left, e.right) }).map(byUS)
      prove(Sequent(IndexedSeq(), IndexedSeq(combined)), OnAll(andR('R) | nil) * (realTerms.size - 1) & BranchTactic(lemmas))
    } else {
      //@note formulas without terms, such as true/false or [ctrl;]true
      syntacticEquality(a, b)
    }
  }

  /** Proves polynomial equality between the terms resulting from chasing simple programs in `a` and `b`. */
  def polynomialEquality(a: Sequent, b: Sequent, normalize: Boolean): ProvableSig = {
    polynomialEquality(a.toFormula, b.toFormula, normalize)
  }

  /** Compares expressions for syntactic equality. */
  def syntacticEquality(a: Expression, b: Expression): ProvableSig = (a, b) match {
    case (af: Formula, bf: Formula) => KeYmaeraXProofChecker(1000)(useAt(Ax.equivReflexive)(1))(Sequent(IndexedSeq(), IndexedSeq(Equiv(af, bf))))
    case (at: Term, bt: Term) => KeYmaeraXProofChecker(1000)(useAt(Ax.equalReflexive)(1))(Sequent(IndexedSeq(), IndexedSeq(Equal(at, bt))))
  }
  /** Compares sequents for syntactic equality. */
  def syntacticEquality(a: List[Sequent], b: List[Sequent]): ProvableSig = {
    require(b.nonEmpty && a.size == b.size, "Cannot check empty lists of sequents or sequent lists of different size")
    val fmls = a.zip(b).map({ case (as, bs) =>
      val edistinct = Sequent(bs.ante.distinct, bs.succ.distinct)
      (sequentToFormula(as, edistinct), edistinct.toFormula)
    })
    syntacticEquality(fmls.map(_._1).reduceRight(And), fmls.map(_._2).reduceRight(And))
  }

  def dIPremiseCheck(a: Formula, b: Formula, diffAssignsMandatory: Boolean, normalize: Boolean): ProvableSig = {
    if (diffAssignsMandatory) {
      def collectDiffAssigns(f: Formula) = {
        val diffAssigns = ListBuffer.empty[Program]
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
            case a@Assign(_: DifferentialSymbol, _) =>
              diffAssigns.append(a)
              Left(None)
            case _: Compose => Left(None)
            case _ => throw new IllegalArgumentException("Only (compositions of) differential assignments allowed in dI result, but found " + e.prettyString)
          }
        }, f)
        diffAssigns.toList
      }

      val ads = collectDiffAssigns(a).map({ case Assign(d: DifferentialSymbol, _) => d }).toSet
      val bds = collectDiffAssigns(b).map({ case Assign(d: DifferentialSymbol, _) => d }).toSet
      require(ads == bds, "Differential assignments do not match: expected assignments to " + ads.map(_.prettyString).mkString(",") + " but found " + (if (bds.isEmpty) "none" else bds.map(_.prettyString).mkString(",")))
    }

    val ap: ProvableSig = KeYmaeraXProofChecker(1000)(chase(1))(Sequent(IndexedSeq(), IndexedSeq(a)))
    val bp: ProvableSig = KeYmaeraXProofChecker(1000)(chase(1))(Sequent(IndexedSeq(), IndexedSeq(b)))
    polynomialEquality(ap.subgoals.head, bp.subgoals.head, normalize)
  }

  def dIPremiseCheck(a: Sequent, b: Sequent, diffAssignsMandatory: Boolean, normalize: Boolean): ProvableSig = {
    dIPremiseCheck(a.toFormula match {
      case Imply(True, fml) => fml
      case f => f
    }, b.toFormula match {
      case Imply(True, fml) => fml
      case f => f
    }, diffAssignsMandatory, normalize)
  }

  /** Checks `inv` for being a differential invariant of `ode`. */
  def dICheck(ode: ODESystem, inv: Formula): ProvableSig = {
    require(!StaticSemantics.freeVars(SimplifierV3.formulaSimp(inv, HashSet.empty,
      SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1).isEmpty, "Invariant " + inv.prettyString + " does not mention free variables")
    KeYmaeraXProofChecker(5000)(dI(auto='cex)(1))(Sequent(IndexedSeq(inv), IndexedSeq(Box(ode, inv))))
  }

  /** Checks program equivalence by `[a;]P <-> [b;]P.` */
  def prgEquivalence(a: Program, b: Program): ProvableSig = {
    val p = PredOf(Function("P", None, Unit, Bool), Nothing)
    def searchCMon(at: PosInExpr) = TacticFactory.anon { (seq: Sequent) =>
      val anteCtxs = seq.ante.map(_.at(at)._1).zipWithIndex
      val succCtxs = seq.succ.map(_.at(at)._1).zipWithIndex
      val anteMatch = anteCtxs.find({ case (ctx, _) => succCtxs.exists(_._1 == ctx) })
      val succMatch = succCtxs.find({ case (ctx, _) => anteMatch.exists(_._1 == ctx) })
      anteMatch.map({ case (_, i) => cohideOnlyL(AntePos(i)) }).getOrElse(skip) &
        succMatch.map({ case (_, i) => cohideOnlyR(SuccPos(i)) }).getOrElse(skip) &
        implyRi & CMon(PosInExpr(1::Nil))
    }
    KeYmaeraXProofChecker(5000)(chase(1,0::Nil) & chase(1,1::Nil) &
      SaturateTactic(OnAll(prop & OnAll(searchCMon(PosInExpr(1::Nil))))))(Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(a, p), Box(b, p)))))
  }

  /** Generic assessment prover uses tactic `t` to prove sequent `s`, aborting after `timeout` time. */
  def prove(s: Sequent, t: BelleExpr): ProvableSig = {
    KeYmaeraXProofChecker(5000)(t)(s)
  }

  /** Checks whether artifact `have` fits artifact `expected` using `mode`. */
  def check(have: Artifact, expected: Artifact, mode: Option[String], args: Map[String, String]): ProvableSig = mode.getOrElse(Modes.SYN_EQ) match {
    case Modes.SYN_EQ => (have, expected) match {
      case (ExpressionArtifact(h), ExpressionArtifact(e)) => syntacticEquality(h, e)
      case (SequentArtifact(h), SequentArtifact(e)) => syntacticEquality(h, e)
    }
    case Modes.VALUE_EQ =>(have, expected) match {
      case (ExpressionArtifact(h: Term), ExpressionArtifact(e: Term)) => valueEquality(h, e)
      case (ListExpressionArtifact(h: List[Term]), ListExpressionArtifact(e: List[Term])) => valueEquality(h, e)
    }
    case Modes.POLY_EQ => (have, expected) match {
      case (ExpressionArtifact(h: Term), ExpressionArtifact(e: Term)) => polynomialEquality(h, e)
      case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean)
      case (SequentArtifact(h::Nil), SequentArtifact(e::Nil)) => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean)
    }
    case Modes.QE_EQUIV => (have, expected) match {
      case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) => qeEquivalence(h, e)
    }
    case Modes.DI_PREMISE =>
      val diffAssignsMandatory = args.getOrElse("diffAssignsMandatory", "true").toBoolean
      val normalize = args.getOrElse("normalize", "false").toBoolean
      (have, expected) match {
        case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) => dIPremiseCheck(h, e, diffAssignsMandatory, normalize)
        case (SequentArtifact(h :: Nil), SequentArtifact(e :: Nil)) => dIPremiseCheck(h, e, diffAssignsMandatory, normalize)
      }
    case Modes.DI =>
      args.get("question") match {
        case Some(q) =>
          KeYmaeraXParser.programParser(q) match {
            case ode: ODESystem => have match {
              case ExpressionArtifact(h: Formula) => dICheck(ode, h)
              case SequentArtifact(h :: Nil) => dICheck(ode, h.toFormula)
            }
            case _ => throw new IllegalArgumentException("Question must be an ODE system")
          }
        case None => throw new IllegalArgumentException("Mandatory question missing in DI check")
      }
    case Modes.PRG_EQUIV => (have, expected) match {
      case (ExpressionArtifact(h: Program), ExpressionArtifact(e: Program)) => prgEquivalence(e, h)
    }
    case Modes.BELLE_PROOF =>
      args.get("question") match {
        case Some(q) =>
          have match {
            case ExpressionArtifact(h) =>
              val m = expand(q, h :: Nil, KeYmaeraXParser).asInstanceOf[Formula]
              val t = expand(args("tactic"), h :: Nil, BelleParser)
              prove(Sequent(IndexedSeq(), IndexedSeq(m)), t)
            case ListExpressionArtifact(hs) =>
              val m = expand(q, hs, KeYmaeraXParser).asInstanceOf[Formula]
              val t = expand(args("tactic"), hs, BelleParser)
              prove(Sequent(IndexedSeq(), IndexedSeq(m)), t)
          }
        case None =>
          val t = BelleParser(args("tactic"))
          (have, expected) match {
            case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) =>
              prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(h, e))), t)
            case (SequentArtifact(h), SequentArtifact(e)) =>
              val combined = sequentsToFormula(e, h, Equiv)
              val lemmas = h.zip(e).map({ case (hs, es) =>
                prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hs.toFormula, es.toFormula))), t)
              }).map(byUS)
              prove(Sequent(IndexedSeq(), IndexedSeq(combined)), OnAll(andR('R))*(e.size-1) & BranchTactic(lemmas))
          }
    }


  }

  /** Converts list of `expected` subgoals and list of `actual` subgoals into a formula,
    * combining the formulas in the sequents using `fml` (equivalence checking by default). */
  private def sequentsToFormula(expected: List[Sequent], actual: List[Sequent], fml: (Formula, Formula) => Formula = Equiv) = {
    require(expected.nonEmpty && actual.size == expected.size, "Cannot check empty lists of sequents or sequent lists of different size")
    val afs = actual.map(_.toFormula)
    val efs = expected.map(_.toFormula)
    afs.zip(efs).map({ case (af, ef) => fml(af, ef) }).reduceRight(And)
  }

  /** Converts sequent `s` into a formula; removes duplicates and sorts formulas according to their index in
    * sequent `ref` for robust syntactic equality comparison of sequents. */
  private def sequentToFormula(s: Sequent, ref: Sequent): Formula = {
    Imply(
      s.ante.distinct.sortWith((a, b) => ref.ante.indexOf(a) < ref.ante.indexOf(b)).reduceRightOption(And).getOrElse(True),
      s.succ.distinct.sortWith((a, b) => ref.succ.indexOf(a) < ref.succ.indexOf(b)).reduceRightOption(Or).getOrElse(False))
  }

  private val TACTIC_REPETITION_EXTRACTOR = "for #i do(.*)endfor".r("reptac")

  /** Expands occurrences of #i in string `s` with arguments from argument list `args`. */
  @tailrec
  private def expand[T](s: String, args: List[Expression], parser: String=>T): T = {
    val repTacs = TACTIC_REPETITION_EXTRACTOR.findAllMatchIn(s).toList
    if (repTacs.nonEmpty) {
      val unfolded = repTacs.map(_.group("reptac")).map(t => {
        t -> (1 to args.size).map(i => t.replaceAllLiterally("#i", s"#$i")).mkString(";")
      })
      val replaced = unfolded.foldRight(s)({ case ((what, repl), s) => s.replaceAllLiterally(s"for #i do${what}endfor", repl) })
      assert(!replaced.contains("#i"), "Expected to have replaced all variable-length argument repetitions")
      expand(replaced, args, parser)
    } else {
      val ts = (1 to args.size).foldRight(s)({ case (i, s) => s.replaceAllLiterally(s"#$i", args(i-1).prettyString) })
      require(!ts.contains("#"), "Not enough arguments provided for tactic")
      parser(ts)
    }
  }

}
