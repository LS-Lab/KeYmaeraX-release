/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cli

import java.io.{OutputStream, PrintStream}
import java.util.Properties

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleUnfinished, BelleUserCorrectableException, BranchTactic, OnAll, SaturateTactic, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.{Ax, DebuggingTactics, FixedGenerator, PolynomialArithV2, SimplifierV3, TacticFactory}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.AskGrader.Modes
import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.OptionMap
import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor.{AnyChoiceQuestion, AskQuestion, AskTFQuestion, OneChoiceQuestion, Problem}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import spray.json._

import scala.annotation.tailrec
import scala.collection.immutable.{HashSet, IndexedSeq}
import scala.collection.mutable.ListBuffer
import scala.io.Source
import scala.util.{Failure, Success, Try}

/** Assesses dL terms and formulas for equality, equivalence, implication etc. with restricted automation. */
object AssessmentProver {

  /** Assessment prover input artifacts (expressions, sequents etc.) */
  abstract class Artifact {
    def hintString: String
  }
  case class ExpressionArtifact(expr: Expression) extends Artifact {
    override def hintString: String = expr.kind.toString
  }
  case class TexExpressionArtifact(expr: Expression) extends Artifact {
    override def hintString: String = "Simple list/interval notation"
  }
  case class ListExpressionArtifact(exprs: List[Expression]) extends Artifact {
    override def hintString: String = "List of " + exprs.headOption.map(_.kind).getOrElse("<unknown>")
  }
  case class SequentArtifact(goals: List[Sequent]) extends Artifact {
    override def hintString: String = "Sequent"
  }
  case class ChoiceArtifact(selected: List[String]) extends Artifact {
    override def hintString: String = "Choice"
  }
  case class BoolArtifact(value: Option[Boolean]) extends Artifact {
    override def hintString: String = "Boolean"
  }
  case class TextArtifact(value: Option[String]) extends Artifact {
    override def hintString: String = "Text"
  }
  case class MultiArtifact(artifacts: List[Artifact]) extends Artifact {
    override def hintString: String = "<unknown>"
  }

  abstract class Grader {
    val expected: Artifact
    def check(have: Artifact): Either[ProvableSig, String]
  }
  object AskGrader {
    /** Builtin assessment modes */
    object Modes {
      /** Equality of real values. */
      val VALUE_EQ: String = "valueeq"
      /** Syntactic equality. */
      val SYN_EQ: String = "syneq"
      /** Polynomial equality. */
      val POLY_EQ: String = "polyeq"
      /** Equivalent by QE. */
      val QE: String = "qe"
      /** DI premise check. */
      val DI_PREMISE: String = "dipremise"
      /** DI with additional free variables check. */
      val DI: String = "di"
      /** Loop with automated proofs on each branch. */
      val LOOP: String = "loop"
      /** Program equivalence. */
      val PRG_EQUIV = "prgequiv"
      /** Propositional. */
      val PROP = "prop"
      /** Text explanations. */
      val EXPLANATION_CHECK = "explanation"
      /** Provable using a tactic. */
      val BELLE_PROOF: String = "prove"
    }
  }
  case class AskGrader(mode: Option[String], args: Map[String, String], expected: Artifact) extends Grader {
    /** Checks whether artifact `have` fits artifact `expected` using `mode`. */
    override def check(have: Artifact): Either[ProvableSig, String] = {
      (have, expected) match {
        case (ExpressionArtifact(h), ExpressionArtifact(e)) => e match {
          case Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))
              if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") =>
            return run(() => syntacticEquality(h, e))
          case _ => if (h.kind != e.kind) return Right("Expected a " + e.kind + " but got a " + h.kind)
        }
        case (ExpressionArtifact(h), ListExpressionArtifact(exprs)) =>
          if (exprs.exists(_.kind != h.kind)) return Right("Expected a " + exprs.head.kind + " but got a " + h.kind)
        case (ListExpressionArtifact(h), ExpressionArtifact(e)) =>
          if (h.exists(_.kind != e.kind)) return Right("Expected a " + e.kind + " but got a " + h.map(_.kind))
        case (ListExpressionArtifact(h), ListExpressionArtifact(e)) =>
          if (e.map(_.kind).toSet.size != 1 || h.exists(_.kind != e.head.kind)) return Right("Expected a " + e.head.kind + " but got " + h.map(_.kind).mkString(","))
        case (h, e) =>
          if (!e.getClass.isAssignableFrom(h.getClass)) return Right("Expected a " + e.hintString + " but got a " + h.hintString)
      }
      mode.getOrElse(Modes.SYN_EQ) match {
        case Modes.SYN_EQ => (have, expected) match {
          case (ExpressionArtifact(h), ExpressionArtifact(e)) => run(() => syntacticEquality(h, e))
          case (TexExpressionArtifact(h), TexExpressionArtifact(e)) => run(() => syntacticEquality(h, e))
          case (SequentArtifact(h), SequentArtifact(e)) => run(() => syntacticEquality(h, e))
          case _ => Right("Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " + have.hintString)
        }
        case Modes.VALUE_EQ =>(have, expected) match {
          case (ExpressionArtifact(h: Term), ExpressionArtifact(e: Term)) => run(() => valueEquality(h, e))
          case (TexExpressionArtifact(h: Term), TexExpressionArtifact(e: Term)) => run(() => valueEquality(h, e))
          case (ListExpressionArtifact(h: List[Term]), ListExpressionArtifact(e: List[Term])) => Try(Left(valueEquality(h, e))).getOrElse(
            Right(if (h.size < e.size) "Too few values"
                  else if (h.size > e.size) "Too many values"
                  else "Incorrect answer"))
          case _ => Right("Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " + have.hintString)
        }
        case Modes.POLY_EQ => (have, expected) match {
          case (ExpressionArtifact(h: Term), ExpressionArtifact(e: Term)) => run(() => polynomialEquality(h, e))
          case (TexExpressionArtifact(h: Term), TexExpressionArtifact(e: Term)) => run(() => polynomialEquality(h, e))
          case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) => run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
          case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) => run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
          case (SequentArtifact(h::Nil), SequentArtifact(e::Nil)) => run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
          case _ => Right("Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " + have.hintString)
        }
        case Modes.QE => (have, expected) match {
          case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) =>
            args.get("op") match {
              case None | Some("<->") => run(() => qe(h, e, Equiv))
              case Some("->") => run(() => qe(h, e, Imply))
              case Some("<-") => run(() => qe(e, h, Imply))
            }
          case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) =>
            args.get("op") match {
              case None | Some("<->") => run(() => qe(h, e, Equiv))
              case Some("->") => run(() => qe(h, e, Imply))
              case Some("<-") => run(() => qe(e, h, Imply))
            }
          case _ => Right("Answer must be a KeYmaera X formula, but got " + have.hintString)
        }
        case Modes.PROP => (have, expected) match {
          case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) =>
            run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(h, e))), prop))
          case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) =>
            run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(h, e))), prop))
          case _ => Right("Answer must be a KeYmaera X formula, but got " + have.hintString)
        }
        case Modes.DI_PREMISE =>
          val diffAssignsMandatory = args.getOrElse("diffAssignsMandatory", "true").toBoolean
          val normalize = args.getOrElse("normalize", "false").toBoolean
          (have, expected) match {
            case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) => run(() => dIPremiseCheck(h, e, diffAssignsMandatory, normalize))
            case (SequentArtifact(h :: Nil), SequentArtifact(e :: Nil)) => run(() => dIPremiseCheck(h, e, diffAssignsMandatory, normalize))
            case _ => Right("Answer must be a KeYmaera X formula, but got " + have.hintString)
          }
        case Modes.DI =>
          args.get("question") match {
            case Some(q) =>
              KeYmaeraXParser.programParser(q) match {
                case ode: ODESystem => have match {
                  case ExpressionArtifact(h: Formula) => run(() => dICheck(ode, h))
                  case SequentArtifact(h :: Nil) => run(() => dICheck(ode, h.toFormula))
                  case _ => Right("Answer must be a KeYmaera X formula, but got a " + have.hintString)
                }
                case _ => throw new IllegalArgumentException("Question must be an ODE system")
              }
            case None => throw new IllegalArgumentException("Mandatory question missing in DI check")
          }
        case Modes.PRG_EQUIV => (have, expected) match {
          case (ExpressionArtifact(h: Program), ExpressionArtifact(e: Program)) => run(() => prgEquivalence(e, h))
          case _ => Right("Answer must be a KeYmaera X program, but got " + have.hintString)
        }
        case Modes.LOOP =>
          val invArg = args.get("inv").map(KeYmaeraXParser.formulaParser)
          args.get("question") match {
            case Some(q) =>
              have match {
                case ExpressionArtifact(h: Formula) =>
                  var inv: Option[Formula] = None
                  KeYmaeraXParser.setAnnotationListener({ case (_: Loop, f) => inv = Some(f) case _ => })
                  val m = expand(q, h :: Nil, KeYmaeraXParser.formulaParser)
                  run(() => loopCheck(m, invArg.getOrElse(inv.getOrElse(h))))
                case ListExpressionArtifact(h) =>
                  var inv: Option[Formula] = None
                  KeYmaeraXParser.setAnnotationListener({ case (_: Loop, f) => inv = Some(f) case _ => })
                  val m = expand(q, h, KeYmaeraXParser.formulaParser)
                  run(() => loopCheck(m, invArg.getOrElse(inv.getOrElse(h.headOption.map(_.asInstanceOf[Formula]).getOrElse(False)))))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.hintString)
              }
            case _ => throw new IllegalArgumentException("Missing argument 'question' in check 'loop'")
          }
        case Modes.EXPLANATION_CHECK =>
          (have, expected) match {
            case (TextArtifact(Some(hs)), TextArtifact(Some(es))) =>
              run(() => prove(Sequent(IndexedSeq(), IndexedSeq(GreaterEqual(Number(hs.length), Divide(Number(es.length), Number(3))))),
                QE & DebuggingTactics.done("Explanation too short")))
            case (TextArtifact(None), _) => Right("No answer")
            case _ => Right("Answer must be an explanation, but got " + have.hintString)
          }
        case Modes.BELLE_PROOF =>
          args.get("question") match {
            case Some(q) =>
              have match {
                case ExpressionArtifact(h) =>
                  val m = expand(q, h :: Nil, KeYmaeraXParser).asInstanceOf[Formula]
                  val t = expand(args("tactic"), h :: Nil, BelleParser)
                  run(() => prove(Sequent(IndexedSeq(), IndexedSeq(m)), t))
                case ListExpressionArtifact(hs) =>
                  val m = expand(q, hs, KeYmaeraXParser).asInstanceOf[Formula]
                  val t = expand(args("tactic"), hs, BelleParser)
                  run(() => prove(Sequent(IndexedSeq(), IndexedSeq(m)), t))
                case _ => Right("Answer must a a KeYmaera X expression or list of expressions, but got " + have.hintString)
              }
            case None =>
              val t = BelleParser(args("tactic"))
              (have, expected) match {
                case (ExpressionArtifact(h: Formula), ExpressionArtifact(e: Formula)) =>
                  run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(h, e))), t))
                case (SequentArtifact(h), SequentArtifact(e)) =>
                  val combined = sequentsToFormula(e, h, Equiv)
                  val lemmaResults = h.zip(e).map({ case (hs, es) =>
                    run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hs.toFormula, es.toFormula))), t))
                  })
                  if (lemmaResults.forall(_.isLeft)) {
                    val lemmas = lemmaResults.map(_.left.get).map(byUS)
                    run(() => prove(Sequent(IndexedSeq(), IndexedSeq(combined)), OnAll(andR('R))*(e.size-1) & BranchTactic(lemmas)))
                  } else {
                    lemmaResults.find(_.isRight).get
                  }
                case _ => Right("Answer must a KeYmaera X formula or sequent, but got " + have.hintString)
              }
          }
      }
    }
  }
  /** A grader that has access to multiple answers. */
  case class MultiAskGrader(main: Grader, earlier: Map[Int, Grader]) extends Grader {
    private val grader = main match {
      case AskGrader(mode, args, expected) =>
        val mergedExpected = expected //@todo ignored for now

        val ARG_PLACEHOLDER = "argPlaceholder"
        val ARG_INDEX = """#(-?\d+)""".r(ARG_PLACEHOLDER)
        val argIdxs = args.values.flatMap(v => { ARG_INDEX.findAllMatchIn(v).map(_.group(ARG_PLACEHOLDER).toInt).toList }).toList.sorted
        val newArgIdxs = argIdxs.map(i => (i, if (i<0) i+earlier.keys.size+1 else i+earlier.keys.size))
        val mergedArgs = args.map({ case (k, v) =>
          val rewrittenBackRefs = newArgIdxs.foldRight(v)({ case ((i, j), mv) => mv.replaceAllLiterally("#" + i, "#" + j) })
          (k, rewrittenBackRefs)
        })

        AskGrader(mode, mergedArgs, mergedExpected)
    }

    override val expected: Artifact = grader.expected
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      //@note assumed sorted from earliest to main artifact
      case MultiArtifact(as) =>
        val mergedHave = as.reduceRight[Artifact]({
          case (ExpressionArtifact(a), ExpressionArtifact(b)) => ListExpressionArtifact(a :: b :: Nil)
          case (ExpressionArtifact(a), ListExpressionArtifact(all)) => ListExpressionArtifact(all :+ a)
        })
        //@todo may also want to recheck old answers to know how to grade the current answer
        grader.check(mergedHave)
    }
  }

  case class OneChoiceGrader(args: Map[String, String], expected: ChoiceArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case h: ChoiceArtifact =>
        //@note correct if answering with any of the correctly marked solutions
        if (h.selected.nonEmpty && h.selected.toSet.subsetOf(expected.selected.toSet)) run(() => KeYmaeraXProofChecker(1000)(closeT)(Sequent(IndexedSeq.empty, IndexedSeq(True))))
        else Right("Incorrect answer")
    }
  }
  case class AnyChoiceGrader(args: Map[String, String], expected: ChoiceArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case h: ChoiceArtifact =>
        //@note correct if answering with exactly the correct yes/no pattern (modulo order)
        if (h.selected.toSet == expected.selected.toSet) run(() => KeYmaeraXProofChecker(1000)(closeT)(Sequent(IndexedSeq.empty, IndexedSeq(True))))
        else Right("Incorrect answer")
    }
  }

  case class AskTFGrader(expected: BoolArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case BoolArtifact(Some(h)) =>
        val ef = if (expected.value.get) True else False
        val hf = if (h) True else False
        run(() => KeYmaeraXProofChecker(1000)(useAt(Ax.equivReflexive)(1))(Sequent(IndexedSeq.empty, IndexedSeq(Equiv(hf, ef)))))
      case BoolArtifact(_) =>
        Right("No answer")
    }
  }

  /** Runs a proof returning either the proved provable as a witness of a hint message. */
  private def run(p: => () => ProvableSig): Either[ProvableSig, String] = {
    Try(p()) match {
      case Success(p) => Left(p)
      case Failure(BelleUnfinished(msg, _)) => Right(msg)
      case Failure(ex: BelleUserCorrectableException) => Right(ex.getMessage)
      case Failure(_) => Right("Incorrect answer")
    }
  }

  /** Proves equivalence of `a` and `b` by QE. */
  def qe(a: Formula, b: Formula, op: (Formula, Formula) => Formula): ProvableSig = {
    KeYmaeraXProofChecker(5000)(QE)(Sequent(IndexedSeq.empty, IndexedSeq(op(a, b))))
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

  /** Checks `inv` for being a loop invariant for `question` of the shape `P->[{a;}*]Q` or `[{a;}*]P`. */
  def loopCheck(question: Formula, inv: Formula): ProvableSig = {
    def loopCheckTactic(inv: Formula): BelleExpr = {
      loop(inv)(1) <(
        master(loop(FixedGenerator(List.empty)), ODE, keepQEFalse=true) & DebuggingTactics.done("Precondition does not imply invariant"),
        master(loop(FixedGenerator(List.empty)), ODE, keepQEFalse=true) & DebuggingTactics.done("Invariant does not imply postcondition"),
        master(loop(FixedGenerator(List.empty)), ODE, keepQEFalse=true) & DebuggingTactics.done("Invariant is not preserved by loop body")
      ) & done
    }

    question match {
      case Imply(a, b@Box(_: Loop, _)) =>
        prove(Sequent(IndexedSeq(a), IndexedSeq(b)), loopCheckTactic(inv))
      case b@Box(_: Loop, _) =>
        prove(Sequent(IndexedSeq(), IndexedSeq(b)), loopCheckTactic(inv))
      case _ => throw new IllegalArgumentException("Loop only applicable to P->[{a;}*]Q or [{a;}*]P questions")
    }
  }

  /** Checks program equivalence by `[a;]P <-> [b;]P.` */
  def prgEquivalence(a: Program, b: Program): ProvableSig = {
    val p = PredOf(Function("P", None, Unit, Bool), Nothing)
    def searchCMon(at: PosInExpr) = TacticFactory.anon { (seq: Sequent) =>
      val anteCtxs = seq.ante.map(_.at(at)._1).zipWithIndex
      val succCtxs = seq.succ.map(_.at(at)._1).zipWithIndex
      val anteMatch = anteCtxs.find({ case (ctx, _) => succCtxs.exists(_._1 == ctx) })
      val succMatch = succCtxs.find({ case (ctx, _) => anteMatch.exists(_._1 == ctx) })
      (anteMatch, succMatch) match {
        case (Some((_, ai)), Some((_, si))) =>
          cohideOnlyL(AntePos(ai)) & cohideOnlyR(SuccPos(si)) & implyRi & CMon(PosInExpr(1::Nil))
        case _ => throw new TacticInapplicableFailure("No matching contexts found")
      }
    }
    def unloop() = TacticFactory.anon { (seq: Sequent) =>
      val anteLoops = seq.ante.zipWithIndex.find({ case (Box(Loop(ap), _), _) => FormulaTools.dualFree(ap) case _ => false })
      val succLoops = seq.succ.zipWithIndex.find({ case (Box(Loop(bp), _), _) => FormulaTools.dualFree(bp) case _ => false })
      (anteLoops, succLoops) match {
        case (Some((af@Box(_, ap), ai)), Some((Box(bbody, bp), si))) =>
          if (ap != bp) throw new TacticInapplicableFailure("No matching loop postconditions found")
          cohideOnlyL(AntePos(ai)) & cohideOnlyR(SuccPos(si)) & cut(Box(bbody, af)) <(
            useAt(Ax.I)(-2, 1::Nil) & boxAnd(-2) & prop & done
            ,
            hideR(1) & implyRi & useAt(Ax.IIinduction, PosInExpr(1::Nil))(1) &
            useAt(Ax.iterateb)(1, 1::0::Nil) & G(1) & implyR(1) & andL(-1) & hideL(-1) &
            chase(-1) & chase(1)
          )
      }
    }
    val (as, bs) = (elaborateToSystem(a), elaborateToSystem(b))
    KeYmaeraXProofChecker(5000)(chase(1, 0::Nil) & chase(1, 1::Nil) &
      SaturateTactic(OnAll(prop & OnAll(searchCMon(PosInExpr(1::Nil)) | unloop))) & DebuggingTactics.done("Program is not as expected"))(Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(as, p), Box(bs, p)))))
  }

  /** Generic assessment prover uses tactic `t` to prove sequent `s`, aborting after `timeout` time. */
  def prove(s: Sequent, t: BelleExpr): ProvableSig = {
    KeYmaeraXProofChecker(5000)(t)(s)
  }

  /** Grades a submission.
    *
    * @param options The prover options:
    *                - 'in (mandatory) identifies the file to grade
    *                - 'config (mandatory) identifies the grader configuration file (maps chapter labels to source files)
    *                - 'msgOut (mandatory) message output stream
    *                - 'resultOut (mandatory) result output stream
    */
  def grade(options: OptionMap, msgOut: OutputStream, resultOut: OutputStream, usage: String): Unit = {
    require(options.contains('in), usage)
    require(options.contains('config), usage)

    val configSource = Source.fromFile(options('config).toString, "UTF-8")
    val config = new Properties()
    try { config.load(configSource.reader()) } finally { configSource.close() }

    val inputFileName = options('in).toString
    val src = Source.fromFile(inputFileName, "UTF-8")
    val input = try { src.mkString.parseJson } finally { src.close() }
    val chapter = {
      import Submission.SubmissionJsonFormat._
      input.convertTo[Submission.Chapter]
    }

    def toArtifact[T <: Artifact](p: Submission.Prompt, expected: Class[T]): Artifact = p.answers match {
      case Submission.TextAnswer(_, t) :: Nil =>
        if (classOf[TexExpressionArtifact].isAssignableFrom(expected)) QuizExtractor.AskQuestion.artifactsFromTexMathString(t)
        else if (classOf[TextArtifact].isAssignableFrom(expected)) QuizExtractor.AskQuestion.artifactsFromTexTextString(t)
        else QuizExtractor.AskQuestion.artifactsFromKyxString(t)
      case answers =>
        if (classOf[BoolArtifact].isAssignableFrom(expected)) {
          val choiceAnswers = answers.map(_.asInstanceOf[Submission.ChoiceAnswer])
          BoolArtifact(choiceAnswers.find(_.isSelected).map(_.text == "True"))
        } else {
          // list if choice answers
          val choiceAnswers = answers.map(_.asInstanceOf[Submission.ChoiceAnswer])
          ChoiceArtifact(choiceAnswers.filter(_.isSelected).map(_.text))
        }
    }

    Option(config.getProperty(chapter.label)) match {
      case Some(file) =>
        val gradeSource = Source.fromFile(file, "UTF-8")
        val problems = try {
          Problem.fromString(gradeSource.mkString.linesWithSeparators.filterNot(_.startsWith("%")).mkString)
        } finally {
          gradeSource.close()
        }
        val parsedProblems: List[(Problem, (List[(Grader, Submission.Prompt, Artifact)], List[(Submission.Prompt, Throwable)]))] =
            problems.zip(chapter.problems).map({ case (qp, ap) =>
          val parsed = qp.questions.zip(ap.prompts).map({ case (q, prompt) =>
            val grader = q match {
              case q: AskQuestion =>
                //@todo access to previous question if grader mode is explanation
                AskGrader(q.grader, q.args, q.expected)
              case q: OneChoiceQuestion =>
                val correct = ChoiceArtifact(q.choices.filter(_.isCorrect).map(_.text))
                assert(correct.selected.size == 1, "Missing or non-unique correct solution")
                OneChoiceGrader(Map.empty[String, String], correct)
              case q: AnyChoiceQuestion =>
                val correct = ChoiceArtifact(q.choices.filter(_.isCorrect).map(_.text))
                assert(correct.selected.nonEmpty, "Missing correct solution")
                AnyChoiceGrader(Map.empty[String, String], correct)
              case q: AskTFQuestion => AskTFGrader(BoolArtifact(Some(q.isTrue)))
            }
            try {
              Left((grader, prompt, toArtifact(prompt, grader.expected.getClass)))
            } catch {
              case ex: Throwable => Right((prompt, ex))
            }
          })
          (qp, parsed.partition(_.isLeft) match {
            case (artifacts, parseErrors) => (artifacts.map(_.left.get), parseErrors.map(_.right.get))
          })
        })

        val msgStream = new PrintStream(msgOut, true)
        if (parsedProblems.exists(_._2._2.nonEmpty)) {
          // report parse errors
          parsedProblems.foreach({ case (p, (_, errors)) =>
            msgStream.print("Parsing '" + p.name.getOrElse("") + "':")
            if (errors.nonEmpty) {
              msgStream.println("FAILED")
              msgStream.println(errors.map({ case (prompt, ex) =>
                prompt.answers.map(_.text).mkString(",") + "\n" + ex.getMessage }).mkString("\n"))
            } else msgStream.println("PASSED")
          })
        } else {
          // grade
          val allGrades: List[(Submission.Prompt, Double)] = parsedProblems.flatMap({ case (p, (graders, _)) =>
            msgStream.println("Grading section " + p.name.getOrElse(""))
            val grades = graders.map({ case (grader, prompt, artifact) =>
              msgStream.print("Grading question " + prompt.id + "...")
              grader.check(artifact) match {
                case Left(_) =>
                  msgStream.println("PASSED")
                  (prompt, prompt.points)
                case Right(hint) =>
                  msgStream.print("FAILED:")
                  msgStream.println(hint)
                  (prompt, 0.0)
              }
            })
            msgStream.println("Done grading section " + p.name.getOrElse(""))
            grades
          })
          printJSONGrades(allGrades, resultOut)
        }

      case None => throw new IllegalArgumentException("Missing grading information for " + chapter.label)
    }
  }

  private def printJSONGrades(grades: List[(Submission.Prompt, Double)], out: OutputStream): Unit = {
    import spray.json.DefaultJsonProtocol._
    import Submission.GradeJsonFormat._
    out.write(grades.toJson.compactPrint.getBytes("UTF-8"))
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

  /** Elaborates program constants to system constants in dual-free contexts. */
  private def elaborateToSystem(prg: Program): Program = {
    if (FormulaTools.literalDualFree(prg)) {
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
          case ProgramConst(name, space) => Right(SystemConst(name, space))
          case _ => Left(None)
        }
      }, prg).get
    } else prg
  }

}
