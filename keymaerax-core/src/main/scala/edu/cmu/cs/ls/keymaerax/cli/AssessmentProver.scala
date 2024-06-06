/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{
  BelleExpr,
  BelleUnfinished,
  BelleUserCorrectableException,
  BranchTactic,
  NamedBelleExpr,
  OnAll,
  SaturateTactic,
  SeqTactic,
  TacticInapplicableFailure,
}
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, GenProduct}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{
  Ax,
  ConfigurableGenerator,
  DebuggingTactics,
  FixedGenerator,
  PolynomialArithV2,
  SimplifierV3,
  TacticFactory,
  TactixInit,
  ToolProvider,
}
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.AskGrader.Modes
import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor.AskQuestion.extractSolfinAnswers
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.parser.{
  ArchiveParser,
  Declaration,
  KeYmaeraXArchivePrinter,
  ParseException,
  ParsedArchiveEntry,
  Parser,
  PrettierPrintFormatProvider,
}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import spray.json._

import java.io.{BufferedWriter, File, FileReader, FileWriter, IOException, OutputStream, PrintStream, PrintWriter}
import java.util.Properties
import java.util.concurrent.TimeoutException
import scala.annotation.tailrec
import scala.collection.immutable.{HashSet, IndexedSeq, Nil}
import scala.collection.mutable.ListBuffer
import scala.io.Source
import scala.util.matching.Regex
import scala.util.{Failure, Success, Try}

/** Assesses dL terms and formulas for equality, equivalence, implication etc. with restricted automation. */
object AssessmentProver {

  object Messages {
    val BLANK = "BLANK"
    val FAILED = "FAILED"
    val PASS = "PASS"
    val OK = "OK"
    val SKIPPED = "SKIPPED"
    val PARSE_ERROR = "PARSE ERROR"
    val INSPECT = "INSPECT"
  }

  object Options {
    val FAIL_HINT = "failHint"
  }

  /** Assessment prover input artifacts (expressions, sequents etc.) */
  abstract class Artifact {
    def hintString: String
    def longHintString: String = hintString
    def prettyString: String

    /**
     * Checks the artifact for being of a certain shape (skip if None), returns None if shape constraint is met, an
     * error message otherwise.
     */
    def checkShape(shape: Option[String]): Option[String] = None
  }
  case class ExpressionArtifact(exprString: String, kind: Option[Kind] = None) extends Artifact {
    val expr: Expression = kind match {
      case Some(FormulaKind) => exprString.asFormula
      case Some(ProgramKind) => exprString.asProgram
      case Some(DifferentialProgramKind) => exprString.asDifferentialProgram
      case Some(TermKind) => exprString.asTerm
      case _ => exprString.asExpr
    }
    def as(kind: Kind): Expression = kind match {
      case FormulaKind => exprString.asFormula
      case ProgramKind => exprString.asProgram
      case DifferentialProgramKind => exprString.asDifferentialProgram
      case TermKind => exprString.asTerm
      case _ => exprString.asExpr
    }
    override def hintString: String = expr.kind.toString
    override def longHintString: String = expr.kind.toString + " " + exprString
    override def prettyString: String = expr.prettyString
    override def checkShape(shape: Option[String]): Option[String] = {
      shape match {
        case Some("&=") => expr match {
            case h: Formula if FormulaTools.conjuncts(h).forall(_.isInstanceOf[Equal]) => None
            case _ => Some("Not a conjunction of equalities")
          }
        case Some("atom") => expr match {
            case _: AtomicFormula => None
            case _ => Some("Not an atomic formula")
          }
        case Some("=") => expr match {
            case _: Equal => None
            case _ => Some("Not an equality")
          }
        case Some("<=") => expr match {
            case _: Equal => Some("Not an inequality")
            case _: ComparisonFormula => None
            case _ => Some("Not an inequality")
          }
        // quantifier-free real arithmetic
        case Some("qfra") => expr match {
            case f: Formula if StaticSemantics.boundVars(f).isEmpty => None
            case _ => Some("Not a quantifier-free formula of real arithmetic")
          }
        // quantifier-free real arithmetic with only natural exponents
        case Some("qfrane") => expr match {
            case f: Formula if StaticSemantics.boundVars(f).isEmpty =>
              val exponents = ListBuffer[Term]()
              ExpressionTraversal.traverse(
                new ExpressionTraversalFunction() {
                  override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
                    case Power(_, e) =>
                      exponents += e
                      Left(None)
                    case _ => Left(None)
                  }
                },
                f,
              )
              if (
                exponents.forall({
                  case Number(n) => n >= 1
                  case _ => false
                })
              ) None
              else Some("Not a quantifier-free formula of real arithmetic with only natural exponents")
            case _ => Some("Not a quantifier-free formula of real arithmetic with only natural exponents")
          }
        // quantifier-free division-free real arithmetic with only natural exponents
        case Some("qfradfne") => expr match {
            case f: Formula if StaticSemantics.boundVars(f).isEmpty =>
              val exponents = ListBuffer[Term]()
              val divisions = ListBuffer[Term]()
              ExpressionTraversal.traverse(
                new ExpressionTraversalFunction() {
                  override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
                    case d: Divide =>
                      divisions += d
                      Left(None)
                    case Power(_, e) =>
                      exponents += e
                      Left(None)
                    case _ => Left(None)
                  }
                },
                f,
              )
              if (
                divisions.isEmpty && exponents.forall({
                  case Number(n) => n >= 1
                  case _ => false
                })
              ) None
              else Some("Not a quantifier-free division-free formula of real arithmetic with only natural exponents")
            case _ => Some("Not a quantifier-free formula of real arithmetic with only natural exponents")
          }
        case Some(_) => throw new IllegalArgumentException("Unknown shape " + shape)
        case None => None
      }
    }

  }
  case class TexExpressionArtifact(expr: Expression) extends Artifact {
    override def hintString: String = "Simple list/interval notation"
    override def prettyString: String = expr.prettyString
  }
  case class ListExpressionArtifact(exprs: List[Expression]) extends Artifact {
    override def hintString: String = {
      if (exprs.map(_.kind).toSet.size > 1) exprs.map(_.kind).mkString(",")
      else "List of " + exprs.headOption.map(_.kind).getOrElse("<unknown>")
    }
    override def longHintString: String = exprs.map(_.kind).mkString(",") + ":\n  " +
      exprs.map(e => e.prettyString + ": " + e.kind).mkString("\n  ")
    override def prettyString: String = if (exprs.isEmpty) Messages.BLANK else longHintString
  }
  case class SequentArtifact(goals: List[Sequent]) extends Artifact {
    override def hintString: String = if (goals.size <= 1) "Sequent" else "List of sequents"

    override def prettyString: String = hintString + ":\n" + goals.map(_.prettyString).mkString("\n")
  }
  case class TacticArtifact(s: String, t: BelleExpr) extends Artifact {
    override def hintString: String = "Tactic"
    override def prettyString: String = t.prettyString
  }
  case class ArchiveArtifact(s: String) extends Artifact {
    lazy val entries: List[ParsedArchiveEntry] = ArchiveParser.parse(s, parseTactics = true)
    override def hintString: String = "Archive"
    override def prettyString: String = entries
      .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80)))
      .mkString("\n")
  }
  case class SubstitutionArtifact(s: List[SubstitutionPair]) extends Artifact {
    override def hintString: String = "Uniform substitution"
    override def prettyString: String = s.map(_.toString).mkString(", ")
  }
  case class ChoiceArtifact(selected: List[String]) extends Artifact {
    override def hintString: String = "Choice"
    override def prettyString: String = selected.mkString(",")
  }
  case class BoolArtifact(value: Option[Boolean]) extends Artifact {
    override def hintString: String = "Boolean"
    override def prettyString: String = value.map(_.toString).getOrElse(Messages.BLANK)
  }
  case class TextArtifact(value: Option[String]) extends Artifact {
    override def hintString: String = "Text"
    override def prettyString: String = if (value.map(_.trim).getOrElse("").isEmpty) Messages.BLANK else value.get
  }

  /** Artifacts from multiple questions. */
  case class MultiArtifact(artifacts: List[Artifact]) extends Artifact {
    override def hintString: String = "<unknown>"
    override def prettyString: String = artifacts.map(_.prettyString).mkString("\n")
  }

  /** Any of the artifacts is correct. */
  case class AnyOfArtifact(artifacts: List[Artifact]) extends Artifact {
    override def hintString: String = artifacts
      .map(_.hintString)
      .distinct
      .reduceOption(_ + "/" + _)
      .getOrElse("<unknown>")
    override def prettyString: String = artifacts
      .map(_.prettyString)
      .distinct
      .reduceOption(_ + "/" + _)
      .getOrElse("<unknown>")
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

      /** Reduce differential invariant to equivalent other differential invariant. */
      val DI_REDUCTION: String = "direduction"

      /** Loop with automated proofs on each branch. */
      val LOOP: String = "loop"

      /** Program equivalence. */
      val PRG_EQUIV = "prgequiv"

      /** Contract equivalence. */
      val CONTRACT_EQUIV = "contractequiv"

      /** Minimum number of parentheses. */
      val MIN_PARENS = "minparens"

      /** Propositional. */
      val PROP = "prop"

      /** Text explanations. */
      val EXPLANATION_CHECK = "explanation"

      /** Provable using a tactic. */
      val BELLE_PROOF: String = "prove"

      /** Check a kyx archive */
      val CHECK_ARCHIVE: String = "checkArchive"

      /** Check if model assumptions and postcondition are ok. */
      val TEST_MODEL: String = "testModel"

      /** Checks a ModelPlex monitor */
      val CHECK_MODELPLEX_MONITOR: String = "checkmx"

      /** Skip grading */
      val SKIP: String = "skip"
    }
  }
  case class SkipGrader(expected: Artifact, reason: String) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = Right(reason)
  }
  case class AskGrader(mode: Option[String], args: Map[String, String], expected: Artifact) extends Grader {

    /** Checks whether artifact `have` fits artifact `expected` using `mode`. */
    override def check(have: Artifact): Either[ProvableSig, String] = {
      if (mode.contains(Modes.SKIP)) Right(Messages.SKIPPED)
      else checkArtifactKind(have, expected) match {
        case Right(e) => Right(e)
        case Left(have) => expected match {
            case e: ExpressionArtifact => e.expr match {
                // central treatment of N/A
                case Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))
                    if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") =>
                  have match {
                    case h: ExpressionArtifact => h.expr match {
                        case Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))
                            if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") =>
                          run(() => syntacticEquality(h.copy(exprString = h.exprString.toLowerCase).expr, e.expr))
                        case _ => Right(errorMsg(expected, have))
                      }
                  }
                case _ => checkShapeThenRun(have, expected)
              }
            case _ => checkShapeThenRun(have, expected)
          }
      }
    }

    /** Checks the shape of artifact `have`; if successful, runs the grader afterwards. */
    private def checkShapeThenRun(have: Artifact, expected: Artifact): Either[ProvableSig, String] =
      have.checkShape(args.get("shape")) match {
        case Some(e) => Right(e)
        case None => expected match {
            case AnyOfArtifact(exp) =>
              for (e <- exp) {
                check(have, e) match {
                  case Left(p) => return Left(p)
                  case _ => // continue
                }
              }
              Right("")
            case _ => check(have, expected)
          }
      }

    private def run(p: => () => ProvableSig): Either[ProvableSig, String] = AssessmentProver
      .run(p, args.get(Options.FAIL_HINT))

    private def errorMsg(expected: Artifact, haveMsg: String) = expected match {
      case e: ExpressionArtifact => e.expr match {
          case Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))
              if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") =>
            if (haveMsg == Messages.BLANK) haveMsg else "Incorrect " + haveMsg
          case _ =>
            if (haveMsg == Messages.BLANK) haveMsg else "Expected a " + expected.hintString + " but got " + haveMsg
        }
      case _ => if (haveMsg == Messages.BLANK) haveMsg else "Expected a " + expected.hintString + " but got " + haveMsg
    }

    private def errorMsg(expected: Artifact, have: Artifact): String = have match {
      case h: ExpressionArtifact => h.expr match {
          case Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))
              if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") => "Incorrect " + h.expr.prettyString
          case _ => errorMsg(expected, h.expr.prettyString)
        }
      case _ => errorMsg(expected, have.prettyString)
    }

    private def check(have: Artifact, expected: Artifact): Either[ProvableSig, String] = {
      mode.getOrElse(Modes.SYN_EQ) match {
        case Modes.SYN_EQ => (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => run(() => syntacticEquality(h.expr, e.expr))
            case (h: ListExpressionArtifact, e: ExpressionArtifact) => check(h, ListExpressionArtifact(List(e.expr)))
            case (h: ExpressionArtifact, e: ListExpressionArtifact) => check(ListExpressionArtifact(List(h.expr)), e)
            case (ListExpressionArtifact(h), ListExpressionArtifact(e)) => run(() => {
                val checkResults = h
                  .sortBy(_.prettyString)
                  .zip(e.sortBy(_.prettyString))
                  .map({ case (he, ee) => syntacticEquality(he, ee) })
                checkResults.find(!_.isProved).getOrElse(checkResults.head)
              })
            case (TexExpressionArtifact(h), TexExpressionArtifact(e)) => run(() => syntacticEquality(h, e))
            case (SequentArtifact(h), SequentArtifact(e)) => run(() => syntacticEquality(h, e))
            case (TextArtifact(h), TextArtifact(e)) =>
              if (h == e) run(() => prove(Sequent(IndexedSeq(), IndexedSeq(True)), closeT)) else Right("")
            case _ => Right(
                "Answer must be a KeYmaera X expression, sequent, list of expressions, or simple list/interval notation, but got " +
                  have.longHintString
              )
          }
        case Modes.VALUE_EQ => (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (ht: Term, et: Term) => run(() => valueEquality(ht, et))
                case _ => Right(
                    "Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " +
                      have.longHintString
                  )
              }
            case (TexExpressionArtifact(h: Term), TexExpressionArtifact(e: Term)) => run(() => valueEquality(h, e))
            case (ListExpressionArtifact(h: List[Term]), ListExpressionArtifact(e: List[Term])) =>
              Try(Left(valueEquality(h, e))).getOrElse(Right(
                if (h.size < e.size) "Too few values" else if (h.size > e.size) "Too many values" else ""
              ))
            case _ => Right(
                "Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " +
                  have.longHintString
              )
          }
        case Modes.POLY_EQ => (have, expected) match {
            case (h @ ListExpressionArtifact(have), e: ExpressionArtifact) =>
              if (have.distinct.size == 1) check(ExpressionArtifact(have.head.prettyString), e)
              else Right(errorMsg(e, h))
            case (h: ExpressionArtifact, e @ ListExpressionArtifact(expected)) =>
              if (expected.distinct.size == 1) check(h, ExpressionArtifact(expected.head.prettyString))
              else Right(errorMsg(e, h))
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (ht: Term, et: Term) => run(() => polynomialEquality(ht, et))
                case (hf: Formula, ef: Formula) => run(() => polynomialEquality(hf, ef, normalize = false))
                case _ => Right(
                    "Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " +
                      have.longHintString
                  )
              }
            case (ListExpressionArtifact(h), ListExpressionArtifact(e)) => run(() => {
                val checkResults = h
                  .sortBy(_.prettyString)
                  .zip(e.sortBy(_.prettyString))
                  .map({
                    case (ht: Term, et: Term) => polynomialEquality(ht, et)
                    case (hf: Formula, ef: Formula) =>
                      polynomialEquality(hf, ef, args.getOrElse("normalize", "false").toBoolean)
                  })
                checkResults.find(!_.isProved).getOrElse(checkResults.head)
              })
            case (TexExpressionArtifact(h: Term), TexExpressionArtifact(e: Term)) => run(() => polynomialEquality(h, e))
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (hf: Formula, ef: Formula) =>
                  run(() => polynomialEquality(hf, ef, args.getOrElse("normalize", "false").toBoolean))
                case _ => Right(
                    "Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " +
                      have.longHintString
                  )
              }
            case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) =>
              run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
            case (SequentArtifact(h :: Nil), SequentArtifact(e :: Nil)) =>
              run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
            case _ => Right(
                "Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " +
                  have.longHintString
              )
          }
        case Modes.QE => args.get("question") match {
            case Some(q) =>
              def runQE(question: String, answers: List[String]) = {
                run(() => {
                  val m = expand(question, answers, Parser.parser).asInstanceOf[Formula]
                  KeYmaeraXProofChecker(5, Declaration(Map.empty))(QE)(Sequent(IndexedSeq.empty, IndexedSeq(m)))
                })
              }

              have match {
                case h: ExpressionArtifact => runQE(q, h.exprString :: Nil)
                case ListExpressionArtifact(hs) => runQE(q, hs.map(_.prettyString))
                case SequentArtifact(goals) => runQE(q, goals.map(_.toFormula).map(_.prettyString))
                case _ =>
                  Right("Answer must a a KeYmaera X expression or list of expressions, but got " + have.longHintString)
              }
            case None => (have, expected) match {
                case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                    case (hf: Formula, ef: Formula) => args.get("op") match {
                        case None | Some("<->") => run(() => qe(hf, ef, Equiv))
                        case Some("->") => run(() => qe(hf, ef, Imply))
                        case Some("<-") => run(() => qe(ef, hf, Imply))
                      }
                    case _ => Right("Answer must be a KeYmaera X expression, but got " + have.longHintString)
                  }
                case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) => args.get("op") match {
                    case None | Some("<->") => run(() => qe(h, e, Equiv))
                    case Some("->") => run(() => qe(h, e, Imply))
                    case Some("<-") => run(() => qe(e, h, Imply))
                  }
                case (ListExpressionArtifact(h), ListExpressionArtifact(e)) =>
                  val checked = h
                    .zip(e)
                    .map({ case (h, e) =>
                      check(ExpressionArtifact(h.prettyString), ExpressionArtifact(e.prettyString))
                    })
                  checked.find(_.isRight) match {
                    case None => checked.head
                    case Some(r) => r
                  }
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }
          }
        case Modes.PROP => (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (hf: Formula, ef: Formula) =>
                  run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hf, ef))), prop & done))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }
            case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) =>
              run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(h, e))), prop & done))
            case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
          }
        case Modes.DI_PREMISE =>
          val diffAssignsMandatory = args.getOrElse("diffAssignsMandatory", "true").toBoolean
          val normalize = args.getOrElse("normalize", "false").toBoolean
          (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (hf: Formula, ef: Formula) => run(() => dIPremiseCheck(hf, ef, diffAssignsMandatory, normalize))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }

            case (SequentArtifact(h :: Nil), SequentArtifact(e :: Nil)) =>
              run(() => dIPremiseCheck(h, e, diffAssignsMandatory, normalize))
            case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
          }
        case Modes.DI => args.get("question") match {
            case Some(q) => Parser.parser.programParser(q) match {
                case ode: ODESystem => have match {
                    case h: ExpressionArtifact => h.expr match {
                        case hf: Formula => run(() => dICheck(ode, hf))
                        case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
                      }
                    case SequentArtifact(h :: Nil) => run(() => dICheck(ode, h.toFormula))
                    case _ => Right("Answer must be a KeYmaera X formula, but got a " + have.longHintString)
                  }
                case _ => throw new IllegalArgumentException("Question must be an ODE system")
              }
            case None => throw new IllegalArgumentException("Mandatory question missing in DI check")
          }
        case Modes.DI_REDUCTION => (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (hf: Formula, ef: Formula) => run(() => dIReductionCheck(hf, ef))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }
          }
        case Modes.PRG_EQUIV => (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (hp: Program, ep: Program) => run(() => prgEquivalence(ep, hp))
                case _ => Right("Answer must be a KeYmaera X program, but got " + have.longHintString)
              }
            case _ => Right("Answer must be a KeYmaera X program, but got " + have.longHintString)
          }
        case Modes.CONTRACT_EQUIV => (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                case (hf: Formula, ef: Formula) => run(() => contractEquivalence(hf, ef))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }
            case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
          }
        case Modes.MIN_PARENS => (have, expected) match {
            case (h @ ExpressionArtifact(hs, _), e @ ExpressionArtifact(es, _)) =>
              run(() => syntacticEquality(h.expr, e.expr)) match {
                case Left(p) =>
                  if (hs.count(_ == '(') + hs.count(_ == '{') <= es.count(_ == '(') + es.count(_ == '{') + 1) Left(p)
                  else Right("Not minimal number of parentheses and braces")
                case r => r
              }
          }
        case Modes.LOOP =>
          val invArg = args.get("inv").map(Parser.parser.formulaParser)
          args.get("question") match {
            case Some(q) => have match {
                case h: ExpressionArtifact => h.expr match {
                    case hf: Formula =>
                      var inv: Option[Formula] = None
                      Parser
                        .parser
                        .setAnnotationListener({
                          case (_: Loop, f) => inv = Some(f)
                          case _ =>
                        })
                      val m = expand(q, hf.prettyString :: Nil, Parser.parser.formulaParser)
                      run(() => loopCheck(m, invArg.getOrElse(inv.getOrElse(hf))))
                    case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
                  }
                case ListExpressionArtifact(h) =>
                  var inv: Option[Formula] = None
                  Parser
                    .parser
                    .setAnnotationListener({
                      case (_: Loop, f) => inv = Some(f)
                      case _ =>
                    })
                  val m = expand(q, h.map(_.prettyString), Parser.parser.formulaParser)
                  run(() =>
                    loopCheck(
                      m,
                      invArg.getOrElse(inv.getOrElse(h.headOption.map(_.asInstanceOf[Formula]).getOrElse(False))),
                    )
                  )
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }
            case _ => throw new IllegalArgumentException("Missing argument 'question' in check 'loop'")
          }
        case Modes.EXPLANATION_CHECK => (have, expected) match {
            case (TextArtifact(Some(hs)), TextArtifact(Some(es))) =>
              def extract(s: String) = """(\s|~)*(?<text>.*)(\s*|~)*"""
                .r
                .findFirstMatchIn(s.linesIterator.reduceOption(_ + _).getOrElse(""))
                .map(_.group("text"))
                .getOrElse("")

              val hsTrimmed = extract(hs)
              val esTrimmed = extract(es)
              val minLength = args.getOrElse("minLength", "8").toInt
              val fracOfSol = args.getOrElse("fracOfSol", "0.3").toDouble
              if (hsTrimmed.length >= fracOfSol * esTrimmed.length) run(() =>
                prove(
                  ("==> " + Modes.EXPLANATION_CHECK + "&full<->" + Modes.EXPLANATION_CHECK + "&full").asSequent,
                  byUS(Ax.equivReflexive),
                )
              )
              else if (hsTrimmed.length >= minLength) run(() =>
                prove(
                  ("==> " + Modes.EXPLANATION_CHECK + "&min<->" + Modes.EXPLANATION_CHECK + "&min").asSequent,
                  byUS(Ax.equivReflexive),
                )
              )
              else Right("Please elaborate your explanation")
            case (_, TextArtifact(None)) => run(() =>
                prove(
                  ("==> " + Modes.EXPLANATION_CHECK + "&full<->" + Modes.EXPLANATION_CHECK + "&full").asSequent,
                  byUS(Ax.equivReflexive),
                )
              )
            case (TextArtifact(None), _) => Right("Missing answer")
            case _ => Right("Answer must be an explanation, but got " + have.longHintString)
          }
        case Modes.TEST_MODEL =>
          val (havePrecondition, havePostcondition) = have match {
            case ListExpressionArtifact(exprs) => (exprs.head, exprs.last)
            case _ => return Right(Messages.INSPECT)
          }
          try {
            val expectPrecondition = args.get("precondition") match { case Some(p) => p.asFormula }
            val expectPostcondition = args.get("postcondition") match { case Some(p) => p.asFormula }

            def makeResponse(preconditionOk: Boolean, postconditionOk: Boolean): String = {
              var response: String = "";
              if (!preconditionOk) {
                response = response + "\nYou may be assuming too much. Consider weakening your assumptions."
              }
              if (!postconditionOk) {
                response = response + "\nYour safety property may not be strong enough. Consider strengthening it."
              }
              if (preconditionOk & postconditionOk) { response = Messages.OK }
              response
            }

            val preconditionOk =
              isFormulaImplied(expectPrecondition.asInstanceOf[Formula], havePrecondition.asInstanceOf[Formula])
            val postconditionOk =
              isFormulaImplied(havePostcondition.asInstanceOf[Formula], expectPostcondition.asInstanceOf[Formula])
            Right(makeResponse(preconditionOk, postconditionOk))
          } catch { case _: Throwable => Right(Messages.INSPECT) }
        case Modes.CHECK_MODELPLEX_MONITOR => AskGrader(Some(Modes.POLY_EQ), args, expected).check(have) match {
            case Left(result) => Left(result)
            case r @ Right("INSPECT") => AskGrader(
                Some(Modes.QE),
                args ++ Map("question" -> ("!(" + QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "1)")),
                expected,
              ).check(have) match {
                // answer is satisfiable, now check implication
                case Right(_) => AskGrader(
                    Some(Modes.QE),
                    args ++ Map(
                      "question" -> ("(" + QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "1) -> " + expected.prettyString)
                    ),
                    expected,
                  ).check(have) match {
                    case Left(_) => Left(prove(
                        s"==> ${Modes.CHECK_MODELPLEX_MONITOR}&partialimplies <-> ${Modes.CHECK_MODELPLEX_MONITOR}&partialimplies"
                          .asSequent,
                        byUS(Ax.equivReflexive),
                      ))
                    case r @ Right("INSPECT") => (expected, have) match {
                        case (e: ExpressionArtifact, h: ExpressionArtifact) => (e.expr, h.expr) match {
                            case (ef: Formula, hf: Formula) =>
                              val fvDiff = (StaticSemantics.symbols(e.expr) -- StaticSemantics.symbols(h.expr))
                                .filter(_.isInstanceOf[Variable])
                                .map(_.asInstanceOf[Variable])
                              if (fvDiff.nonEmpty) {
                                val existsExpected = fvDiff
                                  .foldLeft[Formula](ef)({ case (p, v) => Exists(v :: Nil, p) })
                                AskGrader(
                                  Some(Modes.QE),
                                  args ++ Map(
                                    "question" ->
                                      (QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "1 -> " +
                                        existsExpected.prettyString)
                                  ),
                                  expected,
                                ).check(have) match {
                                  case Left(_) =>
                                    val v = fvDiff.map(_.prettyString).mkString(",")
                                    // @todo measure "importance" of variables, e.g., occurs in how many of the FormulaTools.atomicFormulas(ef)
                                    val expectedCount = StaticSemantics.symbols(e.expr).count(_.isInstanceOf[Variable])
                                    Left(prove(
                                      s"==> ${Modes.CHECK_MODELPLEX_MONITOR}&partialexists($v,${fvDiff.size},$expectedCount) <-> ${Modes
                                          .CHECK_MODELPLEX_MONITOR}&partialexists($v,${fvDiff.size},$expectedCount)"
                                        .asSequent,
                                      byUS(Ax.equivReflexive),
                                    ))
                                  case r => r
                                }
                              } else r
                            case _ => r
                          }
                        case _ => r
                      }
                    case _ => r
                  }
                case _ => r
              }
            case Right(errorMsg) => Right(errorMsg)
          }
        case Modes.BELLE_PROOF =>
          def lastStep(t: BelleExpr): BelleExpr = t match {
            case SeqTactic(s) => s.last
            case _ => t
          }

          def runBelleProof(question: String, answers: List[String]): Either[ProvableSig, String] = {
            run(() => {
              val generator = new ConfigurableGenerator[GenProduct]()
              Parser
                .parser
                .setAnnotationListener((p: Program, inv: Formula) =>
                  generator.products +=
                    (p -> (generator.products.getOrElse(p, Nil) :+ (inv, Some(AnnotationProofHint(tryHard = true))))
                      .distinct)
                )
              TactixInit.invSupplier = generator
              val m = expand(question, answers, Parser.parser).asInstanceOf[Formula]
              val t = expand(args("tactic"), answers, BelleParser)
              val p = prove(Sequent(IndexedSeq(), IndexedSeq(m)), t)
              // tactics that end in assert are checking whether or not the proof ends in a certain state; all others
              // are expected to be proved
              if (!p.isProved) {
                lastStep(t) match {
                  case n: NamedBelleExpr if n.name == "assert" =>
                    prove(
                      ("==> " + Modes.BELLE_PROOF + "&byassert<->" + Modes.BELLE_PROOF + "&byassert").asSequent,
                      byUS(Ax.equivReflexive),
                    )
                  case _ => p
                }
              } else p
            })
          }

          args.get("question") match {
            case Some(q) => have match {
                case h: ExpressionArtifact => runBelleProof(q, h.exprString :: Nil)
                case ListExpressionArtifact(hs) => runBelleProof(q, hs.map(_.prettyString))
                case SequentArtifact(goals) => runBelleProof(q, goals.map(_.toFormula).map(_.prettyString))
                case SubstitutionArtifact(s) => runBelleProof(
                    q,
                    s.map(sp => sp.what.prettyString + "~>" + sp.repl.prettyString).mkString("", "::", "::nil") :: Nil,
                  )
                case _ =>
                  Right("Answer must a a KeYmaera X expression or list of expressions, but got " + have.longHintString)
              }
            case None =>
              val t = BelleParser(args("tactic"))
              (have, expected) match {
                case (h: ExpressionArtifact, e: ExpressionArtifact) => (h.expr, e.expr) match {
                    case (hf: Formula, ef: Formula) =>
                      run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hf, ef))), t))
                    case _ => Right(
                        "Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " +
                          have.longHintString
                      )
                  }
                case (SequentArtifact(h), SequentArtifact(e)) =>
                  val combined = sequentsToFormula(e, h, Equiv)
                  val lemmaResults = h
                    .zip(e)
                    .map({ case (hs, es) =>
                      run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hs.toFormula, es.toFormula))), t))
                    })
                  if (lemmaResults.forall(_.isLeft)) {
                    val lemmas = lemmaResults.map(_.left.toOption.get).map(byUS)
                    run(() =>
                      prove(
                        Sequent(IndexedSeq(), IndexedSeq(combined)),
                        OnAll(andR(Symbol("R"))) * (e.size - 1) & BranchTactic(lemmas),
                      )
                    )
                  } else { lemmaResults.find(_.isRight).get }
                case _ => Right("Answer must a KeYmaera X formula or sequent, but got " + have.longHintString)
              }
          }
        case Modes.CHECK_ARCHIVE =>
          // @todo not sure what we could do with a "tactic" argument that is not already possible in the archive, ignore for now
          val entries = have match {
            case TacticArtifact(s, _) => args.get("question") match {
                case Some(q) => expand(q, s :: Nil, ArchiveParser.parse(_, parseTactics = true))
                case None => return Right(Messages.INSPECT)
              }
            case a: ArchiveArtifact => a.entries
            case t: TextArtifact => t.value match {
                case None => return Right(Messages.BLANK)
                case Some(t) =>
                  try { ArchiveParser.parse(t, parseTactics = true) }
                  catch { case ex: ParseException => return Right(ex.getMessage) }
              }
          }
          if (entries.count(_.kind == "theorem") != 1) return Right(
            "Unexpected archive content: any number of lemmas allowed, but expected exactly 1 ArchiveEntry|Theorem"
          )
          val results = entries.map(e =>
            e -> run(() =>
              prove(
                Sequent(IndexedSeq(), IndexedSeq(e.model.asInstanceOf[Formula])),
                e.tactics.headOption.map(_._3).getOrElse(skip),
              )
            )
          )
          if (results.forall(_._2.isLeft)) results.find(_._1.kind == "theorem").get._2
          else Right("Unproved: " + results.filter(_._2.isRight).map(_._1.name).mkString(","))
      }
    }

    /**
     * Checks artifact `have` for being of the kind expected by artifact `expected`. Returns either the (elaborated)
     * artifact `have`, or an error message.
     */
    private def checkArtifactKind(have: Artifact, expected: Artifact): Either[Artifact, String] =
      (have, expected) match {
        case (_, AnyOfArtifact(artifacts)) =>
          val anyOfResults = artifacts.map(checkArtifactKind(have, _))
          anyOfResults.find(r => r.isRight || r.left.toOption.get != have) match {
            case Some(result) => result
            case None => Left(have)
          }
        case (TextArtifact(h), TextArtifact(Some(_))) if h.getOrElse("").trim.isEmpty => Right(Messages.BLANK)
        case (ExpressionArtifact(e, _), _) if e.trim.isEmpty => Right(Messages.BLANK)
        case (ListExpressionArtifact(Nil), _) => Right(Messages.BLANK)
        case (SequentArtifact(Nil), _) => Right(Messages.BLANK)
        case (h: ExpressionArtifact, e: ExpressionArtifact) => Try(h.as(e.expr.kind)).toOption match {
            case None => Right(errorMsg(e, h))
            case Some(_) => Left(h.copy(kind = Some(e.expr.kind)))
          }
        case (h: ExpressionArtifact, e @ ListExpressionArtifact(exprs)) =>
          if (exprs.exists(_.kind != h.expr.kind)) Right(errorMsg(e, h)) else Left(have)
        case (h @ ListExpressionArtifact(have), e: ExpressionArtifact) =>
          if (have.exists(_.kind != e.expr.kind)) Right(errorMsg(e, h)) else Left(h)
        case (h @ ListExpressionArtifact(have), e @ ListExpressionArtifact(expected)) =>
          require(expected.map(_.kind).toSet.nonEmpty)
          if (expected.map(_.kind).toSet.size > 1) {
            if (expected.zip(have).exists({ case (ee, he) => ee.kind != he.kind })) Right(errorMsg(e, h)) else Left(h)
          } else if (have.exists(_.kind != expected.head.kind)) { Right(errorMsg(e, h)) }
          else Left(h)
        case (h, e) => if (!e.getClass.isAssignableFrom(h.getClass)) Right(errorMsg(e, h)) else Left(have)
        case _ => Left(have)
      }
  }

  /** A grader that has access to multiple answers. */
  case class MultiAskGrader(main: Grader, earlier: Map[Int, Grader]) extends Grader {
    private val grader = main match {
      case AskGrader(mode, args, expected) =>
        val mergedExpected = expected // @todo ignored for now

        val ARG_INDEX = (Regex.quote(QuizExtractor.AskQuestion.ARG_PLACEHOLDER) + """(?<argPlaceholder>-?\d+)""").r
        val argIdxs = args
          .values
          .flatMap(v => { ARG_INDEX.findAllMatchIn(v).map(_.group("argPlaceholder").toInt).toList })
          .toList
          .sorted
        val newArgIdxs = argIdxs.map(i => (i, if (i < 0) i + earlier.keys.size + 1 else i + earlier.keys.size))
        val mergedArgs = args.map({ case (k, v) =>
          val rewrittenBackRefs = newArgIdxs.foldRight(v)({ case ((i, j), mv) =>
            mv.replace(QuizExtractor.AskQuestion.ARG_PLACEHOLDER + i, QuizExtractor.AskQuestion.ARG_PLACEHOLDER + j)
          })
          (k, rewrittenBackRefs)
        })

        AskGrader(mode, mergedArgs, mergedExpected)
    }

    override val expected: Artifact = grader.expected
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      // @note assumed sorted from earliest to main artifact
      case MultiArtifact(as) =>
        if (as.size < 1 + earlier.size) {
          // @note some earlier answers not parseable
          Right("FAILED:IGNORE explanation for a wrong answer")
        } else grader.mode match {
          case Some(AskGrader.Modes.EXPLANATION_CHECK) =>
            val mainArtifact = as.last
            grader.args.get("ifCorrect") match {
              case Some(_) =>
                val prereqAnsweredCorrectly = earlier
                  .zip(as.dropRight(1))
                  .forall({ case ((_, g), a) =>
                    g.check(a) match {
                      case Left(p) => p.isProved
                      case _ => false
                    }
                  })
                if (prereqAnsweredCorrectly) grader.check(mainArtifact)
                else Right("FAILED:IGNORE explanation for a wrong answer")
              case None => grader.check(mainArtifact)
            }
          case _ =>
            val mergedHave = as.reduceRight[Artifact]({
              case (a: ExpressionArtifact, b: ExpressionArtifact) => ListExpressionArtifact(a.expr :: b.expr :: Nil)
              case (a: ExpressionArtifact, ListExpressionArtifact(all)) => ListExpressionArtifact(all :+ a.expr)
              case (TextArtifact(None), _) => return Right("FAILED: missing answer for prerequisite question")
              case (_, TextArtifact(None)) => return Right(Messages.BLANK)
            })
            grader.check(mergedHave)
        }
    }
  }

  case class OneChoiceGrader(args: Map[String, String], expected: ChoiceArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case ChoiceArtifact(Nil) => Right(Messages.BLANK)
      case ChoiceArtifact(h) =>
        // @note correct if answering with any of the correctly marked solutions
        if (h.toSet.subsetOf(expected.selected.toSet)) run(
          () =>
            KeYmaeraXProofChecker(1000, Declaration(Map.empty))(closeT)(Sequent(IndexedSeq.empty, IndexedSeq(True))),
          None,
        )
        else Right("")
    }
  }
  case class AnyChoiceGrader(args: Map[String, String], expected: ChoiceArtifact) extends Grader {
    private val ANYCHOICE_MODE = "anychoice"
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case ChoiceArtifact(Nil) => Right(Messages.BLANK)
      case ChoiceArtifact(h) =>
        val incorrect = (h.toSet -- expected.selected.toSet) ++ (expected.selected.toSet -- h.toSet)
        // correct if answering with exactly the correct yes/no pattern (modulo order)
        if (incorrect.isEmpty) run(
          () => prove(s"==> $ANYCHOICE_MODE&full <-> $ANYCHOICE_MODE&full".asSequent, byUS(Ax.equivReflexive)),
          None,
        )
        // partial credit for 75% correct
        else if (incorrect.size / expected.selected.toSet.size <= 0.25) run(
          () => prove(s"==> $ANYCHOICE_MODE&partial <-> $ANYCHOICE_MODE&partial".asSequent, byUS(Ax.equivReflexive)),
          None,
        )
        else Right("")
    }
  }

  case class AskTFGrader(expected: BoolArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case BoolArtifact(None) => Right(Messages.BLANK)
      case BoolArtifact(Some(h)) =>
        val ef = if (expected.value.get) True else False
        val hf = if (h) True else False
        run(
          () =>
            KeYmaeraXProofChecker(1000, Declaration(Map.empty))(useAt(Ax.equivReflexive)(1))(
              Sequent(IndexedSeq.empty, IndexedSeq(Equiv(hf, ef)))
            ),
          None,
        )
    }
  }

  /** Runs a proof returning either the proved provable as a witness of a hint message. */
  private def run(p: => () => ProvableSig, failHint: Option[String]): Either[ProvableSig, String] = {
    Try(p()) match {
      case Success(p) => Left(p)
      case Failure(BelleUnfinished(msg, _)) => Right(msg)
      case Failure(ex: BelleUserCorrectableException) => Right(ex.getMessage)
      case Failure(ex: TacticInapplicableFailure) if ex.getMessage.startsWith("QE with Z3 gives UNKNOWN") =>
        Right(Messages.INSPECT)
      case Failure(_: TimeoutException) => Right(Messages.INSPECT)
      case Failure(_) => Right(failHint.getOrElse(""))
    }
  }

  /** Proves equivalence of `a` and `b` by QE. */
  def qe(a: Formula, b: Formula, op: (Formula, Formula) => Formula): ProvableSig = {
    KeYmaeraXProofChecker(60, Declaration(Map.empty))(QE)(Sequent(IndexedSeq.empty, IndexedSeq(op(a, b))))
  }

  /** Compares terms `a` and `b` for having the same real values. */
  def valueEquality(a: Term, b: Term): ProvableSig = bigdecimalQE(Equal(a, b))

  /** Compares terms in lists `a` and `b` pairwise for the same real value. */
  def valueEquality(a: List[Term], b: List[Term]): ProvableSig = {
    require(
      a.nonEmpty && a.length == b.length,
      "Same-length non-empty lists expected, but got " + a.mkString(",") + " vs. " + b.mkString(","),
    )
    bigdecimalQE(a.zip(b).map({ case (a, b) => Equal(a, b) }).reduceRight(And))
  }

  /** Invokes the BigDecimalQETool but returns an open proof if statement `fml` is false. */
  private def bigdecimalQE(fml: Formula): ProvableSig = {
    val p = ProvableSig.proveArithmetic(BigDecimalQETool, fml)
    p.conclusion match {
      case Sequent(IndexedSeq(), IndexedSeq(Equiv(f, True))) if fml == f => p
      case _ => ProvableSig.startPlainProof(False)
    }
  }

  /** Proves polynomial equality of `a` and `b`. */
  def polynomialEquality(a: Term, b: Term): ProvableSig = (a, b) match {
    case (Pair(al, ar), Pair(bl, br)) =>
      if (polynomialEquality(al, bl).isProved) polynomialEquality(ar, br)
      else throw new IllegalArgumentException("Pair left-hand sides not equal")
    case (_: Pair, _) => throw new IllegalArgumentException("Unable to compare pair to non-pair term")
    case (_, _: Pair) => throw new IllegalArgumentException("Unable to compare pair to non-pair term")
    case _ =>
      val expa = encodeNonConstPolynomials(a)
      val expb = encodeNonConstPolynomials(b)
      // @todo extend PolynomialArithV2.equate
      val funca = extractFunctions(expa)
        .map({ case FuncOf(fn @ Function(name, idx, _, _, _), args) =>
          (fn, StaticSemantics.freeVars(args).toSet) -> (BaseVariable(name + nameOf(args) + "_", idx), args)
        })
        .toMap
      val funcb = extractFunctions(expb)
        .map({ case FuncOf(fn @ Function(name, idx, _, _, _), args) =>
          (fn, StaticSemantics.freeVars(args).toSet) -> (BaseVariable(name + nameOf(args) + "_", idx), args)
        })
        .toMap
      require(
        funca.keys == funcb.keys,
        "Expected all function symbols to match, but found non-matching symbols " + funca.keys.mkString(",") + " vs. " +
          funcb.keys.mkString(","),
      )
      val matchedArgs = funca.map({ case (fn, (_, a)) => (a, funcb(fn)._2) })
      require(
        matchedArgs.forall({ case (arga, argb) => polynomialEquality(arga, argb).isProved }),
        "Expected uninterpreted function arguments to be equal, but not all are.",
      )
      val encodeda = encodeFunctions(expa, funca.map({ case (fn, (v, _)) => fn -> v }))
      val encodedb = encodeFunctions(expb, funcb.map({ case (fn, (v, _)) => fn -> v }))
      KeYmaeraXProofChecker(60, Declaration(Map.empty))(PolynomialArithV2.equate(1))(
        Sequent(IndexedSeq.empty, IndexedSeq(Equal(encodeda, encodedb)))
      )
  }

  private def nameOf(t: Term): String = StaticSemantics
    .freeVars(t)
    .toSet[Variable]
    .map(_.prettyString.replace("_", "$u$"))
    .mkString("")

  /** Extracts all function subterms of term `t`. */
  private def extractFunctions(t: Term): List[Term] = {
    val fns = ListBuffer.empty[Term]
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case FuncOf(_, Nothing) => Left(None)
          case fn: FuncOf =>
            fns.append(fn)
            Left(None)
          case _ => Left(None)
        }
      },
      t,
    )
    fns.toList
  }

  private def encodeFunctions(t: Term, encoding: Map[(NamedSymbol, Set[Variable]), Term]): Term = {
    ExpressionTraversal
      .traverse(
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case FuncOf(fn, args) => encoding.get((fn, StaticSemantics.freeVars(args).toSet)) match {
                case Some(e) => Right(e)
                case _ => Left(None)
              }
            case _ => Left(None)
          }
        },
        t,
      )
      .get
  }

  /** Encodes `x^y` and `x/y` for non-constant polynomial exponent as pow(x,y) and div(x,y). */
  private def encodeNonConstPolynomials(t: Term): Term = {
    ExpressionTraversal
      .traverse(
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case Power(base, exp) =>
              if (StaticSemantics.freeVars(exp).isEmpty) Left(None)
              else Right(FuncOf(
                // TODO: potential use case?
                Function("pow", None, Tuple(Real, Real), Real, interp = None),
                Pair(encodeNonConstPolynomials(base), encodeNonConstPolynomials(exp)),
              ))
            case Divide(a, b) =>
              if (StaticSemantics.freeVars(b).isEmpty) Left(None)
              else Right(FuncOf(
                // TODO: as above
                Function("div", None, Tuple(Real, Real), Real, interp = None),
                Pair(encodeNonConstPolynomials(a), encodeNonConstPolynomials(b)),
              ))
            case _ => Left(None)
          }
        },
        t,
      )
      .get
  }

  /** Collects terms and compares for polynomial equality. Checks parent operators along the way. */
  def polynomialEquality(a: Formula, b: Formula, normalize: Boolean): ProvableSig = {
    if (
      FormulaTools.atomicFormulas(a).forall(_.isInstanceOf[Equal]) &&
      FormulaTools.atomicFormulas(b).forall(_.isInstanceOf[Equal])
    ) { groebnerBasisEquality(a, b, normalize) }
    else generalPolynomialEquality(a, b, normalize)
  }

  /** Polynomial equality by Groebner basis comparison for formulas whose atoms are all equalities. */
  private def groebnerBasisEquality(a: Formula, b: Formula, normalize: Boolean): ProvableSig = {
    val at = SimplifierV3.algNormalize(a)._1 match { case Equal(l, Number(n)) if n == 0 => l }
    val bt = SimplifierV3.algNormalize(b)._1 match { case Equal(l, Number(n)) if n == 0 => l }
    ToolProvider.algebraTool() match {
      case Some(tool) =>
        val gba = tool.groebnerBasis(at :: Nil)
        tool.polynomialReduce(bt, gba) match {
          case (_, Number(n)) if n == 0 =>
            val gbb = tool.groebnerBasis(bt :: Nil)
            tool.polynomialReduce(at, gbb) match {
              case (_, Number(n)) if n == 0 => prove(Sequent(IndexedSeq(), IndexedSeq(True)), closeT)
              case _ => ProvableSig.startPlainProof(False)
            }
          case _ => ProvableSig.startPlainProof(False)
        }
      case None => generalPolynomialEquality(a, b, normalize)
    }
  }

  /**
   * Approximates polynomial equality for general formulas by comparing program/formula operators and term polynomial
   * equality on the resulting leafs. Not able to handle commutativity and other simple differences.
   */
  private def generalPolynomialEquality(a: Formula, b: Formula, normalize: Boolean): ProvableSig = {
    val terms = ListBuffer.empty[(PosInExpr, Equal)]
    val doNormalize = new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
        if (e.isFOL) { Right(SimplifierV3.semiAlgNormalize(e)._1) }
        else Left(None)
      }
    }
    val na = if (normalize) ExpressionTraversal.traverse(doNormalize, a).get else a
    val nb = if (normalize) ExpressionTraversal.traverse(doNormalize, b).get else b

    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = {
          // @note avoids comparing sub-terms
          if (!terms.lastOption.exists({ case (last, _) => p.pos.startsWith(last.pos) })) {
            val f = nb.sub(p) match {
              case Some(t: Term) => t
              case t => throw new IllegalArgumentException(
                  "Formulas differ at position " + p.prettyString + ": expected " + e.prettyString + ", but got " +
                    t.map(_.prettyString)
                )
            }
            terms.append((p, Equal(e, f)))
          }
          Left(None)
        }
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
          require(
            nb.sub(p).map(_.getClass).contains(e.getClass),
            "Formula operators do not match at position '" + p.prettyString + "'; expected " + e.prettyString + " (" +
              e.getClass.getSimpleName + ") but got " +
              nb.sub(p).map(f => f.prettyString + " (" + f.getClass.getSimpleName + ")").getOrElse("none"),
          )
          Left(None)
        }
        override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = {
          require(
            nb.sub(p).map(_.getClass).contains(e.getClass),
            "Program operators do not match at position '" + p.prettyString + "'; expected " + e.prettyString + " (" +
              e.getClass.getSimpleName + ") but got " +
              nb.sub(p).map(f => f.prettyString + " (" + f.getClass.getSimpleName + ")").getOrElse("none"),
          )
          Left(None)
        }
      },
      na,
    )

    val (realTerms, otherTerms) = terms.partition({ case (_, Equal(l, r)) => l.sort == Real && r.sort == Real })
    require(
      otherTerms.forall({ case (_, Equal(l, r)) => l == r }),
      "Expected all non-Real terms to be syntactically equal, but got " + otherTerms.mkString(","),
    )

    if (realTerms.nonEmpty) {
      val combined = realTerms.map(_._2).reduceRight(And)
      val lemmas = realTerms.map({ case (_, e) => polynomialEquality(e.left, e.right) }).map(byUS).toList
      prove(
        Sequent(IndexedSeq(), IndexedSeq(combined)),
        OnAll(andR(Symbol("R")) | nil) * (realTerms.size - 1) & BranchTactic(lemmas),
      )
    } else {
      // @note formulas without terms, such as true/false or [ctrl;]true
      syntacticEquality(a, b)
    }
  }

  /** Proves polynomial equality between the terms resulting from chasing simple programs in `a` and `b`. */
  def polynomialEquality(a: Sequent, b: Sequent, normalize: Boolean): ProvableSig = {
    polynomialEquality(a.toFormula, b.toFormula, normalize)
  }

  /** Compares expressions for syntactic equality. */
  def syntacticEquality(a: Expression, b: Expression): ProvableSig = (a, b) match {
    case (af: Formula, bf: Formula) => KeYmaeraXProofChecker(1000, Declaration(Map.empty))(useAt(Ax.equivReflexive)(1))(
        Sequent(IndexedSeq(), IndexedSeq(Equiv(af, bf)))
      )
    case (at: Term, bt: Term) => KeYmaeraXProofChecker(1000, Declaration(Map.empty))(useAt(Ax.equalReflexive)(1))(
        Sequent(IndexedSeq(), IndexedSeq(Equal(at, bt)))
      )
    case (ap: Program, bp: Program) => KeYmaeraXProofChecker(1000, Declaration(Map.empty))(useAt(Ax.equivReflexive)(1))(
        Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(ap, True), Box(bp, True))))
      )
  }

  /** Compares sequents for syntactic equality. */
  def syntacticEquality(a: List[Sequent], b: List[Sequent]): ProvableSig = {
    require(b.nonEmpty && a.size == b.size, "Cannot check empty lists of sequents or sequent lists of different size")
    val fmls = a
      .sortBy(_.prettyString)
      .zip(b.sortBy(_.prettyString))
      .map({ case (as, bs) =>
        val edistinct = Sequent(bs.ante.distinct, bs.succ.distinct)
        (sequentToFormula(as, edistinct), edistinct.toFormula)
      })
    syntacticEquality(fmls.map(_._1).reduceRight(And), fmls.map(_._2).reduceRight(And))
  }

  def dIPremiseCheck(a: Formula, b: Formula, diffAssignsMandatory: Boolean, normalize: Boolean): ProvableSig = {
    if (diffAssignsMandatory) {
      def collectDiffAssigns(f: Formula) = {
        val diffAssigns = ListBuffer.empty[Program]
        ExpressionTraversal.traverse(
          new ExpressionTraversalFunction() {
            override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] =
              e match {
                case a @ Assign(_: DifferentialSymbol, _) =>
                  diffAssigns.append(a)
                  Left(None)
                case _: Compose => Left(None)
                case _ => throw new IllegalArgumentException(
                    "Only (compositions of) differential assignments allowed in dI result, but found " + e.prettyString
                  )
              }
          },
          f,
        )
        diffAssigns.toList
      }

      val ads = collectDiffAssigns(a).map({ case Assign(d: DifferentialSymbol, r) => (d, r) }).groupBy(_._1)
      val bds = collectDiffAssigns(b).map({ case Assign(d: DifferentialSymbol, r) => (d, r) }).groupBy(_._1)
      require(
        ads.forall(_._2.size == 1),
        "Differential assignments must be unique, but got " +
          ads.find(_._2.size > 1).map(_._1.prettyString).getOrElse(""),
      )
      require(
        bds.forall(_._2.size == 1),
        "Differential assignments must be unique, but got " +
          bds.find(_._2.size > 1).map(_._1.prettyString).getOrElse(""),
      )
      require(
        ads.keys == bds.keys,
        "Differential assignments do not match: expected assignments to " + ads.map(_._1.prettyString).mkString(",") +
          " but found " + (if (bds.isEmpty) "none" else bds.map(_._1.prettyString).mkString(",")),
      )
      val zipped = for (key <- ads.keys) yield (key, ads(key).map(_._2).head, bds(key).map(_._2).head)
      assert(
        zipped.map({ case (_, a, b) => polynomialEquality(a, b) }).forall(_.isProved),
        "Unexpected differential assignment right-hand side",
      )
    }

    val ap: ProvableSig =
      KeYmaeraXProofChecker(1000, Declaration(Map.empty))(chase(1))(Sequent(IndexedSeq(), IndexedSeq(a)))
    val bp: ProvableSig =
      KeYmaeraXProofChecker(1000, Declaration(Map.empty))(chase(1))(Sequent(IndexedSeq(), IndexedSeq(b)))
    polynomialEquality(ap.subgoals.head, bp.subgoals.head, normalize)
  }

  def dIPremiseCheck(a: Sequent, b: Sequent, diffAssignsMandatory: Boolean, normalize: Boolean): ProvableSig = {
    dIPremiseCheck(
      a.toFormula match {
        case Imply(True, fml) => fml
        case f => f
      },
      b.toFormula match {
        case Imply(True, fml) => fml
        case f => f
      },
      diffAssignsMandatory,
      normalize,
    )
  }

  /** Checks `inv` for being a differential invariant of `ode`. */
  def dICheck(ode: ODESystem, inv: Formula): ProvableSig = {
    require(
      !StaticSemantics
        .freeVars(SimplifierV3.formulaSimp(inv, HashSet.empty, SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1)
        .isEmpty,
      "Invariant " + inv.prettyString + " does not mention free variables",
    )
    KeYmaeraXProofChecker(60, Declaration(Map.empty))(dI(auto = Symbol("cex"))(1))(Sequent(
      IndexedSeq(inv),
      IndexedSeq(Box(ode, inv)),
    ))
  }

  /** Checks that formula `h` is equivalent differential invariant to formula `e`, i.e. (e<->h) & (e' -> h') */
  def dIReductionCheck(h: Formula, e: Formula): ProvableSig = {
    val abbreviatePrimes = TacticFactory.anon { s: Sequent =>
      StaticSemantics
        .freeVars(s)
        .toSet
        .filter(_.isInstanceOf[DifferentialSymbol])
        .map(abbrvAll(_, None))
        .reduceRightOption[BelleExpr](_ & _)
        .getOrElse(skip) & SaturateTactic(hideL(Symbol("L")))
    }
    KeYmaeraXProofChecker(60, Declaration(Map.empty))(
      chase(1, PosInExpr(1 :: 0 :: Nil)) & chase(1, PosInExpr(1 :: 1 :: Nil)) & abbreviatePrimes &
        SimplifierV3.fullSimplify & prop & OnAll(QE & done)
    )(Sequent(IndexedSeq(), IndexedSeq(And(Equiv(e, h), Imply(DifferentialFormula(e), DifferentialFormula(h))))))
  }

  /** Checks `inv` for being a loop invariant for `question` of the shape `P->[{a;}*]Q` or `[{a;}*]P`. */
  def loopCheck(question: Formula, inv: Formula): ProvableSig = {
    def loopCheckTactic(inv: Formula): BelleExpr = {
      loop(inv)(1) <
        (
          autoImpl(loop(FixedGenerator(List.empty)), ODE, keepQEFalse = true) &
            DebuggingTactics.done("Precondition does not imply invariant"),
          autoImpl(loop(FixedGenerator(List.empty)), ODE, keepQEFalse = true) &
            DebuggingTactics.done("Invariant does not imply postcondition"),
          autoImpl(loop(FixedGenerator(List.empty)), ODE, keepQEFalse = true) &
            DebuggingTactics.done("Invariant is not preserved by loop body"),
        ) & done
    }

    question match {
      case Imply(a, b @ Box(_: Loop, _)) => prove(Sequent(IndexedSeq(a), IndexedSeq(b)), loopCheckTactic(inv))
      case b @ Box(_: Loop, _) => prove(Sequent(IndexedSeq(), IndexedSeq(b)), loopCheckTactic(inv))
      case _ => throw new IllegalArgumentException("Loop only applicable to P->[{a;}*]Q or [{a;}*]P questions")
    }
  }

  /** True if a->b. */
  def isFormulaImplied(a: Formula, b: Formula): Boolean = {
    try {
      val isImplied = formulaImplication(a, b).isProved
      isImplied
    } catch { case _: Throwable => false }
  }

  def formulaImplication(a: Formula, b: Formula): ProvableSig = {
    KeYmaeraXProofChecker(60, Declaration(Map.empty))(autoClose)(Sequent(IndexedSeq(), IndexedSeq(Imply(a, b))))
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
        case (Some((_, ai)), Some((_, si))) => cohideOnlyL(AntePos(ai)) & cohideOnlyR(SuccPos(si)) & implyRi &
            CMon(PosInExpr(1 :: Nil))
        case _ => throw new TacticInapplicableFailure("No matching contexts found")
      }
    }
    def unloop() = TacticFactory.anon { (seq: Sequent) =>
      val anteLoops = seq
        .ante
        .zipWithIndex
        .find({
          case (Box(Loop(ap), _), _) => FormulaTools.dualFree(ap)
          case _ => false
        })
      val succLoops = seq
        .succ
        .zipWithIndex
        .find({
          case (Box(Loop(bp), _), _) => FormulaTools.dualFree(bp)
          case _ => false
        })
      (anteLoops, succLoops) match {
        case (Some((af @ Box(_, ap), ai)), Some((Box(bbody, bp), si))) =>
          if (ap != bp) throw new TacticInapplicableFailure("No matching loop postconditions found")
          cohideOnlyL(AntePos(ai)) & cohideOnlyR(SuccPos(si)) &
            cut(Box(bbody, af)) <
            (
              useAt(Ax.I)(-2, 1 :: Nil) & boxAnd(-2) & prop & done,
              hideR(1) & implyRi & useAt(Ax.IIinduction, PosInExpr(1 :: Nil))(1) &
                useAt(Ax.iterateb)(1, 1 :: 0 :: Nil) & G(1) & implyR(1) & andL(-1) & hideL(-1) & chase(-1) & chase(1),
            )
      }
    }
    val (as, bs) = (elaborateToSystem(a), elaborateToSystem(b))
    KeYmaeraXProofChecker(60, Declaration(Map.empty))(
      chase(1, 0 :: Nil) & chase(1, 1 :: Nil) &
        SaturateTactic(OnAll(prop & OnAll(searchCMon(PosInExpr(1 :: Nil)) | unloop()))) &
        DebuggingTactics.done("Program is not as expected")
    )(Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(as, p), Box(bs, p)))))
  }

  def contractEquivalence(have: Formula, expected: Formula): ProvableSig = {
    val rephrasePost = TacticFactory.anon { s: Sequent =>
      val anteBoxes = s.ante.filter(_.isInstanceOf[Box])
      val succBoxes = s.succ.zipWithIndex.filter(_._1.isInstanceOf[Box])
      val boxes = (anteBoxes ++ succBoxes.map(_._1)).groupBy({ case Box(prg, _) => prg })
      val postEquivs = boxes.map({ case (k, v) =>
        k -> v.map({ case Box(_, f) => f }).toSet.subsets(2).toList.map(s => Equiv(s.head, s.tail.head))
      })
      val postEquivLemmas = postEquivs
        .map({ case (k, v) => k -> v.map(e => e -> Lemma(proveBy(e, prop), Nil)) })
        .filter(_._2.forall(_._2.fact.isProved))
      succBoxes
        .flatMap({ case (Box(prg, fml), i) =>
          postEquivLemmas
            .getOrElse(prg, List.empty)
            .find({ case (Equiv(l, r), _) => l == fml || r == fml })
            .map({ case (Equiv(l, _), pr) =>
              useAt(pr, if (l == fml) PosInExpr(0 :: Nil) else PosInExpr(1 :: Nil))(
                Position(SuccPos(i)) ++ PosInExpr(1 :: Nil)
              )
            })
        })
        .reduceRightOption[BelleExpr](_ & _)
        .getOrElse(skip)
    }
    KeYmaeraXProofChecker(60, Declaration(Map.empty))(
      chase(1) & prop & OnAll(rephrasePost & prop) & DebuggingTactics.done("")
    )(Sequent(IndexedSeq(), IndexedSeq(Equiv(elaborateToSystems(expected), elaborateToSystems(have)))))
  }

  /** Generic assessment prover uses tactic `t` to prove sequent `s`, aborting after `timeout` time. */
  def prove(s: Sequent, t: BelleExpr): ProvableSig = { KeYmaeraXProofChecker(60, Declaration(Map.empty))(t)(s) }

  /**
   * Exports answers from `chapter` to individual files in directory `out`, on for each question (named 1a.txt ...
   * Xy.txt)
   */
  def exportAnswers(chapter: Submission.Chapter, out: String): Unit = {
    val outDir = new File(out)
    if (!outDir.exists) outDir.mkdirs()

    chapter
      .problems
      .foreach(problem =>
        problem
          .prompts
          .foreach({ prompt =>
            val out = new PrintWriter(new BufferedWriter(new FileWriter(
              s"$outDir${File.separator}${problem.number}${prompt.number}.txt"
            )))
            prompt
              .answers
              .foreach({
                case Submission.ChoiceAnswer(_, _, _, _, text, isSelected) => out.println(text + ":" + isSelected)
                case Submission.TextAnswer(_, _, _, _, answer, _) => out.println(answer)
              })
            out.close()
          })
      )

  }

  /**
   * Grades a submission.
   *
   * @param in
   *   The file to grade
   * @param out
   *   Output directory for answer files
   * @param exportAnswers
   *   Export answers to text files instead of grading
   * @param options
   *   The prover options:
   *   - 'skiponparseerror (optional) skips grading on parse errors
   */
  def grade(
      in: String,
      out: Option[String],
      exportAnswers: Boolean,
      options: Options,
      msgOut: OutputStream,
      resultOut: OutputStream,
  ): Unit = {
    val src = Source.fromFile(in, "UTF-8")
    val input =
      try { src.mkString.parseJson }
      finally { src.close() }
    val chapter = {
      import Submission.SubmissionJsonFormat._
      input.convertTo[Submission.Chapter]
    }

    if (exportAnswers) { this.exportAnswers(chapter, out.getOrElse(".")) }
    else {
      val skipGradingOnParseError = options.skiponparseerror.getOrElse(false)
      grade(chapter, msgOut, resultOut, skipGradingOnParseError)
    }
  }

  private def grade(
      chapter: Submission.Chapter,
      msgOut: OutputStream,
      resultOut: OutputStream,
      skipGradingOnParseError: Boolean,
  ): Unit = {
    val parsedProblems = chapter
      .problems
      .map({ case problem @ Submission.Problem(_, _, _, _, _, _, prompts) =>
        val parsedAnswers = prompts.map(p =>
          try { Left(p -> toAnswerArtifact(p)) }
          catch { case ex: Throwable => Right(p -> ex) }
        )
        (
          problem,
          parsedAnswers.partition(_.isLeft) match {
            case (as, pe) => (as.map(_.left.toOption.get), pe.map(_.toOption.get))
          },
        )
      })

    val msgStream = new PrintStream(msgOut, true)
    if (skipGradingOnParseError && parsedProblems.exists(_._2._2.nonEmpty)) {
      // report parse errors
      reportParseSummary(parsedProblems, msgStream)
      val allGrades = parsedProblems.map({ case (p, (prompts, _)) =>
        (p, None, prompts.map({ case (p, _) => p -> 0.0 }))
      })
      printJSONGrades(allGrades, resultOut)
    } else {
      val allGrades: List[(Submission.Problem, Option[String], List[(Submission.Prompt, Double)])] = parsedProblems
        .map({ case (p, (gradablePrompts, unparseablePrompts)) =>
          msgStream.println(p.number + " " + p.title)

          val allPromptArtifacts = (gradablePrompts ++ unparseablePrompts.map({ case (p, _) => (p, None) }))
            .sortBy(_._1.id)
          val graders = extractGraders(p, allPromptArtifacts)
          val errors = unparseablePrompts.map({ case (prompt, ex: Throwable) => (prompt, Right(ex)) })
          val all = (graders ++ errors).sortBy({ case (p, _) => p.id })
          val grades = all.map({
            case (prompt, Left((grader, Some(answerArtifact)))) =>
              if (prompt.points > 0.0) runGrader(p, prompt, Some(answerArtifact), grader, msgStream)
              else runGrader(p, prompt, Some(answerArtifact), SkipGrader(null, Messages.SKIPPED), msgStream)
            case (prompt, Right(ex)) => reportParseError(p, prompt, ex, msgStream)
          })

          val feedback = graders
            .headOption
            .flatMap({ case (_, Left((g, _))) =>
              g match {
                case AskGrader(_, args, _) => args.get("feedback")
                case MultiAskGrader(main: AskGrader, _) => main.args.get("feedback")
                // @todo feedback for other problems?
                case _ => None
              }
            })
          val percentage =
            if (grades.exists(_._1.points > 0.0)) (100.0 * grades.count(_._2 > 0.0)) / grades.count(_._1.points > 0.0)
            else 1
          msgStream.println(f"${p.number} ) Sum $percentage%2.1f%%")
          feedback match {
            case Some(s) => if (percentage <= 75) msgStream
                .println(s"If you had difficulty with this question you would likely benefit from a review of $s")
            case None => // no feedback annotated
          }
          (p, feedback, grades)
        })
      // printSummaryFeedback(allGrades, msgStream)
      printCSVGrades(allGrades, msgStream)
      printGradeSummary(allGrades, msgStream)
      printJSONGrades(allGrades, resultOut)
    }
  }

  /**
   * Extracts graders from prompts, assumes that all prompts (even unparseable ones) are present in this list. Returns
   * graders for prompts that have answers.
   */
  private def extractGraders(
      problem: Submission.Problem,
      prompts: List[(Submission.Prompt, Option[Artifact])],
  ): List[(Submission.Prompt, Either[(Grader, Option[Artifact]), Throwable])] = {
    val NEG_HASH = (Regex.quote(QuizExtractor.AskQuestion.ARG_PLACEHOLDER) + """(?<argPlaceholder>-\d+)""").r
    val mergedPrompts = prompts
      .zipWithIndex
      .map({
        case (
              (
                p @ Submission.SinglePrompt(
                  _,
                  _,
                  _,
                  _,
                  _,
                  Submission.TextAnswer(_, _, _, Some(Submission.GraderCookie(_, _, method)), _, _) :: Nil,
                ),
                answer,
              ),
              i,
            ) =>
          val backRefs = NEG_HASH.findAllMatchIn(method).map(_.group("argPlaceholder").toInt).toList
          if (backRefs.nonEmpty) {
            val mergedPrompt = Submission.MultiPrompt(p, backRefs.map(j => (j, prompts(i + j)._1)).toMap)
            val answers = answer.map(a => MultiArtifact(backRefs.flatMap(j => prompts(i + j)._2) :+ a))
            (mergedPrompt, answers)
          } else (p, answer)
        case (q, _) => q
      })

    mergedPrompts
      .filter(_._2.isDefined)
      .map({ case (prompt, answerArtifact) => (prompt, Left(toGrader(problem, prompt), answerArtifact)) })
  }

  private def runGrader(
      p: Submission.Problem,
      prompt: Submission.Prompt,
      answerArtifact: Option[Artifact],
      grader: Grader,
      msgStream: PrintStream,
  ): (Submission.Prompt, Double) = {
    msgStream.print(p.number + "." + prompt.number + " (" + prompt.id + ")...")

    def failedMessage(prompt: Submission.Prompt): String = {
      val msg = prompt
        .answers
        .map({
          case Submission.TextAnswer(_, _, _, _, answer, _) =>
            val solfinAnswers = extractSolfinAnswers(answer)
            val sanitizedAnswers = if (solfinAnswers.nonEmpty) solfinAnswers else answer :: Nil
            val shortened = sanitizedAnswers.map(a => { if (a.length <= 100) a else a.substring(0, 95) + "[...]" })
            if (shortened.length > 1) shortened.mkString("\n  ", "\n  ", "") else shortened.headOption.getOrElse("")
          case _: Submission.ChoiceAnswer => ""
        })
        .filter(_.nonEmpty)
        .mkString(",")
      if (msg.nonEmpty) ":" + msg else msg
    }

    answerArtifact match {
      case Some(a) => grader.check(a) match {
          case Left(p) =>
            if (p.isProved) {
              p.conclusion match {
                case Sequent(IndexedSeq(), IndexedSeq(Equiv(And(p, q), _)))
                    if p.prettyString.startsWith(Modes.EXPLANATION_CHECK) =>
                  q.prettyString match {
                    case "full()" =>
                      msgStream.println(Messages.PASS)
                      (prompt, prompt.points)
                    case "min()" =>
                      msgStream.println(Messages.PASS + ":Partial (please elaborate your explanation)")
                      (prompt, prompt.points / 2)
                  }
                case Sequent(IndexedSeq(), IndexedSeq(Equiv(And(p, q), _))) if p.prettyString.startsWith("anychoice") =>
                  q.prettyString match {
                    case "full()" =>
                      msgStream.println(Messages.PASS)
                      (prompt, prompt.points)
                    case "partial()" =>
                      msgStream.println(Messages.PASS + ":Partial")
                      (prompt, prompt.points / 2)
                  }
                case Sequent(IndexedSeq(), IndexedSeq(Equiv(And(p, q), _))) if p.prettyString.startsWith("checkmx") =>
                  if (q.prettyString == "partialimplies()") {
                    msgStream.println(Messages.PASS + ":Partial (answer identifies too many situations as violations)")
                    (prompt, prompt.points * 0.75)
                  } else if (q.prettyString.startsWith("partialexists(")) {
                    val args = q.prettyString.stripPrefix("partialexists(").stripSuffix(")").split(",").toList
                    val (v, missing :: expected :: Nil) = args.splitAt(args.length - 2)
                    msgStream.println(Messages.PASS + ":Partial (think about the role of " + v.mkString(",") + ")")
                    (prompt, prompt.points * 0.5 * (expected.toFloat - missing.toFloat) / expected.toFloat)
                  } else {
                    msgStream.println(Messages.FAILED + failedMessage(prompt))
                    (prompt, 0.0)
                  }
                case _ =>
                  msgStream.println(Messages.PASS)
                  (prompt, prompt.points)
              }
            } else {
              msgStream.println(Messages.FAILED + failedMessage(prompt))
              (prompt, 0.0)
            }
          case Right(hint) =>
            if (hint.nonEmpty && hint == hint.toUpperCase) msgStream.println(hint)
            else {
              msgStream.print(Messages.FAILED + failedMessage(prompt))
              if (hint.trim.nonEmpty) msgStream.println(" (hint: " + hint + ")") else msgStream.println("")
            }
            (prompt, 0.0)
        }
      case None =>
        msgStream.println(Messages.BLANK) // Missing answer
        (prompt, 0.0)
    }
  }

  private def reportParseError(
      problem: Submission.Problem,
      prompt: Submission.Prompt,
      ex: Throwable,
      msgStream: PrintStream,
  ): (Submission.Prompt, Double) = {
    ex match {
      case ex: ParseException => msgStream.println(
          questionIdentifier(problem, prompt) + "..." + Messages.PARSE_ERROR + "\n  " +
            ex.toString.replace("\n", "\n  ")
        )
      case _ => msgStream.println(
          questionIdentifier(problem, prompt) + "..." + Messages.PARSE_ERROR + "\n" +
            ex.getMessage.replace("\n", "\n  ")
        )
    }
    (prompt, 0.0)
  }

  /** Translates a submission prompt into a grader artifact (None if question not answered). */
  private def toAnswerArtifact[T <: Artifact](p: Submission.Prompt): Option[Artifact] = {
    p.name match {
      case "\\ask" =>
        require(
          p.answers.size == 1,
          "Expected exactly 1 answer for text prompt " + p.id + ", but got " + p.answers.size,
        )
        p.answers
          .map({
            case Submission.TextAnswer(_, _, name, _, answer, expected) =>
              if (answer.trim.isEmpty) Some(TextArtifact(None))
              else name match {
                case "\\sol" =>
                  if (expected.startsWith(QuizExtractor.AskQuestion.KYXLINE))
                    Some(QuizExtractor.AskQuestion.artifactsFromKyxString(answer))
                  else if (expected.startsWith(QuizExtractor.AskQuestion.MATH_DELIM))
                    Some(QuizExtractor.AskQuestion.artifactsFromTexMathString(answer))
                  else if (expected.startsWith(QuizExtractor.AskQuestion.LISTING_DELIM)) Some(ArchiveArtifact(answer))
                  else Some(QuizExtractor.AskQuestion.artifactsFromTexTextString(answer))
                case "\\solfin" | "\\solfinask" => Some(QuizExtractor.AskQuestion.solfinArtifactsFromString(answer)._2)
              }
            case a =>
              throw new IllegalArgumentException("Expected text answer for \\ask, but got " + a.getClass.getSimpleName)
          })
          .head
      case "\\onechoice" | "\\anychoice" =>
        val choiceAnswers = p.answers.map(_.asInstanceOf[Submission.ChoiceAnswer])
        Some(ChoiceArtifact(choiceAnswers.filter(_.isSelected).map(_.text)))
      case "\\asktf" =>
        val choiceAnswers = p.answers.map(_.asInstanceOf[Submission.ChoiceAnswer])
        Some(BoolArtifact(choiceAnswers.find(_.isSelected).map(_.text == "True")))
    }
  }

  /** Translates a submission prompt into the question and an expected artifact. */
  private def toExpectedArtifact[T <: Artifact](p: Submission.Prompt): (Option[Artifact], Map[String, String]) = {
    p.name match {
      case "\\ask" =>
        require(
          p.answers.size == 1,
          "Expected exactly 1 answer for text prompt " + p.id + ", but got " + p.answers.size,
        )
        p.answers
          .map({
            case Submission.TextAnswer(_, _, name, _, _, expected) => name match {
                case "\\sol" => (QuizExtractor.AskQuestion.artifactFromSolContent(expected), Map.empty[String, String])
                case "\\solfin" | "\\solfinask" =>
                  val (question, artifact) = QuizExtractor.AskQuestion.solfinArtifactsFromLstList(expected)
                  (Some(artifact), Map("question" -> question))
              }
            case a =>
              throw new IllegalArgumentException("Expected text answer for \\ask, but got " + a.getClass.getSimpleName)
          })
          .head
      case "\\onechoice" | "\\anychoice" =>
        val choiceAnswers = p.answers.map(_.asInstanceOf[Submission.ChoiceAnswer])
        (Some(ChoiceArtifact(choiceAnswers.filter(_.name == "\\choice*").map(_.text))), Map.empty[String, String])
      case "\\asktf" =>
        val choiceAnswers = p.answers.map(_.asInstanceOf[Submission.ChoiceAnswer])
        val expected = choiceAnswers.find(_.name == "\\choice*") match {
          case Some(sol) =>
            if (sol.text == "True") Some(true)
            else if (sol.text == "False") Some(false)
            else throw new IllegalArgumentException("Expected either True or False, but got " + sol.text)
          case None => None
        }
        (Some(BoolArtifact(expected)), Map.empty[String, String])
    }
  }

  private def toGrader(problem: Submission.Problem, p: Submission.Prompt): Grader = p match {
    case mp @ Submission.MultiPrompt(main, earlier) =>
      require(mp.name == "\\ask", "Expected text multiprompt") // @note other questions do not have \algog
      require(
        mp.answers.size == 1,
        "Expected exactly 1 answer for text prompt " + mp.id + ", but got " + mp.answers.size,
      )
      val mainGrader = toGrader(problem, main)
      val earlierGraders = earlier.map({ case (k, v) => (k, toGrader(problem, v)) }).toList.sortBy(_._1)
      MultiAskGrader(mainGrader, earlierGraders.toMap)
    case _: Submission.SinglePrompt => p.name match {
        case "\\ask" =>
          require(
            p.answers.size == 1,
            "Expected exactly 1 answer for text prompt " + p.id + ", but got " + p.answers.size,
          )
          p.answers
            .map({ case Submission.TextAnswer(_, _, _, grader, _, _) =>
              grader match {
                case Some(g) =>
                  val (gr, args) = QuizExtractor.AskQuestion.graderInfoFromString(g.method)
                  toExpectedArtifact(p) match {
                    case (Some(expected), a) =>
                      AskGrader(Some(gr), args ++ a.filter({ case (k, _) => !args.keySet.contains(k) }), expected)
                    case (None, _) => SkipGrader(null, Messages.INSPECT)
                  }
                case None =>
                  // pull grader from file
                  val graderProperties = new Properties()
                  try {
                    graderProperties.load(new FileReader("grader.properties"))
                    val method = graderProperties.getProperty(problem.number + "." + p.number)
                    val (gr, args) = QuizExtractor.AskQuestion.graderInfoFromString(method)
                    toExpectedArtifact(p) match {
                      case (Some(expected), a) => AskGrader(Some(gr), args ++ a, expected)
                      case (None, _) => SkipGrader(null, Messages.INSPECT)
                    }
                  } catch { case _: IOException => SkipGrader(null, Messages.INSPECT) }
              }
            })
            .head
        case "\\onechoice" => toExpectedArtifact(p) match {
            case (Some(expected: ChoiceArtifact), _) => OneChoiceGrader(Map.empty, expected)
            case (None, _) => SkipGrader(null, Messages.INSPECT)
          }
        case "\\anychoice" => toExpectedArtifact(p) match {
            case (Some(expected: ChoiceArtifact), _) => AnyChoiceGrader(Map.empty, expected)
            case (None, _) => SkipGrader(null, Messages.INSPECT)
          }
        case "\\asktf" => toExpectedArtifact(p) match {
            case (Some(expected: BoolArtifact), _) => AskTFGrader(expected)
            case (None, _) => SkipGrader(null, Messages.INSPECT)
          }
      }
    case _ => SkipGrader(null, Messages.INSPECT)
  }

  /** Prints a question identifier for the `i`-th question `prompt` in section `problem`. */
  private def questionIdentifier(problem: Submission.Problem, prompt: Submission.Prompt): String = problem.number +
    "." + prompt.number + " (" + prompt.id + ")"

  private def reportParseSummary(
      parsedProblems: List[
        (Submission.Problem, (List[(Submission.Prompt, Option[Artifact])], List[(Submission.Prompt, Throwable)]))
      ],
      msgStream: PrintStream,
  ): Unit = {
    msgStream.println("Parsing Summary")
    msgStream.println("---------------")
    parsedProblems.foreach({ case (problem, (prompts, errors)) =>
      msgStream.println(problem.number + " " + problem.title)
      if (errors.nonEmpty) {
        val passed = prompts
          .filter({ case (p, _) => !errors.exists(p == _._1) })
          .map({ case (p, _) => (p, questionIdentifier(problem, p) + "..." + Messages.OK) })
        val failed = errors.map({
          case (prompt, ex: ParseException) => (
              prompt,
              questionIdentifier(problem, prompt) + "..." + Messages.PARSE_ERROR + "\n" + ex.toString + "\n----------",
            )
          case (prompt, ex) => (
              prompt,
              questionIdentifier(problem, prompt) + "..." + Messages.PARSE_ERROR + "\n" + ex.getMessage + "\n----------",
            )
        })
        msgStream.println((passed ++ failed).sortBy({ case (p, _) => p.id }).map(_._2).mkString("\n"))
      } else {
        msgStream
          .println(prompts.map({ case (p, _) => questionIdentifier(problem, p) + "..." + Messages.OK }).mkString("\n"))
      }
    })
    msgStream.println("------------")
    msgStream.println("Parsing Done")
    msgStream.println("------------")
  }

  private def printGradeSummary(
      grades: List[(Submission.Problem, Option[String], List[(Submission.Prompt, Double)])],
      out: PrintStream,
  ): Unit = {
    out.println("-------------")
    out.println("Score Summary")
    val score = grades.map({ case (_, _, pg) => pg.map({ case (_, score) => score }).sum }).sum
    val maxScore = grades.map({ case (_, _, pg) => pg.map({ case (p, _) => p.points }).sum }).sum
    out.println("Total points: " + score + "/" + maxScore)
    out.println(f"Total score:  ${(100 * score) / maxScore}%2.1f%%")
    out.println("-------------")
  }

  private def printCSVGrades(
      grades: List[(Submission.Problem, Option[String], List[(Submission.Prompt, Double)])],
      out: PrintStream,
  ): Unit = {
    val gradeStrings = grades.flatMap({ case (problem, _, pg) =>
      pg.map({ case (prompt, score) =>
        questionIdentifier(problem, prompt) :: prompt.id.toString :: score.toString :: Nil
      })
    })
    out.println("-----------")
    out.println("Score Sheet")
    out.println(gradeStrings.map(_.mkString(",")).mkString("\n"))
  }

  private def printJSONGrades(
      grades: List[(Submission.Problem, Option[String], List[(Submission.Prompt, Double)])],
      out: OutputStream,
  ): Unit = {
    def problemTitle(p: Submission.Problem, i: Int): String = if (p.title.isEmpty) s"$i" else s"$i ${p.title}"
    val problemFields = grades
      .zipWithIndex
      .map({ case ((problem, _, _), i) => problemTitle(problem, i) -> JsNumber(problem.points) })
    val scoreFields = grades
      .zipWithIndex
      .map({ case ((problem, _, pg), i) => problemTitle(problem, i) -> JsNumber(pg.map(_._2).sum) })
    val promptScoreFields = grades.flatMap(_._3.map({ case (prompt, score) => prompt.id.toString -> JsNumber(score) }))
    val jsonGrades = JsObject(
      "problems" -> JsObject(problemFields: _*),
      "scores" -> JsObject(scoreFields: _*),
      "prompt_scores" -> JsObject(promptScoreFields: _*),
    )
    out.write(jsonGrades.compactPrint.getBytes("UTF-8"))
  }

  private def printSummaryFeedback(
      grades: List[(Submission.Problem, Option[String], List[(Submission.Prompt, Double)])],
      msgStream: PrintStream,
  ): Unit = {
    val correct = grades.map({ case (_, _, gp) => gp.count(_._2 > 0.0) }).sum
    val total = grades.map({ case (_, _, gp) => gp.size }).sum
    val percentage = (100 * correct) / total
    msgStream.println("\nOverall: " + percentage + "%")
    grades.foreach({
      case (problem, Some(feedback), pg) =>
        val ratio = pg.count(_._2 > 0.0) / pg.size.toDouble
        if (ratio <= 0.75) msgStream.println(problem.number + " " + problem.title)
        if (ratio <= 0.25) {
          msgStream.print(
            s"""  You have found this problem difficult. Before you proceed with an imperfect understanding and
               |  risk causing later misunderstandings, you should carefully review the topics in $feedback."""
              .stripMargin
          )
        } else if (ratio <= 0.5) {
          msgStream.print(
            s"""  You have demonstrated an understanding of the topics covered in this problem,
               |  but also had difficulties with some questions. Before you proceed,
               |  we encourage you to take a closer look at $feedback.""".stripMargin
          )
        } else if (ratio <= 0.75) {
          msgStream.println(
            s"""  You have shown a good understanding of the topics covered in this problem.
               |  If you want to learn more about it, refer to $feedback.""".stripMargin
          )
        }
      case _ => // no feedback annotated
    })

  }

  /**
   * Converts list of `expected` subgoals and list of `actual` subgoals into a formula, combining the formulas in the
   * sequents using `fml` (equivalence checking by default).
   */
  private def sequentsToFormula(
      expected: List[Sequent],
      actual: List[Sequent],
      fml: (Formula, Formula) => Formula = Equiv,
  ) = {
    require(
      expected.nonEmpty && actual.size == expected.size,
      "Cannot check empty lists of sequents or sequent lists of different size",
    )
    val afs = actual.map(_.toFormula)
    val efs = expected.map(_.toFormula)
    afs.zip(efs).map({ case (af, ef) => fml(af, ef) }).reduceRight(And)
  }

  /**
   * Converts sequent `s` into a formula; removes duplicates and sorts formulas according to their index in sequent
   * `ref` for robust syntactic equality comparison of sequents.
   */
  private def sequentToFormula(s: Sequent, ref: Sequent): Formula = {
    Imply(
      s.ante
        .distinct
        .sortWith((a, b) => ref.ante.indexOf(a) < ref.ante.indexOf(b))
        .reduceRightOption(And)
        .getOrElse(True),
      s.succ
        .distinct
        .sortWith((a, b) => ref.succ.indexOf(a) < ref.succ.indexOf(b))
        .reduceRightOption(Or)
        .getOrElse(False),
    )
  }

  private val TACTIC_REPETITION_EXTRACTOR =
    ("for " + Regex.quote(QuizExtractor.AskQuestion.ARG_PLACEHOLDER) + "i do(?<reptac>.*)endfor").r

  /** Expands occurrences of \%i in string `s` with arguments from argument list `args`. */
  @tailrec
  private def expand[T](s: String, args: List[String], parser: String => T): T = {
    val repTacs = TACTIC_REPETITION_EXTRACTOR.findAllMatchIn(s).toList
    if (repTacs.nonEmpty) {
      val unfolded = repTacs
        .map(_.group("reptac"))
        .map(t => {
          t -> (1 to args.size)
            .map(i =>
              t.replace(
                QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "i",
                s"${QuizExtractor.AskQuestion.ARG_PLACEHOLDER}$i",
              )
            )
            .mkString(";")
        })
      val replaced = unfolded.foldRight(s)({ case ((what, repl), s) =>
        s.replace(s"for ${QuizExtractor.AskQuestion.ARG_PLACEHOLDER}i do${what}endfor", repl)
      })
      assert(
        !replaced.contains(QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "i"),
        "Expected to have replaced all variable-length argument repetitions",
      )
      expand(replaced, args, parser)
    } else {
      val ts = (1 to args.size).foldRight(s)({ case (i, s) =>
        s.replace(s"${QuizExtractor.AskQuestion.ARG_PLACEHOLDER}$i", args(i - 1))
      })
      require(!ts.contains(QuizExtractor.AskQuestion.ARG_PLACEHOLDER), "Not enough arguments provided for tactic")
      parser(ts)
    }
  }

  /** Elaborates program constants to system constants in dual-free contexts. */
  private def elaborateToSystem(prg: Program): Program = {
    if (FormulaTools.literalDualFree(prg)) {
      ExpressionTraversal
        .traverse(
          new ExpressionTraversalFunction() {
            override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
              case ProgramConst(name, space) => Right(SystemConst(name, space))
              case _ => Left(None)
            }
          },
          prg,
        )
        .get
    } else prg
  }

  /** Elaborates program constants to system constants. */
  private def elaborateToSystems(f: Formula): Formula = {
    ExpressionTraversal
      .traverse(
        new ExpressionTraversalFunction() {
          override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
            Right(elaborateToSystem(e))
          }
        },
        f,
      )
      .get
  }

}
