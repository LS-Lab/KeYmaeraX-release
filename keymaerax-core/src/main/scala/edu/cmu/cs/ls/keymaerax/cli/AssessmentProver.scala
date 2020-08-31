/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cli

import java.io.{BufferedOutputStream, FileOutputStream, OutputStream, PrintStream, PrintWriter}

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleUnfinished, BelleUserCorrectableException, BranchTactic, OnAll, SaturateTactic, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.{Ax, DebuggingTactics, FixedGenerator, PolynomialArithV2, SimplifierV3, TacticFactory}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.AskGrader.Modes
import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.OptionMap
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, ParseException}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import spray.json._

import scala.annotation.tailrec
import scala.collection.immutable.{HashSet, IndexedSeq}
import scala.collection.mutable.ListBuffer
import scala.io.Source
import scala.util.matching.Regex
import scala.util.{Failure, Success, Try}

/** Assesses dL terms and formulas for equality, equivalence, implication etc. with restricted automation. */
object AssessmentProver {

  /** Assessment prover input artifacts (expressions, sequents etc.) */
  abstract class Artifact {
    def hintString: String
    def longHintString: String = hintString
    /** Checks the artifact for being of a certain shape (skip if None), returns None if shape constraint is met, an error message otherwise. */
    def checkShape(shape: Option[String]): Option[String] = None
  }
  case class ExpressionArtifact(exprString: String) extends Artifact {
    val expr: Expression = exprString.asExpr
    override def hintString: String = expr.kind.toString
    override def longHintString: String = expr.kind.toString + " " + exprString
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
        case Some("qfra") => expr match {
          case f: Formula if StaticSemantics.boundVars(f).isEmpty => None
          case _ => Some("Not a quantifier-free formula of real arithmetic")
        }
        case Some(_) => throw new IllegalArgumentException("Unknown shape " + shape)
        case None => None
      }
    }

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
    }
  }
  case class AskGrader(mode: Option[String], args: Map[String, String], expected: Artifact) extends Grader {
    /** Checks whether artifact `have` fits artifact `expected` using `mode`. */
    override def check(have: Artifact): Either[ProvableSig, String] = {
      (have, expected) match {
        case (TextArtifact(h), _) if h.getOrElse("").trim.isEmpty => return Right("Missing answer")
        case (ExpressionArtifact(e), _) if e.trim.isEmpty => return Right("Missing answer")
        case (ListExpressionArtifact(Nil), _) => return Right("Missing answer")
        case (SequentArtifact(Nil), _) => return Right("Missing answer")
        case (h: ExpressionArtifact, e: ExpressionArtifact) => e.expr match {
          case Divide(BaseVariable(n, None, Real), BaseVariable(a, None, Real))
              if n.equalsIgnoreCase("n") && a.equalsIgnoreCase("a") =>
            return run(() => syntacticEquality(h.expr, e.expr))
          case _ => if (h.expr.kind != e.expr.kind) return Right("Expected a " + e.expr.kind + " but got " + h.expr.kind + " " + h.exprString)
        }
        case (h: ExpressionArtifact, ListExpressionArtifact(exprs)) =>
          if (exprs.exists(_.kind != h.expr.kind)) return Right("Expected a " + exprs.head.kind + " but got " + h.expr.kind + " " + h.exprString)
        case (ListExpressionArtifact(h), e: ExpressionArtifact) =>
          if (h.exists(_.kind != e.expr.kind)) return Right("Expected a " + e.expr.kind + " but got "  + h.map(_.kind).mkString(",") + ":\n  " + h.map(e => e.prettyString + ": " + e.kind).mkString("\n  "))
        case (ListExpressionArtifact(h), ListExpressionArtifact(e)) =>
          require(e.map(_.kind).toSet.nonEmpty)
          if (e.map(_.kind).toSet.size > 1) {
            if (e.zip(h).forall({ case (ee, he) => ee.kind == he.kind })) Right("Expected " + e.map(_.kind).mkString + " gut got "  + h.map(_.kind).mkString(",") + ":\n  " + h.map(e => e.prettyString + ": " + e.kind).mkString("\n  "))
          } else if (h.exists(_.kind != e.head.kind)) return Right("Expected a list of " + e.headOption.map(_.kind).getOrElse("<unknown>") + " but got " + h.map(_.kind).mkString(",") + ":\n  " + h.map(e => e.prettyString + ": " + e.kind).mkString("\n  "))
        case (h, e) =>
          if (!e.getClass.isAssignableFrom(h.getClass)) return Right("Expected a " + e.hintString + " but got " + h.longHintString)
      }
      have.checkShape(args.get("shape")) match {
        case Some(e) => return Right(e)
        case None => // shape check passed
      }
      mode.getOrElse(Modes.SYN_EQ) match {
        case Modes.SYN_EQ => (have, expected) match {
          case (h: ExpressionArtifact, e: ExpressionArtifact) => run(() => syntacticEquality(h.expr, e.expr))
          case (TexExpressionArtifact(h), TexExpressionArtifact(e)) => run(() => syntacticEquality(h, e))
          case (SequentArtifact(h), SequentArtifact(e)) => run(() => syntacticEquality(h, e))
          case _ => Right("Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " + have.longHintString)
        }
        case Modes.VALUE_EQ =>(have, expected) match {
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (ht: Term, et: Term) => run(() => valueEquality(ht, et))
              case _ => Right("Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " + have.longHintString)
            }
          case (TexExpressionArtifact(h: Term), TexExpressionArtifact(e: Term)) => run(() => valueEquality(h, e))
          case (ListExpressionArtifact(h: List[Term]), ListExpressionArtifact(e: List[Term])) => Try(Left(valueEquality(h, e))).getOrElse(
            Right(if (h.size < e.size) "Too few values"
                  else if (h.size > e.size) "Too many values"
                  else "Incorrect answer"))
          case _ => Right("Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " + have.longHintString)
        }
        case Modes.POLY_EQ => (have, expected) match {
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (ht: Term, et: Term) => run(() => polynomialEquality(ht, et))
              case (hf: Formula, ef: Formula) => run(() => polynomialEquality(hf, ef, normalize=false))
              case _ => Right("Answer must be a KeYmaera X term, list of terms, or simple list/interval notation, but got " + have.longHintString)
            }
          case (TexExpressionArtifact(h: Term), TexExpressionArtifact(e: Term)) => run(() => polynomialEquality(h, e))
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (hf: Formula, ef: Formula) => run(() => polynomialEquality(hf, ef, args.getOrElse("normalize", "false").toBoolean))
              case _ => Right("Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " + have.longHintString)
            }
          case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) => run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
          case (SequentArtifact(h::Nil), SequentArtifact(e::Nil)) => run(() => polynomialEquality(h, e, args.getOrElse("normalize", "false").toBoolean))
          case _ => Right("Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " + have.longHintString)
        }
        case Modes.QE => (have, expected) match {
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (hf: Formula, ef: Formula) =>
                args.get("op") match {
                  case None | Some("<->") => run(() => qe(hf, ef, Equiv))
                  case Some("->") => run(() => qe(hf, ef, Imply))
                  case Some("<-") => run(() => qe(ef, hf, Imply))
                }
              case _ => Right("Answer must be a KeYmaera X expression, but got " + have.longHintString)
            }
          case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) =>
            args.get("op") match {
              case None | Some("<->") => run(() => qe(h, e, Equiv))
              case Some("->") => run(() => qe(h, e, Imply))
              case Some("<-") => run(() => qe(e, h, Imply))
            }
          case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
        }
        case Modes.PROP => (have, expected) match {
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (hf: Formula, ef: Formula) => run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hf, ef))), prop))
              case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
            }
          case (TexExpressionArtifact(h: Formula), TexExpressionArtifact(e: Formula)) =>
            run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(h, e))), prop))
          case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
        }
        case Modes.DI_PREMISE =>
          val diffAssignsMandatory = args.getOrElse("diffAssignsMandatory", "true").toBoolean
          val normalize = args.getOrElse("normalize", "false").toBoolean
          (have, expected) match {
            case (h: ExpressionArtifact, e: ExpressionArtifact) =>
              (h.expr, e.expr) match {
                case (hf: Formula, ef: Formula) => run(() => dIPremiseCheck(hf, ef, diffAssignsMandatory, normalize))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }

            case (SequentArtifact(h :: Nil), SequentArtifact(e :: Nil)) => run(() => dIPremiseCheck(h, e, diffAssignsMandatory, normalize))
            case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
          }
        case Modes.DI =>
          args.get("question") match {
            case Some(q) =>
              KeYmaeraXParser.programParser(q) match {
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
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (hp: Program, ep: Program) => run(() => prgEquivalence(ep, hp))
              case _ => Right("Answer must be a KeYmaera X program, but got " + have.longHintString)
            }
          case _ => Right("Answer must be a KeYmaera X program, but got " + have.longHintString)
        }
        case Modes.CONTRACT_EQUIV => (have, expected) match {
          case (h: ExpressionArtifact, e: ExpressionArtifact) =>
            (h.expr, e.expr) match {
              case (hf: Formula, ef: Formula) => run(() => contractEquivalence(hf, ef))
              case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
            }
          case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
        }
        case Modes.MIN_PARENS => (have, expected) match {
          case (h@ExpressionArtifact(hs), e@ExpressionArtifact(es)) =>
            run(() => syntacticEquality(h.expr, e.expr)) match {
              case Left(p) =>
                if (hs.count(_ == '(') + hs.count(_ == '{') <= es.count(_ == '(') + es.count(_ == '{')) Left(p)
                else Right("Not minimal number of parentheses and braces")
              case r => r
            }
        }
        case Modes.LOOP =>
          val invArg = args.get("inv").map(KeYmaeraXParser.formulaParser)
          args.get("question") match {
            case Some(q) =>
              have match {
                case h: ExpressionArtifact => h.expr match {
                  case hf: Formula =>
                    var inv: Option[Formula] = None
                    KeYmaeraXParser.setAnnotationListener({ case (_: Loop, f) => inv = Some(f) case _ => })
                    val m = expand(q, hf :: Nil, KeYmaeraXParser.formulaParser)
                    run(() => loopCheck(m, invArg.getOrElse(inv.getOrElse(hf))))
                  case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
                }
                case ListExpressionArtifact(h) =>
                  var inv: Option[Formula] = None
                  KeYmaeraXParser.setAnnotationListener({ case (_: Loop, f) => inv = Some(f) case _ => })
                  val m = expand(q, h, KeYmaeraXParser.formulaParser)
                  run(() => loopCheck(m, invArg.getOrElse(inv.getOrElse(h.headOption.map(_.asInstanceOf[Formula]).getOrElse(False)))))
                case _ => Right("Answer must be a KeYmaera X formula, but got " + have.longHintString)
              }
            case _ => throw new IllegalArgumentException("Missing argument 'question' in check 'loop'")
          }
        case Modes.EXPLANATION_CHECK =>
          (have, expected) match {
            case (TextArtifact(Some(hs)), TextArtifact(Some(es))) =>
              val trim = """(?:\s|~)*(.*)(?:\s*|~)*""".r("text")
              val hsTrimmed = trim.findFirstMatchIn(hs).map(_.group("text")).getOrElse("")
              val esTrimmed = trim.findFirstMatchIn(es).map(_.group("text")).getOrElse("")
              run(() => bigdecimalQE(GreaterEqual(Number(hsTrimmed.length), Divide(Number(esTrimmed.length), Number(2)))))
            case (TextArtifact(None), _) => Right("Missing answer")
            case _ => Right("Answer must be an explanation, but got " + have.longHintString)
          }
        case Modes.BELLE_PROOF =>
          args.get("question") match {
            case Some(q) =>
              have match {
                case h: ExpressionArtifact =>
                  run(() => {
                    val m = expand(q, h.expr :: Nil, KeYmaeraXParser).asInstanceOf[Formula]
                    val t = expand(args("tactic"), h.expr :: Nil, BelleParser)
                    prove(Sequent(IndexedSeq(), IndexedSeq(m)), t)
                  })
                case ListExpressionArtifact(hs) =>
                  run(() => {
                    val m = expand(q, hs, KeYmaeraXParser).asInstanceOf[Formula]
                    val t = expand(args("tactic"), hs, BelleParser)
                    prove(Sequent(IndexedSeq(), IndexedSeq(m)), t)
                  })
                case _ => Right("Answer must a a KeYmaera X expression or list of expressions, but got " + have.longHintString)
              }
            case None =>
              val t = BelleParser(args("tactic"))
              (have, expected) match {
                case (h: ExpressionArtifact, e: ExpressionArtifact) =>
                  (h.expr, e.expr) match {
                    case (hf: Formula, ef: Formula) => run(() => prove(Sequent(IndexedSeq(), IndexedSeq(Equiv(hf, ef))), t))
                    case _ => Right("Answer must be a KeYmaera X expression, sequent, or simple list/interval notation, but got " + have.longHintString)
                  }
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
                case _ => Right("Answer must a KeYmaera X formula or sequent, but got " + have.longHintString)
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

        val ARG_PLACEHOLDER_GROUP = "argPlaceholder"
        val ARG_INDEX = (Regex.quote(QuizExtractor.AskQuestion.ARG_PLACEHOLDER) + """(-?\d+)""").r(ARG_PLACEHOLDER_GROUP)
        val argIdxs = args.values.flatMap(v => { ARG_INDEX.findAllMatchIn(v).map(_.group(ARG_PLACEHOLDER_GROUP).toInt).toList }).toList.sorted
        val newArgIdxs = argIdxs.map(i => (i, if (i<0) i+earlier.keys.size+1 else i+earlier.keys.size))
        val mergedArgs = args.map({ case (k, v) =>
          val rewrittenBackRefs = newArgIdxs.foldRight(v)({ case ((i, j), mv) => mv.replaceAllLiterally(QuizExtractor.AskQuestion.ARG_PLACEHOLDER + i, QuizExtractor.AskQuestion.ARG_PLACEHOLDER + j) })
          (k, rewrittenBackRefs)
        })

        AskGrader(mode, mergedArgs, mergedExpected)
    }

    override val expected: Artifact = grader.expected
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      //@note assumed sorted from earliest to main artifact
      case MultiArtifact(as) =>
        grader.mode match {
          case Some(AskGrader.Modes.EXPLANATION_CHECK) =>
            val mainArtifact = as.last
            grader.args.get("ifCorrect") match {
              case Some(_) =>
                val prereqAnsweredCorrectly = earlier.zip(as.dropRight(1)).forall({ case ((_, g), a) => g.check(a) match {
                  case Left(p) => p.isProved
                  case _ => false
                }})
                if (prereqAnsweredCorrectly) grader.check(mainArtifact)
                else Right("Ignored explanation for a wrong answer")
              case None => grader.check(mainArtifact)
            }
          case _ =>
            val mergedHave = as.reduceRight[Artifact]({
              case (a: ExpressionArtifact, b: ExpressionArtifact) => ListExpressionArtifact(a.expr :: b.expr :: Nil)
              case (a: ExpressionArtifact, ListExpressionArtifact(all)) => ListExpressionArtifact(all :+ a.expr)
              case (TextArtifact(None), _) => return Right("Missing answer for prerequisite question")
              case (_, TextArtifact(None)) => return Right("Missing answer")
            })
            grader.check(mergedHave)
        }
    }
  }

  case class OneChoiceGrader(args: Map[String, String], expected: ChoiceArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case ChoiceArtifact(Nil) => Right("Missing answer")
      case ChoiceArtifact(h) =>
        //@note correct if answering with any of the correctly marked solutions
        if (h.toSet.subsetOf(expected.selected.toSet)) run(() => KeYmaeraXProofChecker(1000)(closeT)(Sequent(IndexedSeq.empty, IndexedSeq(True))))
        else Right("Incorrect answer")
    }
  }
  case class AnyChoiceGrader(args: Map[String, String], expected: ChoiceArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case ChoiceArtifact(Nil) => Right("Missing answer")
      case ChoiceArtifact(h) =>
        //@note correct if answering with exactly the correct yes/no pattern (modulo order)
        if (h.toSet == expected.selected.toSet) run(() => KeYmaeraXProofChecker(1000)(closeT)(Sequent(IndexedSeq.empty, IndexedSeq(True))))
        else Right("Incorrect answer")
    }
  }

  case class AskTFGrader(expected: BoolArtifact) extends Grader {
    override def check(have: Artifact): Either[ProvableSig, String] = have match {
      case BoolArtifact(None) => Right("Missing answer")
      case BoolArtifact(Some(h)) =>
        val ef = if (expected.value.get) True else False
        val hf = if (h) True else False
        run(() => KeYmaeraXProofChecker(1000)(useAt(Ax.equivReflexive)(1))(Sequent(IndexedSeq.empty, IndexedSeq(Equiv(hf, ef)))))
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
  def valueEquality(a: Term, b: Term): ProvableSig = bigdecimalQE(Equal(a, b))

  /** Compares terms in lists `a` and `b` pairwise for the same real value. */
  def valueEquality(a: List[Term], b: List[Term]): ProvableSig = {
    require(a.nonEmpty && a.length == b.length, "Same-length non-empty lists expected, but got " + a.mkString(",") + " vs. " + b.mkString(","))
    bigdecimalQE(a.zip(b).map({ case (a, b) => Equal(a, b) }).reduceRight(And))
  }

  /** Invokes the BigDecimalQETool but returns an open proof if statement `fml` is false. */
  private def bigdecimalQE(fml: Formula): ProvableSig = {
    val p = ProvableSig.proveArithmetic(BigDecimalQETool, fml)
    p.conclusion match {
      case Sequent(IndexedSeq(), IndexedSeq(Equiv(f, True))) if fml == f => p
      case _ => ProvableSig.startProof(False)
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
      //@todo extend PolynomialArithV2.equate
      val funca = extractFunctions(expa).
        map({ case FuncOf(fn@Function(name, idx, _, _, _), args) =>
          (fn, StaticSemantics.freeVars(args).toSet) -> (BaseVariable(name + nameOf(args) + "_", idx), args) }).toMap
      val funcb = extractFunctions(expb).
        map({ case FuncOf(fn@Function(name, idx, _, _, _), args) =>
          (fn, StaticSemantics.freeVars(args).toSet) -> (BaseVariable(name + nameOf(args) + "_", idx), args) }).toMap
      require(funca.keys == funcb.keys, "Expected all function symbols to match, but found non-matching symbols " + funca.keys.mkString(",") + " vs. " + funcb.keys.mkString(","))
      val matchedArgs = funca.map({ case (fn, (_, a)) => (a, funcb(fn)._2) })
      require(matchedArgs.forall({ case (arga, argb) => polynomialEquality(arga, argb).isProved }),
        "Expected uninterpreted function arguments to be equal, but not all are.")
      val encodeda = encodeFunctions(expa, funca.map({ case (fn, (v, _)) => fn -> v }))
      val encodedb = encodeFunctions(expb, funcb.map({ case (fn, (v, _)) => fn -> v }))
      KeYmaeraXProofChecker(5000)(PolynomialArithV2.equate(1))(Sequent(IndexedSeq.empty, IndexedSeq(Equal(encodeda, encodedb))))
  }

  private def nameOf(t: Term): String = StaticSemantics.freeVars(t).toSet[Variable].map(_.prettyString.replaceAllLiterally("_", "$u$")).mkString("")

  /** Extracts all function subterms of term `t`. */
  private def extractFunctions(t: Term): List[Term] = {
    val fns = ListBuffer.empty[Term]
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(_, Nothing) => Left(None)
        case fn: FuncOf =>
          fns.append(fn)
          Left(None)
        case _ => Left(None)
      }
    }, t)
    fns.toList
  }

  private def encodeFunctions(t: Term, encoding: Map[(NamedSymbol, Set[Variable]), Term]): Term = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(fn, args) => encoding.get((fn, StaticSemantics.freeVars(args).toSet)) match {
          case Some(e) => Right(e)
          case _ => Left(None)
        }
        case _ => Left(None)
      }
    }, t).get
  }

  /** Encodes `x^y` and `x/y` for non-constant polynomial exponent as pow(x,y) and div(x,y). */
  private def encodeNonConstPolynomials(t: Term): Term = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case Power(base, exp) =>
          if (StaticSemantics.freeVars(exp).isEmpty) Left(None)
          else Right(FuncOf(
            Function("pow", None, Tuple(Real, Real), Real, interpreted=false),
            Pair(encodeNonConstPolynomials(base), encodeNonConstPolynomials(exp))))
        case Divide(a, b) =>
          if (StaticSemantics.freeVars(b).isEmpty) Left(None)
          else Right(FuncOf(
            Function("div", None, Tuple(Real, Real), Real, interpreted=false),
            Pair(encodeNonConstPolynomials(a), encodeNonConstPolynomials(b))))
        case _ => Left(None)
      }
    }, t).get
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
    case (ap: Program, bp: Program) => KeYmaeraXProofChecker(1000)(useAt(Ax.equivReflexive)(1))(Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(ap, True), Box(bp, True)))))
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

  /** Checks that formula `h` is equivalent differential invariant to formula `e`, i.e. (e<->h) & (e' -> h')  */
  def dIReductionCheck(h: Formula, e: Formula): ProvableSig = {
    val abbreviatePrimes = TacticFactory.anon { s: Sequent =>
      StaticSemantics.freeVars(s).toSet.filter(_.isInstanceOf[DifferentialSymbol]).
        map(abbrvAll(_, None)).reduceRightOption[BelleExpr](_&_).getOrElse(skip) & SaturateTactic(hideL('L))
    }
    KeYmaeraXProofChecker(5000)(chase(1, PosInExpr(1::0::Nil)) & chase(1, PosInExpr(1::1::Nil)) & abbreviatePrimes &
      SimplifierV3.fullSimplify & prop & OnAll(QE & done))(
      Sequent(IndexedSeq(), IndexedSeq(And(Equiv(e, h), Imply(DifferentialFormula(e), DifferentialFormula(h)))))
    )
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

  def contractEquivalence(have: Formula, expected: Formula): ProvableSig = {
    val rephrasePost = TacticFactory.anon { s: Sequent =>
      val anteBoxes = s.ante.filter(_.isInstanceOf[Box])
      val succBoxes = s.succ.zipWithIndex.filter(_._1.isInstanceOf[Box])
      val boxes = (anteBoxes ++ succBoxes.map(_._1)).groupBy({ case Box(prg, _) => prg })
      val postEquivs = boxes.map({ case (k, v) => k -> v.map({ case Box(_, f) => f }).toSet.subsets(2).toList.map(s => Equiv(s.head, s.tail.head)) })
      val postEquivLemmas = postEquivs.map({ case (k, v) => k -> v.map(e => e -> Lemma(proveBy(e, prop), Nil)) }).filter(_._2.forall(_._2.fact.isProved))
      succBoxes.flatMap({ case (Box(prg, fml), i) => postEquivLemmas.getOrElse(prg, List.empty).
        find({ case (Equiv(l, r), _) => l==fml || r==fml }).
        map({ case (Equiv(l, _), pr) => DebuggingTactics.print("Using lemma") & useAt(pr, if (l == fml) PosInExpr(0::Nil) else PosInExpr(1::Nil))(Position(SuccPos(i)) ++ PosInExpr(1::Nil)) & DebuggingTactics.print("Used") }) }).
        reduceRightOption[BelleExpr](_&_).getOrElse(skip)
    }
    KeYmaeraXProofChecker(5000)(DebuggingTactics.print("Start") & chase(1) & prop & OnAll(rephrasePost & prop) &
      DebuggingTactics.done("Incorrect answer"))(Sequent(IndexedSeq(), IndexedSeq(Equiv(elaborateToSystems(expected), elaborateToSystems(have)))))
  }

  /** Generic assessment prover uses tactic `t` to prove sequent `s`, aborting after `timeout` time. */
  def prove(s: Sequent, t: BelleExpr): ProvableSig = {
    KeYmaeraXProofChecker(5000)(t)(s)
  }

  /** Grades a submission.
    *
    * @param options The prover options:
    *                - 'in (mandatory) identifies the file to grade
    *                - 'res (optional) result file
    *                - 'msg (optional) message file
    */
  def grade(options: OptionMap, usage: String): Unit = {
    val inputFileName = options('in).toString
    val resultFileName = options.getOrElse('res, inputFileName + ".res.json").toString
    val msgFileName = options.getOrElse('msg, inputFileName + ".log").toString
    val resultOut = new BufferedOutputStream(new FileOutputStream(resultFileName))
    val msgOut = new BufferedOutputStream(new FileOutputStream(msgFileName))
    try {
      grade(options, msgOut, resultOut, usage)
    } catch {
      case ex: Throwable =>
        msgOut.flush()
        val writer = new PrintWriter(msgOut)
        ex.printStackTrace(writer)
        writer.flush()
        writer.close()
    } finally {
      msgOut.flush()
      msgOut.close()
      resultOut.flush()
      resultOut.close()
    }
  }

  /** Grades a submission.
    *
    * @param options The prover options:
    *                - 'in (mandatory) identifies the file to grade
    */
  def grade(options: OptionMap, msgOut: OutputStream, resultOut: OutputStream, usage: String): Unit = {
    require(options.contains('in), usage)

    val inputFileName = options('in).toString
    val src = Source.fromFile(inputFileName, "UTF-8")
    val input = try { src.mkString.parseJson } finally { src.close() }
    val chapter = {
      import Submission.SubmissionJsonFormat._
      input.convertTo[Submission.Chapter]
    }

    val parsedProblems = chapter.problems.map({ case problem@Submission.Problem(_, _, _, prompts) =>
      val parsedAnswers = prompts.map(p => try {
          Left(p -> toAnswerArtifact(p))
        } catch {
          case ex: Throwable => Right(p -> ex)
        }
      )
      (problem, parsedAnswers.partition(_.isLeft) match {
        case (as, pe) => (as.map(_.left.get), pe.map(_.right.get))
      })
    })

    val msgStream = new PrintStream(msgOut, true)
    if (parsedProblems.exists(_._2._2.nonEmpty)) {
      // report parse errors
      reportParseErrors(parsedProblems, msgStream)
      val allGrades = parsedProblems.flatMap({ case (_, (prompts, _)) => prompts.map({ case (p, _) => p -> 0.0 }) })
      printJSONGrades(allGrades, resultOut)
    } else {
      val allGrades: List[(Submission.Prompt, Double)] = parsedProblems.flatMap({ case (p, (prompts, _)) =>
        msgStream.println("Grading section " + p.title)

        val ARG_PLACEHOLDER_GROUP = "argPlaceholder"
        val NEG_HASH = (Regex.quote(QuizExtractor.AskQuestion.ARG_PLACEHOLDER) + """(-\d+)""").r(ARG_PLACEHOLDER_GROUP)
        val mergedPrompts = prompts.zipWithIndex.map({
          case ((p@Submission.SinglePrompt(_, _, _, Submission.TextAnswer(_, _, _, Some(Submission.GraderCookie(_, _, method)), _, _) :: Nil), answer), i) =>
            val backRefs = NEG_HASH.findAllMatchIn(method).map(_.group(ARG_PLACEHOLDER_GROUP).toInt).toList
            if (backRefs.nonEmpty) {
              val mergedPrompt = Submission.MultiPrompt(p, backRefs.map(j => (j, prompts(i + j)._1)).toMap)
              val answers = answer.map(a => MultiArtifact(backRefs.flatMap(j => prompts(i + j)._2) :+ a))
              (mergedPrompt, answers)
            }else (p, answer)
          case (q, _) => q
        })

        val graders = mergedPrompts.map({ case (prompt, answerArtifact) => (prompt, (toGrader(prompt), answerArtifact)) })
        val grades = graders.map({ case (prompt, (grader, answerArtifact)) =>
          msgStream.print("Grading question " + prompt.id + "...")
          answerArtifact match {
            case Some(a) => grader.check(a) match {
              case Left(p) =>
                if (p.isProved) {
                  msgStream.println("PASSED")
                  (prompt, prompt.points)
                } else {
                  msgStream.println("FAILED:Incorrect answer")
                  (prompt, 0.0)
                }
              case Right(hint) =>
                msgStream.print("FAILED:")
                msgStream.println(hint)
                (prompt, 0.0)
            }
            case None =>
              msgStream.println("FAILED:Missing answer")
              (prompt, 0.0)
          }
        })
        msgStream.println("Done grading section " + p.title)
        grades
      })
      printJSONGrades(allGrades, resultOut)
    }
  }

  /** Translates a submission prompt into a grader artifact (None if question not answered). */
  private def toAnswerArtifact[T <: Artifact](p: Submission.Prompt): Option[Artifact] = {
    p.name match {
      case "\\ask" =>
        require(p.answers.size == 1, "Expected exactly 1 answer for text prompt " + p.id + ", but got " + p.answers.size)
        p.answers.map({
          case Submission.TextAnswer(_, _, name, _, answer, expected) =>
            if (answer.trim.isEmpty) Some(TextArtifact(None))
            else name match {
              case "\\sol" =>
                if (expected.startsWith(QuizExtractor.AskQuestion.KYXLINE)) Some(QuizExtractor.AskQuestion.artifactsFromKyxString(answer))
                else if (expected.startsWith(QuizExtractor.AskQuestion.MATH_DELIM)) Some(QuizExtractor.AskQuestion.artifactsFromTexMathString(answer))
                else Some(QuizExtractor.AskQuestion.artifactsFromTexTextString(answer))
              case "\\solfin" | "\\solfinask" =>
                Some(QuizExtractor.AskQuestion.solfinArtifactsFromString(answer)._2)
            }
          case a => throw new IllegalArgumentException("Expected text answer for \\ask, but got " + a.getClass.getSimpleName)
        }).head
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
        require(p.answers.size == 1, "Expected exactly 1 answer for text prompt " + p.id + ", but got " + p.answers.size)
        p.answers.map({
          case Submission.TextAnswer(_, _, name, _, _, expected) => name match {
            case "\\sol" => (QuizExtractor.AskQuestion.artifactFromSolContent(expected), Map.empty[String, String])
            case "\\solfin" | "\\solfinask" =>
              val (question, artifact) = QuizExtractor.AskQuestion.solfinArtifactsFromLstList(expected)
              (Some(artifact), Map("question" -> question))
          }
          case a => throw new IllegalArgumentException("Expected text answer for \\ask, but got " + a.getClass.getSimpleName)
        }).head
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

  private def toGrader(p: Submission.Prompt): Grader = p match {
    case mp@Submission.MultiPrompt(main, earlier) =>
      require(mp.name == "\\ask", "Expected text multiprompt") //@note other questions do not have \algog
      require(mp.answers.size == 1, "Expected exactly 1 answer for text prompt " + mp.id + ", but got " + mp.answers.size)
      val mainGrader = toGrader(main)
      val earlierGraders = earlier.map({ case (k, v) => (k, toGrader(v)) }).toList.sortBy(_._1)
      MultiAskGrader(mainGrader, earlierGraders.toMap)
    case _: Submission.SinglePrompt => p.name match {
      case "\\ask" =>
        require(p.answers.size == 1, "Expected exactly 1 answer for text prompt " + p.id + ", but got " + p.answers.size)
        p.answers.map({
          case Submission.TextAnswer(_, _, _, grader, _, _) =>
            grader.map(g => QuizExtractor.AskQuestion.graderInfoFromString(g.method)) match {
              case Some((g, args)) =>
                toExpectedArtifact(p) match {
                  case (Some(expected), a) => AskGrader(Some(g), args ++ a, expected)
                  case (None, _) => throw new IllegalArgumentException("Missing expected solution for \\ask prompt " + p.id)
                }
              case None => throw new IllegalArgumentException("Missing grader information for \\ask prompt " + p.id)
            }
        }).head
      case "\\onechoice" =>
        toExpectedArtifact(p) match {
          case (Some(expected: ChoiceArtifact), _) => OneChoiceGrader(Map.empty, expected)
          case (None, _) => throw new IllegalArgumentException("Missing expected solution for \\onechoice prompt " + p.id)
        }
      case "\\anychoice" =>
        toExpectedArtifact(p) match {
          case (Some(expected: ChoiceArtifact), _) => AnyChoiceGrader(Map.empty, expected)
          case (None, _) => throw new IllegalArgumentException("Missing expected solution for \\anychoice prompt " + p.id)
        }
      case "\\asktf" =>
        toExpectedArtifact(p) match {
          case (Some(expected: BoolArtifact), _) => AskTFGrader(expected)
          case (None, _) => throw new IllegalArgumentException("Missing expected solution for \\asktf prompt " + p.id)
        }
    }
    case _ => throw new IllegalArgumentException("Unexpected prompt type " + p.getClass.getSimpleName)
  }

  private def reportParseErrors(parsedProblems: List[(Submission.Problem, (List[(Submission.Prompt, Option[Artifact])],
                                                                           List[(Submission.Prompt, Throwable)]))],
                                msgStream: PrintStream): Unit = {
    parsedProblems.foreach({ case (problem, (prompts, errors)) =>
      msgStream.print("Parsing problem '" + problem.title + "':")
      if (errors.nonEmpty) {
        msgStream.println("FAILED")
        val skipped = prompts.filter({ case (p, _) => !errors.exists(p == _._1) }).map({ case (p, _) => (p, "Grading question " + p.id + "...SKIPPED") })
        val failed = errors.map({
          case (prompt, ex: ParseException) => (prompt, "Grading question " + prompt.id + "...SKIPPED\n" + prompt.answers.map(a => "Question label '" + a.label + "'").mkString(",") + "\n" + ex.toString + "\n----------")
          case (prompt, ex) => (prompt, "Grading question " + prompt.id + "...SKIPPED\n" + prompt.answers.map(a => "Question label '" + a.label + "'").mkString(",") + "\n" + ex.getMessage + "\n----------")
        })
        msgStream.println((skipped ++ failed).sortBy({ case (p, _) => p.id }).map(_._2).mkString("\n"))
      } else {
        msgStream.println("PASSED")
        msgStream.println(prompts.map({ case (p, _) =>
          "Grading question " + p.id + "...SKIPPED"
        }).mkString("\n"))
      }
    })
  }

  private def printJSONGrades(grades: List[(Submission.Prompt, Double)], out: OutputStream): Unit = {
    val jsonGrades = JsObject("scores" -> JsObject(grades.map({ case (p, s) => p.id.toString -> JsNumber(s) }).toMap))
    out.write(jsonGrades.compactPrint.getBytes("UTF-8"))
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

  private val REPTAC_GROUP = "reptac"
  private val TACTIC_REPETITION_EXTRACTOR = ("for " + Regex.quote(QuizExtractor.AskQuestion.ARG_PLACEHOLDER) + "i do(.*)endfor").r(REPTAC_GROUP)

  /** Expands occurrences of \%i in string `s` with arguments from argument list `args`. */
  @tailrec
  private def expand[T](s: String, args: List[Expression], parser: String=>T): T = {
    val repTacs = TACTIC_REPETITION_EXTRACTOR.findAllMatchIn(s).toList
    if (repTacs.nonEmpty) {
      val unfolded = repTacs.map(_.group(REPTAC_GROUP)).map(t => {
        t -> (1 to args.size).map(i => t.replaceAllLiterally(QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "i", s"${QuizExtractor.AskQuestion.ARG_PLACEHOLDER}$i")).mkString(";")
      })
      val replaced = unfolded.foldRight(s)({ case ((what, repl), s) => s.replaceAllLiterally(s"for ${QuizExtractor.AskQuestion.ARG_PLACEHOLDER}i do${what}endfor", repl) })
      assert(!replaced.contains(QuizExtractor.AskQuestion.ARG_PLACEHOLDER + "i"), "Expected to have replaced all variable-length argument repetitions")
      expand(replaced, args, parser)
    } else {
      val ts = (1 to args.size).foldRight(s)({ case (i, s) => s.replaceAllLiterally(s"${QuizExtractor.AskQuestion.ARG_PLACEHOLDER}$i", args(i-1).prettyString) })
      require(!ts.contains(QuizExtractor.AskQuestion.ARG_PLACEHOLDER), "Not enough arguments provided for tactic")
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

  /** Elaborates program constants to system constants. */
  private def elaborateToSystems(f: Formula): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        Right(elaborateToSystem(e))
      }
    }, f).get
  }

}
