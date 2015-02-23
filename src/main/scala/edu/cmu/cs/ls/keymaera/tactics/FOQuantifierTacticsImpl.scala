package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import TacticLibrary.alphaRenamingT
import PropositionalTacticsImpl.uniformSubstT
import AxiomTactic.axiomT

import scala.collection.immutable.List
import scala.collection.immutable.Seq

/**
 * Implementation of first order quantifier tactics.
 */
object FOQuantifierTacticsImpl {

  def instantiateT: PositionTactic = new PositionTactic("Quantifier Instantiation") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case Forall(_, _) => true
      case _ => false
    })

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos) match {
        case Forall(vars, phi) =>
          Some(vars.filter(_.isInstanceOf[Variable]).
            map(v => instantiateT(v.asInstanceOf[Variable], v.asInstanceOf[Variable])(pos)).
            fold(NilT)((a, b) => a & b))
        case _ => None
      }
    }
  }

  /**
   * Creates a tactic which does quantifier instantiation.
   * @param quantified The quantified variable.
   * @param instance The instance.
   * @return The tactic.
   */
  def instantiateT(quantified: Variable, instance: Term): PositionTactic = new PositionTactic("Quantifier Instantiation") {
    val axiomName = "all instantiate"
    val axiom = Axiom.axioms.get(axiomName)
    require(axiom.isDefined)

    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case Forall(vars, _) => vars.contains(quantified)
      case _ => false
    })

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      def replace(f: Formula)(o: NamedSymbol, n: Term): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Forall(v, fa) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), fa))
          case Exists(v, fa) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), fa))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
      }, f) match {
        case Some(g) => g
        case None => throw new IllegalStateException("Replacing one variable by another should not fail")
      }

      def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution, (Variable, Variable), (Term, Term))] = f match {
        case Forall(x, qf) if x.contains(quantified) =>
          def forall(h: Formula) = if (x.length > 1) Forall(x.filter(_ != quantified), h) else h
          // construct substitution
          val aX = Variable("x", None, Real)
          val aT = Apply(Function("t", None, Unit, Real), Nothing)
          val aP = Function("p", None, Real, Bool)
          val l = List(SubstitutionPair(aT, instance), SubstitutionPair(ApplyPredicate(aP, CDot),
            forall(replace(qf)(quantified, CDot))))
          // construct axiom instance: \forall x. p(x) -> p(t)
          val g = replace(qf)(quantified, instance)
          val axiomInstance = Imply(f, forall(g))
          Some(axiomInstance, Substitution(l), (quantified, aX), (instance, aT))
        case Forall(x, qf) if !x.contains(quantified) => None
        case _ => None
      }

      def decompose(d: Formula): Formula = d match {
        case Forall(v, f) if v.length > 1 => Forall(v.take(1), Forall(v.drop(1), f))
        case Exists(v, f) if v.length > 1 => Exists(v.take(1), Exists(v.drop(1), f))
        case _ => d
      }

      // since we have an implication, we use modus ponens to get it's consequence
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiom match {
          case Some(a) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos)) match {
              case Some((axiomInstance, subst, (quant, aX), (inst, aT))) =>
                val eqPos = AntePosition(node.sequent.ante.length)
                val branch1Tactic = modusPonensT(pos, eqPos)
                // val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                // val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                // val hideSllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
                def alpha(p: Position, q: Variable) = alphaRenamingT(q.name, q.index, "$" + aX.name, aX.index)(p)
                def repl(f: Formula, v: Variable, atTrans: Boolean = true):Formula = f match {
                  case Imply (aa, b) =>
                    val aTName = aT match { case x: Variable => x case Apply(fn, _) => fn }
                    Imply(decompose(replace (aa)(v, Variable ("$" + aX.name, aX.index, aX.sort) )),
                    if(atTrans) replace(b)(aTName, inst) else b)
                  case _ => throw new IllegalArgumentException("...")
                }
                val replMap = Map(repl(axiomInstance, quant, atTrans = false) -> repl(a, aX))
                val branch2Tactic = cohideT(SuccPosition(node.sequent.succ.length)) ~
                  alpha(SuccPosition(0, HereP.first), quant) ~
                  decomposeQuanT(SuccPosition(0, HereP.first)) ~
                  (uniformSubstT(subst, replMap) &
                    (axiomT(axiomName) & alpha(AntePosition(0, HereP.first), aX) & AxiomCloseT))
                Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
              case None => println("Giving up " + this.name); None
            }
          case None => println("Giving up because the axiom does not exist " + this.name); None
        }

    }
  }

  /**
   * Tactic for existential quantifier generalization.
   * @param x The new existentially quantified variable.
   * @param t The term to generalize.
   * @return The tactic.
   */
  def existentialGenT(x: Variable, t: Term) = new AxiomTactic("exists generalize", "exists generalize") {
    override def applies(f: Formula): Boolean = !Helper.names(f).contains(x)

    override def constructInstanceAndSubst(f: Formula, axiom: Formula):
        Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      import AlphaConversionHelper.replaceFree
      require(!Helper.names(f).contains(x))

      // construct substitution
      val aX = Variable("x", None, Real)
      val aT = Variable("t", None, Real)
      val aP = ApplyPredicate(Function("p", None, Real, Bool), t)
      val l = List(SubstitutionPair(aT, t), SubstitutionPair(aP, f))

      // construct axiom instance: p(t) -> \exists x. p(x)
      val g = Exists(x :: Nil, replaceFree(f)(t, x))
      val axiomInstance = Imply(f, g)

      // rename to match axiom if necessary
      val alpha = new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Imply(_, Exists(_, _)) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(x.name, x.index, aX.name, aX.index)(p.second))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
      val Imply(left, right) = axiom
      val (ax, cont) = (Imply(left, replaceFree(right)(aX, x)), Some(alpha))

      Some(ax, axiomInstance, Substitution(l), None, cont)
    }
  }

  /**
   * Base class for vacuous quantifier elimination/introduction tactics.
   * @param x The new quantified variable. If None, the tactic eliminates a vacuous quantifier.
   * @param axiomName The name of the axiom.
   * @param quantFactory Creates the quantifier.
   */
  class VacuousQuantificationTactic(x: Option[Variable], axiomName: String,
                                            quantFactory: (Seq[NamedSymbol], Formula) => Quantifier)
      extends AxiomTactic(axiomName, axiomName) {
    override def applies(f: Formula): Boolean = x match {
      case Some(v) => !Helper.names(f).contains(v)
      case None => f match {
        case q: Quantifier => q.variables.size == 1 && Helper.names(q.child.asInstanceOf[Formula]).
          intersect(q.variables.toSet).isEmpty
        case _ => false
      }
    }

    private def constructSubstAndAlphaRename(axiom: Formula, f: Formula, axiomInstance: Formula, v: Variable) = {
      // construct substitution
      val aP = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
      val l = List(SubstitutionPair(aP, f))

      // rename to match axiom if necessary
      val aX = Variable("x", None, Real)
      val alpha = new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Equiv(_, _: Quantifier) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(v.name, v.index, aX.name, aX.index)(p.second))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
      val Equiv(left, right) = axiom
      val (ax, cont) = (Equiv(left, replaceFree(right)(aX, v)), Some(alpha))

      Some(ax, axiomInstance, Substitution(l), None, cont)
    }

    override def constructInstanceAndSubst(f: Formula, axiom: Formula):
        Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = x match {
      case Some(v) =>
        import AlphaConversionHelper.replaceFree
        require(!Helper.names(f).contains(v))
        // construct axiom instance: p <-> \exists/\forall x. p
        constructSubstAndAlphaRename(axiom, f, Equiv(f, quantFactory(v :: Nil, f)), v)
      case None => f match {
        case q: Quantifier =>
          require(q.variables.size == 1 && q.variables.head.isInstanceOf[Variable])
          val v = q.variables.head.asInstanceOf[Variable]
          // construct axiom instance: p <-> \exists/\forall x. p
          constructSubstAndAlphaRename(axiom, q.child.asInstanceOf[Formula],
            Equiv(q.child.asInstanceOf[Formula], f), v)
        case _ => None
      }
    }
  }

  def vacuousUniversalQuanT(x: Option[Variable]) = new VacuousQuantificationTactic(x,
    "vacuous all quantifier", Forall.apply)
  def vacuousExistentialQuanT(x: Option[Variable]) = new VacuousQuantificationTactic(x,
    "vacuous exists quantifier", Exists.apply)

  /**
   * Creates a tactic to decompose quantifiers.
   * @return The tactic.
   */
  def decomposeQuanT = new PositionTactic("Decompose Quantifiers") {
    override def applies(s: Sequent, pos: Position): Boolean = {
      var res = false
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if(p == pos.inExpr) Left(None) else Right(e)
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Forall(vars, f) if vars.length > 1 => res = true
            case Exists(vars, f) if vars.length > 1 => res = true
            case _ => res = false
          }
          Left(Some(new StopTraversal {}))
        }
      }
      ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), s(pos))
      res
    }

    override def apply(p: Position): Tactic = new ApplyRule(DecomposeQuantifiers(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /**
   * Creates a new tactic for skolemization.
   * @return The skolemization tactic.
   */
  def skolemizeT: PositionTactic = skolemizeT(forceUniquify = false)
  def skolemizeT(forceUniquify: Boolean): PositionTactic = new PositionTactic("Skolemize") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case Forall(_, _) => !p.isAnte
      case Exists(_, _) => p.isAnte
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Forall(vars, _) =>
          val rename =
            if (forceUniquify || Helper.namesIgnoringPosition(node.sequent, p).intersect(vars.toSet).nonEmpty) uniquify(p)
            else NilT
          Some(rename ~ new ApplyRule(new Skolemize(p)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          })
        case Exists(vars, _) =>
          val rename =
            if (forceUniquify || Helper.namesIgnoringPosition(node.sequent, p).intersect(vars.toSet).nonEmpty) uniquify(p)
            else NilT
          Some(rename ~ new ApplyRule(new Skolemize(p)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          })
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  val uniquify = new PositionTactic("Uniquify") {
    // for now only on top level
    def getBoundVariables(s: Sequent, p: Position): Option[Seq[(String, Option[Int])]] = s(p) match {
      case Forall(v, _) => Some(v.map {
        case Variable(n, i, _) => (n, i)
        case _ => ???
      })
      case Exists(v, _) => Some(v.map {
        case Variable(n, i, _) => (n, i)
        case _ => ???
      })
      case BoxModality(Assign(Variable(n, i, _), e), _) => Some(Seq((n, i)))
      case BoxModality(NDetAssign(Variable(n, i, _)), _) => Some(Seq((n, i)))
      case DiamondModality(Assign(Variable(n, i, _), e), _) => Some(Seq((n, i)))
      case DiamondModality(NDetAssign(Variable(n, i, _)), _) => Some(Seq((n, i)))
      case a => None
    }

    override def applies(s: Sequent, p: Position): Boolean = (p.inExpr == HereP) && getBoundVariables(s, p).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        getBoundVariables(node.sequent, p) match {
          case Some(s) =>
            var otherVars = Helper.namesIgnoringPosition(node.sequent, p).map((n: NamedSymbol) => (n.name, n.index)) ++ s
            val pVars = Helper.names(node.sequent(p)).map((n: NamedSymbol) => (n.name, n.index))
            val res: Seq[Option[Tactic]] = for((n, idx) <- s) yield {
              val vars = otherVars.filter(_._1 == n) ++ pVars.filter(_._1 == n)
              //require(vars.size > 0, "The variable we want to rename was not found in the sequent all together " + n + " " + node.sequent)
              // we do not have to rename if there are no name clashes
              if (vars.size > 0) {
                val maxIdx: Option[Int] = vars.map(_._2).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) => acc match {
                  case Some(a) => i match {
                    case Some(b) => if (a < b) Some(b) else Some(a)
                    case None => Some(a)
                  }
                  case None => i
                })
                val tIdx: Option[Int] = maxIdx match {
                  case None => Some(0)
                  case Some(a) => Some(a + 1)
                }
                otherVars = otherVars ++ Seq((n, tIdx))
                Some(alphaRenamingT(n, idx, n, tIdx)(p))
              } else {
                None
              }
            }
            val tactic = res.flatten.reduceRight(seqT)
            Some(tactic)
          case None => None
        }
      }
    }

  }
}
