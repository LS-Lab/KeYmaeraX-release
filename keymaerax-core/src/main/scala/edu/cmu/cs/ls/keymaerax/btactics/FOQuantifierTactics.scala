package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, ExpressionTraversal, FormulaTools, Position, PosInExpr, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._

import scala.collection.immutable
import scala.language.postfixOps


/**
 * [[FOQuantifierTactics]] provides tactics for instantiating quantifiers.
 */
object FOQuantifierTactics {
  /** Proves exists by duality from universal base tactic */
  def existsByDuality(base: DependentPositionTactic, atTopLevel: Boolean = false): DependentPositionTactic =
      new DependentPositionTactic("existsByDuality") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(provable: Provable): BelleExpr =
        useAt("exists dual", PosInExpr(1::Nil))(pos) &
          (if (atTopLevel) notL(pos) & base('Rlast) & notR('Rlast)
           else base(pos.first) & useAt("!! double negation")(pos))
    }
  }

  def allInstantiate(quantified: Option[Variable] = None, instance: Option[Term] = None): DependentPositionTactic =
    new DependentPositionTactic("all instantiate") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
          case (ctx, f@Forall(vars, qf)) if quantified.isEmpty || vars.contains(quantified.get) =>
            require((if (pos.isAnte) -1 else 1) * FormulaTools.polarityAt(ctx(f), pos.inExpr) < 0, "\\forall must have negative polarity")
            def forall(h: Formula) = if (vars.length > 1) Forall(vars.filter(_ != vToInst(vars)), h) else h
            // cut in p(t) from axiom: \forall x. p(x) -> p(t)
            val x = vToInst(vars)
            val t = inst(vars)
            val p = forall(SubstitutionHelper.replaceFree(qf)(x, t))

            val subst = USubst(
              SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), forall(SubstitutionHelper.replaceFree(qf)(x, DotTerm))) ::
              SubstitutionPair("t()".asTerm, t) :: Nil)
            val orig = Sequent(Nil, immutable.IndexedSeq(),
              immutable.IndexedSeq(s"(\\forall ${x.prettyString} p(${x.prettyString})) -> p(t())".asFormula))

            val axiomInstance = if (pos.isAnte) Imply(ctx(f), ctx(p)) else ctx(p)
            if (pos.isAnte) {
              ProofRuleTactics.cut(axiomInstance) <(
                (modusPonens(pos, AntePos(sequent.ante.length)) & hideL(pos.topLevel)) partial,
                cohide('Rlast) & CMon(pos.inExpr) & US(subst, orig) & byUS("all instantiate")
                )
            } else {
              ProofRuleTactics.cut(axiomInstance) <(
                cohide2(new AntePosition(sequent.ante.length), pos.topLevel) &
                  TactixLibrary.by(CMon(ctx)(Provable.startProof(Sequent(Nil, immutable.IndexedSeq(f), immutable.IndexedSeq(p))))) &
                  implyRi & US(subst, orig) & byUS("all instantiate"),
                hideR(pos.topLevel) partial
                )
            }
          case (_, (f@Forall(v, _))) if quantified.isDefined && !v.contains(quantified.get) =>
            throw new BelleError("Cannot instantiate: universal quantifier " + f + " does not bind " + quantified.get)
          case (_, f) =>
            throw new BelleError("Cannot instantiate: formula " + f.prettyString + " at pos " + pos + " is not a universal quantifier")
          case _ =>
            throw new BelleError("Position " + pos + " is not defined in " + sequent.prettyString)
        }
      }

      def vToInst(vars: Seq[Variable]) = if (quantified.isEmpty) vars.head else quantified.get
      def inst(vars: Seq[Variable]) = if (instance.isEmpty) vToInst(vars) else instance.get
  }

  def existsInstantiate(quantified: Option[Variable] = None, instance: Option[Term] = None): DependentPositionTactic =
    existsByDuality(allInstantiate(quantified, instance))


  /**
   * Skolemization with bound renaming on demand.
   * @example{{{
   *     |- x>0
   *     -----------------allSkolemize(1)
   *     |- \forall x x>0
   * }}}
   * @example
   *     x_0>0 |- x>0
   *     -----------------------allSkolemize(1)
   *     x>0   |- \forall x x>0
   */
  lazy val allSkolemize: DependentPositionTactic = new DependentPositionTactic("all skolemize") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc, "All skolemize only in succedent")
        val xs = sequent.sub(pos) match {
          case Some(Forall(vars, _)) => vars
          case f => throw new BelleError("All skolemize expects universal quantifier at position " + pos + ", but got " + f)
        }
        val namePairs = xs.map(x => (x, TacticHelper.freshNamedSymbol(x, sequent)))
        val renaming =
          if (namePairs.size > 1) namePairs.map(np => ProofRuleTactics.boundRenaming(np._1, np._2)).reduce[BelleExpr](_ & _)
          else {assert(namePairs.size == 1); ProofRuleTactics.boundRenaming(namePairs.head._1, namePairs.head._2)}
        val backrenaming =
          if (namePairs.size > 1) namePairs.map(np => ProofRuleTactics.uniformRenaming(np._2, np._1)).reduce[BelleExpr](_ & _)
          else {assert(namePairs.size == 1); ProofRuleTactics.uniformRenaming(namePairs.head._2, namePairs.head._1)}
        renaming & ProofRuleTactics.skolemizeR(pos) & backrenaming
      }
    }
  }

  /**
   * Skolemizes an existential quantifier in the antecedent.
   * @see [[allSkolemize]]
   */
  lazy val existsSkolemize: DependentPositionTactic = existsByDuality(allSkolemize, atTopLevel=true)

  /**
   * Generalizes existential quantifiers, but only at certain positions. All positions have to refer to the same term.
   * @example{{{
   *           \exists z z=a+b |-
   *           ------------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: Nil)(AntePosition(0))
   *                 a+b = a+b |-
   * }}}
   * @example{{{
   *           \exists z z=z |-
   *           ----------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: PosInExpr(1::Nil) :: Nil)(AntePosition(0))
   *               a+b = a+b |-
   * }}}
   * @param x The new existentially quantified variable.
   * @param where Points to the term to generalize.
   * @return The tactic.
   */
  def existsGeneralize(x: Variable, where: List[PosInExpr]): DependentPositionTactic = new DependentPositionTactic("exists generalize") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(fml: Formula) =>
          require(where.nonEmpty, "Need at least one position to generalize")
          require(where.map(w => sequent.sub(pos.navigate(w))).toSet.size == 1, "Not all positions refer to the same term")
          val fmlRepl = replaceWheres(fml, x)

          //@note create own substitution since UnificationMatch doesn't get it right yet
          val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
          val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
          val pDot = replaceWheres(fml, DotTerm)
          val subst = USubst(
            SubstitutionPair(aP, pDot) ::
            SubstitutionPair(aT, sequent.sub(pos.navigate(where.head)).get) :: Nil)
          val origin = Sequent(Nil, immutable.IndexedSeq(),
            immutable.IndexedSeq(Imply("p(t())".asFormula, Exists(x::Nil, PredOf(Function("p", None, Real, Bool), x)))))

          cut(Imply(fml, Exists(x :: Nil, fmlRepl))) <(
            /* use */ implyL('Llast) <(closeId, hide(fml)(pos) partial) partial,
            /* show */ cohide('Rlast) & ProofRuleTactics.US(subst, origin) & byUS("exists generalize")
            )
        case _ => throw new BelleError("Position " + pos + " must refer to a formula in sequent " + sequent)
      }
    }

    private def replaceWheres(fml: Formula, repl: Term) =
      ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] =
          if (where.contains(p)) Right(repl) else Left(None)
      }, fml) match {
        case Some(f) => f
        case _ => throw new IllegalArgumentException(s"Position $where is not a term")
      }
  }

  /**
   * Converse of all instantiate.
   * @param x The universally quantified variable to introduce.
   * @param t The term to generalize.
   * @return The position tactic.
   * @example{{{\forall z \forall x x^2 >= -z^2
   *            ------------------------------- universalGenT(z, f())
   *            \forall x x^2 >= -f()^2
   * }}}
   * @example{{{\forall z \forall x x^2 >= -z^2
   *            ------------------------------- universalGenT(z, y+5)
   *            \forall x x^2 >= -(y+5)^2
   * }}}
   */
  def universalGen(x: Option[Variable], t: Term): DependentPositionTactic = new DependentPositionTactic("all generalize") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isTopLevel, "all generalize only at top-level")
        val quantified: Variable = x match {
          case Some(xx) => xx
          case None => t match {
            case v: Variable => TacticHelper.freshNamedSymbol(v, sequent)
            case FuncOf(fn, _) => val fresh = TacticHelper.freshNamedSymbol(fn, sequent); Variable(fresh.name, fresh.index, fresh.sort)
            case _ => throw new IllegalStateException("Disallowed by applies")
          }
        }

        val genFml = Forall(immutable.Seq(quantified), SubstitutionHelper.replaceFree(sequent(pos))(t, quantified))
        cut(genFml) <(
          /* use */ allL(quantified, t)('Llast) & closeId,
          /* show */ hide(pos) partial
        )
      }
    }
  }

  /**
   * Computes the universal closure of the formula at the specified position. Uses the provided order of quantifiers.
   * Reverse alphabetical order for non-mentioned variables (for all variables if order == Nil).
   * @example{{{
   *           |- \forall a forall z forall x (x>0 & a=2 & z<5)
   *         ---------------------------------------------------universalClosure(Variable("a")::Nil)
   *           |- x>0 & a=2 & z<5
   * }}}
   * @example{{{
   *           |- \forall z forall x forall a (x>0 & a=2 & z<5)
   *         ---------------------------------------------------universalClosure()
   *           |- x>0 & a=2 & z<5
   * }}}
   * @param order The order of quantifiers.
   * @return The tactic.
   */
  def universalClosure(order: List[NamedSymbol] = Nil): DependentPositionTactic = new DependentPositionTactic("Universal closure") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        // fetch non-bound variables and parameterless function symbols
        require(pos.isTopLevel, "Universal closure only at top-level")
        val varsFns: Set[NamedSymbol] = StaticSemantics.freeVars(sequent(pos)).toSet ++ StaticSemantics.signature(sequent(pos))
        require(order.toSet.subsetOf(varsFns), "Order of variables must be a subset of the free symbols+signature, but "
          + (order.toSet -- varsFns) + " is not in the subset")
        // use specified order in reverse, prepend the rest alphabetically
        // @note get both: specified order and compatibility with previous sorting, which resulted in
        //       reverse-alphabetical ordering of quantifiers
        val sorted: List[Term] = ((varsFns -- order).
          filter({ case Variable(_, _, _) => true case Function(_, _, Unit, _) => true case _ => false }).
          // guarantee stable sorting of quantifiers so that Mathematica behavior is predictable - for now: alphabetically
          toList.sortBy(_.name) ++ order.reverse).
          map({ case v@Variable(_, _, _) => v case fn@Function(_, _, Unit, _) => FuncOf(fn, Nothing) case _ => throw new IllegalArgumentException("Should have been filtered") })

        if (sorted.isEmpty) skip
        else sorted.map(t => universalGen(None, t)(pos)).reduce[BelleExpr](_ & _)
      }
    }
  }
  lazy val universalClosure: DependentPositionTactic = universalClosure()
}
