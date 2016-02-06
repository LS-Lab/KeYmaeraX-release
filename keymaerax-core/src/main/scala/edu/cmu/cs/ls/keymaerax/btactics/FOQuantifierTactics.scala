package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._

import scala.collection.immutable._
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
           else base(pos+PosInExpr(0::Nil)) & useAt("!! double negation")(pos))
    }
  }

  def allInstantiate(quantified: Option[Variable] = None, instance: Option[Term] = None): DependentPositionTactic =
    new DependentPositionTactic("all instantiate") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
          case (ctx, f@Forall(vars, qf)) if quantified.isEmpty || vars.contains(quantified.get) =>
            require((if (pos.isAnte) -1 else 1) * FormulaTools.polarityAt(ctx(f), pos.inExpr) < 0, "\\forall must have negative polarity")
            def forall(h: Formula) = if (vars.length > 1) Forall(vars.filter(_ != vToInst(vars)), h) else h
            // cut in [x:=x;]p(t) from axiom: \forall x. p(x) -> p(t)
            val x = vToInst(vars)
            val t = inst(vars)
            val p = forall(qf)

            val subst = USubst(
              SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), forall(Box(Assign(x, DotTerm), qf))) ::
              SubstitutionPair("f()".asTerm, t) :: Nil)
            val orig = Sequent(Nil, IndexedSeq(),
              IndexedSeq(s"(\\forall ${x.prettyString} p(${x.prettyString})) -> p(f())".asFormula))

            DLBySubst.selfAssign(x)(pos + PosInExpr(0::Nil)) &
            ProofRuleTactics.cutLR(ctx(Box(Assign(x, t), p)))(pos.topLevel) <(
              assignb(pos) partial,
              cohide('Rlast) & CMon(pos.inExpr) & US(subst, orig) & byUS("all instantiate")
              )
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
   *     y>5   |- x^2>=0
   *     --------------------------allSkolemize(1)
   *     y>5   |- \forall x x^2>=0
   * }}}
   * @example Uniformly renames other occurrences of the quantified variable in the context on demand. {{{
   *     x_0>0 |- x^2>=0
   *     --------------------------allSkolemize(1)
   *     x>0   |- \forall x x^2>=0
   * }}}
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
        //@note rename variable x wherever bound to fresh x_0, so that final uniform renaming step renames back
        val renaming =
          if (namePairs.size > 1) namePairs.map(np => outerMostBoundPos(np._1, sequent).map(ProofRuleTactics.boundRenaming(np._1, np._2)(_)).reduce[BelleExpr](_&_)).reduce[BelleExpr](_ & _)
          else {assert(namePairs.size == 1); outerMostBoundPos(namePairs.head._1, sequent).map(ProofRuleTactics.boundRenaming(namePairs.head._1, namePairs.head._2)(_)).reduce[BelleExpr](_&_)}
        // uniformly rename variable x to x_0 and simultaneously x_0 to x, effectively swapping \forall x_0 p(x_0) back to \forall x p(x) but renaming all outside occurrences of x in context to x_0.
        val backrenaming =
          if (namePairs.size > 1) namePairs.map(np => ProofRuleTactics.uniformRenaming(np._2, np._1)).reduce[BelleExpr](_ & _)
          else {assert(namePairs.size == 1); ProofRuleTactics.uniformRenaming(namePairs.head._2, namePairs.head._1)}
        renaming & ProofRuleTactics.skolemizeR(pos) & backrenaming
      }
    }

    /** Finds positions where to bound rename */
    private def outerMostBoundPos(x: Variable, s: Sequent): IndexedSeq[Position] = {
      outerMostBoundPos(x, s.ante, AntePosition.apply) ++ outerMostBoundPos(x, s.succ, SuccPosition.apply)
    }

    private def outerMostBoundPos(x: Variable, fmls: IndexedSeq[Formula], posFactory: (Int, List[Int]) => Position): IndexedSeq[Position] = {
      fmls.map(outerMostBoundPos(x, _)).
        zipWithIndex.map({case (Some(posInExpr), i) => Some(posFactory(i+1, posInExpr.pos)) case (None, i) => None}).
        filter(_.isDefined).
        map(_.get)
    }

    private def outerMostBoundPos(x: Variable, fml: Formula): Option[PosInExpr] = {
      var outerMostBound: Option[PosInExpr] = None
      ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
        override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
          case Forall(xs, _) if xs.contains(x) => outerMostBound = Some(p); Left(Some(ExpressionTraversal.stop))
          case Exists(xs, _) if xs.contains(x) => outerMostBound = Some(p); Left(Some(ExpressionTraversal.stop))
          case Box(Assign(y, _), _) if x==y => outerMostBound = Some(p); Left(Some(ExpressionTraversal.stop))
          case Diamond(Assign(y, _), _) if x==y => outerMostBound = Some(p); Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, fml)
      outerMostBound
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
          val aT = FuncOf(Function("t_", None, Unit, Real), Nothing)
          val aP = PredOf(Function("p_", None, Real, Bool), DotTerm)
          val pDot = replaceWheres(fml, DotTerm)
          val subst = USubst(
            SubstitutionPair(aP, pDot) ::
            SubstitutionPair(aT, sequent.sub(pos.navigate(where.head)).get) :: Nil)
          val origin = Sequent(Nil, IndexedSeq(),
            IndexedSeq(Imply("p_(t_())".asFormula, Exists(x::Nil, PredOf(Function("p_", None, Real, Bool), x)))))

          cut(Imply(fml, Exists(x :: Nil, fmlRepl))) <(
            /* use */ implyLOld('Llast) <(closeId, hide(pos,fml) partial) partial,
            /* show */ cohide('Rlast) & TactixLibrary.by(DerivedAxioms.derivedAxiom("exists generalize")(subst))
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

        val genFml = Forall(Seq(quantified), SubstitutionHelper.replaceFree(sequent(pos.top))(t, quantified))
        cut(genFml) <(
          /* use */ allL(quantified, t)('Llast) & closeId,
          /* show */ hide(pos.top) partial
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
        val varsFns: Set[NamedSymbol] = StaticSemantics.freeVars(sequent(pos.top)).toSet ++ StaticSemantics.signature(sequent(pos.top))
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
