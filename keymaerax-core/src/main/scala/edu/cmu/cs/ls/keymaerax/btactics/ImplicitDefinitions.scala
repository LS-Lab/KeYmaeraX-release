package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance.dBarcan
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma

import scala.collection.immutable.List


/**
  * Implements tactics to handle implicit definitions
  */

object ImplicitDefinitions {

  private val namespace = "implicitdef"

  // Prove the partial derivative -> compose axiom
  lazy val DcomposeFull : Lemma = {
    val ss = USubst(List(SubstitutionPair("f()".asTerm, "1".asTerm)))
    val pr1 = ElidingProvable(Ax.Dassignby.provable.underlyingProvable(ss))

    val assignby = proveBy("[y_:=f();]p(y_) <-> p(f())".asFormula,
      byUS(Ax.assignbAxiom))

    val assignby2 = proveBy("[y_:=g(|y_|);][y_':=1;](f(g(|y_|)))'=e(y_)*(g(|y_|))' <-> [y_':=1;](f(g(|y_|)))'=e(g(|y_|))*(g(|y_|))'".asFormula,
      byUS(assignby))

    val assignby3 = proveBy("\\forall y_ p_(||) -> [y_:=f_();]p_(||)".asFormula,
      byUS(Ax.assignball))

    val pd = "\\forall y_ [y_':=1;](f(y_))' = e(y_) -> (f(g(|y_|)))'=e(g(|y_|)) * g(|y_|)'".asFormula

    remember(pd,
      implyR(1) &
        useAt(pr1, PosInExpr(1 :: Nil))(1) &
        useAt(assignby2, PosInExpr(1 :: Nil))(1) &
        cutR("[y_:=g(|y_|);][y_':=1;]( (f(g(|y_|)))' = (f(y_))' * (g(|y_|))' )".asFormula)(1) < (
          cohideR(1) & byUS(Ax.Dcompose),
          useAt(Ax.K)(1) &
            useAt(assignby3, PosInExpr(1 :: Nil))(1) & allR(1) & allL(-1) &
            useAt(Ax.K)(1) & monb & exhaustiveEqR2L(-1) & prop
        ),
      namespace
    )
  }

  // Flip the direction of partial derivative axiom
  lazy val flipPartial : Lemma = {
    val ss1 = USubst(List(SubstitutionPair("f()".asTerm, "-1".asTerm)))
    val pr1 = ElidingProvable(Ax.Dassignby.provable.underlyingProvable(ss1))

    val assignby = proveBy("[y_:=t;]p(y_) <-> p(t)".asFormula,
      byUS(Ax.assignbAxiom))

    val selfasg = proveBy("[y:=x;]p(||) -> (y=x -> p(||))".asFormula,
      implyR(1) & useAt(Ax.assignbeq)(-1) & allL(-1) & id
    )

    val arith = proveBy("f() * -1 = -g() -> f()=g()".asFormula,QE)

    remember("[t':=-1;](f(t))'=-g(t) -> [t':=1;](f(t))'=g(t)".asFormula,
      implyR(1) & DLBySubst.stutter("t".asVariable)(-1) & boundRename("t".asVariable,"y_".asVariable)(-1) &
        useAt(pr1, PosInExpr(1 :: Nil))(1) &
        useAt(assignby, PosInExpr(1 :: Nil))(1) &
        cutL("[y_:=t;][y_':=(-1);][t':=1;](f(y_))'=-g(y_)".asFormula)(-1) <(
          implyRi & K(1) & cutR("[y_:=t;][y_':=(-1);][t':=1;](f(y_))'=(f(t))'*(-1)".asFormula)(1) <(
            assignb(1) & assignb(1) &
              cutR("[t:=y_;][t':=1;](f(y_))'=(f(t))'*(-1)".asFormula)(1) <(
                cut("(y_)'=-1".asFormula) <(
                  cutR("[t:=y_;][t':=1;](f(y_))'=(f(t))'*(y_)'".asFormula)(1) <(
                    cohideR(1) & byUS(Ax.Dcompose),
                    exhaustiveEqL2R(-3) & cohideR(1) & implyR(1) & id
                  ),
                  hideR(1) & hideL(-1) & chase(1,0::Nil) & id
                ),
                implyR(1) & useAt(selfasg)(-3) & implyL(-3) <(
                  hideL(-2) & hideR(1) & QE,
                  id
                )
              )
            ,
            K(1) & G(1) & K(1,1::Nil) & K(1) & G(1) & K(1,1::Nil) & K(1) & G(1) &
              implyR(1) & exhaustiveEqL2R(hide=true)(-1) & cohideR(1) & byUS(arith)
          ),
          cohideR(2) & K(1) & G(1) & K(1) & G(1) & implyR(1) & Dassignb(1) & id
        ),
      namespace
    )
  }

  lazy val contBox : Lemma = {

    val tt = proveBy("!t_<f() -> [{t_'=1,c}]!t_ < f()".asFormula,
      implyR(1) & dI('full)(1)
    )

    val arith = proveBy("f()>=0&true&t_ < x_ ->  !(t_=x_|!f()>=0)".asFormula,QE)

    val pr = proveBy("\\exists x_ (t_=x_ & x_!=g()) <-> t_!=g()".asFormula, QE)

    remember("f(|x_|) > 0 -> \\exists x_ ( x_!=g() & [{t_'=1,c{|x_|}}](t_<x_ -> f(|x_|)>=0) )".asFormula,
      implyR(1) &
      cutL("<{t_'=1,c{|x_|}&f(|x_|)>=0}>\\exists x_ (t_=x_ & x_!=g())".asFormula)(-1) <(
          useAt(ODEInvariance.dBarcan,PosInExpr(1::Nil))(-1) &
            existsL(-1) & existsR(1) &  useAt(Ax.pVd, PosInExpr(1::Nil))(-1) & andL(-1) &
            andR(1) <(
              id,
              hideL(-2) &
                useAt(Ax.DCC)(1) & andR(1) <(
                boxd(1) & notR(1) &
                cutL("<{t_'=1,c{|x_|}&true&t_ < x_}>(t_=x_ | !f(|x_|)>=0)".asFormula)(-2) <( skip , cohideR(1) & implyR(1) & mond & prop) &
                cutL("<{t_'=1,c{|x_|}&f(|x_|)>=0}>(t_=x_ | !f(|x_|)>=0)".asFormula)(-1) <( skip , cohideR(1) & implyR(1) & mond & prop) & andLi &
                useAt(Ax.UniqIff,PosInExpr(0 :: Nil))(-1) & diamondd(-1) & notL(-1) & DW(1) & G(1) & byUS(arith)
                ,
                G(1) & byUS(tt)
            )
          ),
        cohideR(2) & implyR(1) & useAt(pr)(1,1::Nil) &
        useAt(ODEInvariance.contAx,PosInExpr(1::Nil))(1) & id
      ),
      namespace
    )
  }

  // Prove the n-dimensional there-and-back-like axiom
  // P(x) -> [{x'=f(x)}]<{x'=-f(x)}>P(x)
  def thereAndBack(dim : Int) : ProvableSig = {

    if(dim < 1)
      throw new IllegalArgumentException("Axiom derivable for dimension >= 1 but got: "+dim)
    //Indices 1,2,...dim
    val indices = 1 to dim
    // The list of LHS variables x__1, x__2, ..., x__dim
    val xLHS = indices.map(i => BaseVariable("x_", Some(i)))
    // The list of LHS variables y__1, y__2, ..., y__dim
    val yLHS = indices.map(i => BaseVariable("y_", Some(i)))
    // The sort of RHS functions and predicates is (real,(real,...)) n times
    val sort = indices.map(_ => Real).reduceRight(Tuple)
    val RHSfunc = indices.map(i => Function("f_", Some(i), sort, Real))
    // The application f_(x_) where x_ is written as a tuple of the right sort  (x_1,(x_2,(...))
    val RHSxarg = xLHS.reduceRight(Pair)
    val xRHS = RHSfunc.map { f => FuncOf(f, RHSxarg) }
    // The application f_(y_) where y_ is written as a tuple of the right sort (y_1,(y_2,(...))
    val RHSyarg = yLHS.reduceRight(Pair)
    val yRHS =  RHSfunc.map{ f => FuncOf(f,RHSyarg) }

    // pred
    val px = PredOf(Function("p_", None, sort, Bool), RHSxarg)
    val py = PredOf(Function("p_", None, sort, Bool), RHSyarg)

    // ODEs for x_ and its reverse
    val xODE = (xLHS zip xRHS).map { case (x, rhs) => AtomicODE(DifferentialSymbol(x), rhs) }
      .reduceRight(DifferentialProduct.apply)
    val xODER = (xLHS zip xRHS).map { case (x, rhs) => AtomicODE(DifferentialSymbol(x), Neg(rhs)) }
      .reduceRight(DifferentialProduct.apply)
    val yODER = (yLHS zip yRHS).map { case (y, rhs) => AtomicODE(DifferentialSymbol(y), Neg(rhs)) }
      .reduceRight(DifferentialProduct.apply)
    // Domains for x_
    val xDom = PredOf(Function("q_", None, sort, Bool), RHSxarg)
    val yDom = PredOf(Function("q_", None, sort, Bool), RHSyarg)

    val diffadj = ElidingProvable(Provable.diffAdjoint(dim))

    val fml = Imply(px, Box(ODESystem(xODE, xDom), Diamond(ODESystem(xODER, xDom), px)))

    val eqs = (xLHS zip yLHS).map(c => Equal(c._1,c._2)).reduceRight(And)
    val npost = And(eqs,Not(Diamond(ODESystem(yODER, yDom), py)))
    val ndia = Diamond(ODESystem(xODE,xDom),npost)
    val cutfml = yLHS.foldLeft(ndia:Formula)( (f,c) => Exists(c::Nil,f))

    val barcantac =
      (0 to dim-1).map( List.fill(_)(0)).foldLeft(skip:BelleExpr)( (p,t) =>
        useAt(dBarcan)(1,t) & p
      )

    val extac = xLHS.foldLeft(skip:BelleExpr)((t,v) => existsR(v)(1) & t)

    val zLHS = indices.map(i => BaseVariable("z_", Some(i)))
    val eqs2 = (zLHS zip xLHS).map(c => Equal(c._1,c._2)).reduceRight(And)
    val cutfml2 = zLHS.foldLeft(eqs2:Formula)( (f,c) => Exists(c::Nil,f))
    val eqr2l = (0 to dim-1).foldLeft(skip:BelleExpr)( (p,t) => exhaustiveEqR2L(-2-t) & p)

    proveBy(fml,
      implyR(1) & boxd(1) & notR(1) &
        cutL(cutfml)('Llast) <(
          existsL(-2)*dim & useAt(Ax.pVd)(-2) & andL(-2) & useAt(diffadj)(-2) &
          notL(-3) & andLi(AntePos(1),AntePos(0)) & useAt(Ax.pVd,PosInExpr(0::Nil))(-1) &
          mond & SaturateTactic(andL('L)) & SaturateTactic(exhaustiveEqL2R(hide=true)('L)) & id,
          cohideR('Rlast) &
          implyR(1) & barcantac & mond &
          cut(cutfml2) <(
            existsL('Llast) * dim & andL('Llast) * (dim-1) & eqr2l & extac & prop,
            cohideR(2) & QE
          )
    ))
  }
}
