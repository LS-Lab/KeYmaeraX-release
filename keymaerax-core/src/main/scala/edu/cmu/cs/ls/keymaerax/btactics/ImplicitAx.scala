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
import edu.cmu.cs.ls.keymaerax.btactics.Ax.boxTrueAxiom
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.{anon, inputanon}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.lemma.Lemma

import scala.collection.immutable.List


/** Derives axioms from implicit (differential) definitionss
  */

object ImplicitAx {

  private val namespace = "implicitax"

  private def canonicalDiffAxName(f: Function) : String = {
    // todo: how to use directory structure?
    "D"+f.name
  }

  private def registerDiffAx(f: Function, p:ProvableSig) : Unit = {
    println("Registering differential axiom: ",f,p)
    val name = canonicalDiffAxName(f)
    val codename = name
    val info = new DerivedAxiomInfo(name,
      AxiomDisplayInfo(SimpleDisplayInfo(name,name), "displayFormula"),
      codename,
      name,
      'surlinear,
      {case () => edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.useAt(ProvableInfo(name)) },
      'internal,
      List(0),
      List(List(1))
    )
    DerivationInfo.registerR( Ax.derivedAxiomFromFact(name,
      p.conclusion.succ(0),
      p,
      Some(codename)
    ), info)
  }

  // todo: for efficiency initialize ProvableInfo with pre-proved differential axioms
  def getDiffAx(f: Function) : Option[ProvableInfo] = {
    try {
      Some(ProvableInfo(canonicalDiffAxName(f)))
    }
    catch {
      case e:AxiomNotFoundException => {
        try {
          val fpr = deriveDiffAxiomSing(f)
          fpr.foreach(f => registerDiffAx(f._1,f._2))

          if(fpr.map(_._1).contains(f)) getDiffAx(f)
          else None
        }
        catch {
          case e:IllegalArgumentException => {
            //println(e.getMessage)
            None
          }
        }
      }
    }
  }

  private def canonicalInitAxName(f: Function) : String = {
    // todo: how to use directory structure?
    "I"+f.name
  }

  private def registerInitAx(f: Function, p:ProvableSig) : Unit = {
    println("Registering initial condition axiom: ",f,p)
    val name = canonicalInitAxName(f)
    val codename = name
    val info = new DerivedAxiomInfo(name,
      AxiomDisplayInfo(SimpleDisplayInfo(name,name), "displayFormula"),
      codename,
      name,
      'surlinear,
      {case () => edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.useAt(ProvableInfo(name)) },
      'internal,
      List(0),
      List(List(1))
    )
    DerivationInfo.registerR( Ax.derivedAxiomFromFact(name,
      p.conclusion.succ(0),
      p,
      Some(codename)
    ), info)
  }

  // todo: for efficiency initialize ProvableInfo with pre-proved differential axioms
  def getInitAx(f: Function) : Option[ProvableInfo] = {
    try {
      Some(ProvableInfo(canonicalInitAxName(f)))
    }
    catch {
      case e:AxiomNotFoundException => {
        try {
          val pr = deriveInitAxiom(f)
          registerInitAx(f,pr)
          getInitAx(f)
        }
        catch {
          case e:IllegalArgumentException => {
            // println(e.getMessage)
            None
          }
        }
      }
    }
  }

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
    val ss1 = USubst(List(SubstitutionPair("f()".asTerm, "-(1)".asTerm)))
    val pr1 = ElidingProvable(Ax.Dassignby.provable.underlyingProvable(ss1))

    val assignby = proveBy("[y_:=t;]p(y_) <-> p(t)".asFormula,
      byUS(Ax.assignbAxiom))

    val selfasg = proveBy("[y:=x;]p(||) -> (y=x -> p(||))".asFormula,
      implyR(1) & useAt(Ax.assignbeq)(-1) & allL(-1) & id
    )

    val arith = proveBy("f() * -(1) = -g() -> f()=g()".asFormula,QE)

    remember("[t':=-(1);](f(t))'=-g(t) -> [t':=1;](f(t))'=g(t)".asFormula,
      implyR(1) & DLBySubst.stutter("t".asVariable)(-1) & boundRename("t".asVariable,"y_".asVariable)(-1) &
        useAt(pr1, PosInExpr(1 :: Nil))(1) &
        useAt(assignby, PosInExpr(1 :: Nil))(1) &
        cutL("[y_:=t;][y_':=-(1);][t':=1;](f(y_))'=-g(y_)".asFormula)(-1) <(
          implyRi & K(1) & cutR("[y_:=t;][y_':=-(1);][t':=1;](f(y_))'=(f(t))'*-(1)".asFormula)(1) <(
            assignb(1) & assignb(1) &
              cutR("[t:=y_;][t':=1;](f(y_))'=(f(t))'*-(1)".asFormula)(1) <(
                cut("(y_)'=-(1)".asFormula) <(
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
        )
    )
  }

  // First derivative
  lazy val firstDer : Lemma = {
    val ss1 = USubst(List(SubstitutionPair("b(|y_|)".asTerm, "1".asTerm)))
    val pr1 = Ax.DGCa.provable(ss1)(URename("y_".asVariable,"t_".asVariable,semantic=true))
    val pr2 = Ax.alle.provable(URename("x_".asVariable,"t_".asVariable,semantic=true))

    val pr3 = Ax.DGC.provable(ss1)(URename("y_".asVariable,"t_".asVariable,semantic=true))
    val pr4 = proveBy("p_(||) -> (\\exists t_ p_(||))".asFormula, byUS(Ax.existse))

    val g = proveBy("[{c{|t_|}}]p(|t_|) <-> [{t_'=1,c{|t_|}}]p(|t_|)".asFormula,
      equivR(1) <(
        useAt(pr1)(-1) & useAt(pr2)(-1) & useAt(Ax.commaCommute)(-1) & id,
        useAt(pr3)(1) & useAt(pr4,PosInExpr(1::Nil))(1) & useAt(Ax.commaCommute)(1) & id
      )
    )

    val arith = proveBy("!f()=0 ==> f() > 0 | -f()>0".asSequent, QE)
    val negprop = proveBy("!(p()&q()) <-> (p() -> !q())".asFormula, prop)
    val arith2 = proveBy("f()-2*(t_-g())>=0->f()-2*(t_-g())^(2-1)*(1-0)>=0".asFormula,QE)
    val arith3 = proveBy("f()>0, t_=g()  ==>  f()-2*(t_-g())>0".asSequent, QE)

    // c{|t0|} annoying so that we can do g() ~> t0 later
    val tt = proveBy("f(||)=0, t_=g()  ==>  [{t_'=1,c{|t0|}&(f(||))'-2*(t_-g())>=0}]f(||)-(t_-g())^2>=0".asSequent,
      useAt(Ax.DI)(1) & implyR(1) & andR(1) <(
        hideL(-3) & hideL(-3) & exhaustiveEqL2R(-1) & hideL(-1) & QE,
        hideL(-1) & hideL(-1) & chase(1,1::Nil) & DW(1) &
          DE(1) & G(1) & useAt(Ax.Dassignbeq)(1) & allR(1) & implyR(1) &
          exhaustiveEqL2R(-1) & hideL(-1) & byUS(arith2)
      )
    )

    val tt2 = proveBy("f(||)=0, t_=g()  ==>  [{t_'=1,c{|t0|}&-(f(||))'-2*(t_-g())>=0}]-f(||)-(t_-g())^2>=0".asSequent,
      useAt(Ax.DI)(1) & implyR(1) & andR(1) <(
        hideL(-3) & hideL(-3) & exhaustiveEqL2R(-1) & hideL(-1) & QE,
        hideL(-1) & hideL(-1) & chase(1,1::Nil) & DW(1) &
          DE(1) & G(1) & useAt(Ax.Dassignbeq)(1) & allR(1) & implyR(1) &
          exhaustiveEqL2R(-1) & hideL(-1) & byUS(arith2)
      )
    )

    remember("[{c{|t_,t0|}}]f(|t_,t0|)=0 -> [{c{|t_,t0|}}]f(|t_,t0|)'=0".asFormula,
      implyR(1) &
        useAt(g,PosInExpr(0::Nil))(1) &
        useAt(g,PosInExpr(0::Nil))(-1) &
        boxd(1) & notR(1) &
        cutL("<{t_'=1,c{|t_,t0|}}>(((f(|t_,t0|)'>0 | -f(|t_,t0|)' > 0) & f(|t_,t0|)=0) & [{t_'=1,c{|t_,t0|}}]f(|t_,t0|)=0)".asFormula)(-2) <(
          //this part must be done more carefully in context when cont is changed
          diamondd(-2) & notL(-2) & G(1) & useAt(negprop)(1) & implyR(1) & useAt(Ax.notBox)(1) & andL(-1) &
            cut("\\exists t0 ( t_ = t0)".asFormula) <(
              existsL(-3) & orL(-1) <(
                cut("(f(|t_,t0|))' - 2*(t_-t0) > 0".asFormula) <(
                  cutR("<{t_'=1,c{|t_,t0|}& f(|t_,t0|)-(t_-t0)^2>=0}>t_!=t0".asFormula)(1) <(
                    ODELiveness.dDR("(f(|t_,t0|))'-2*(t_-t0)>=0".asFormula)(1)  <(
                      useAt(ODEInvariance.contAx,PosInExpr(1::Nil))(1) & id,
                      hideL(-1) & hideL(-3) & byUS(tt)
                    ) ,
                    cohideR(1) & implyR(1) &
                      DWd(-1) & ODELiveness.kDomainDiamond("f(|t_,t0|)-(t_-t0)^2>=0 & t_!=t0".asFormula)(1)<(
                      ODELiveness.dDR("f(|t_,t0|)-(t_-t0)^2>=0".asFormula)(1) <(
                        id,
                        G(1) & closeT
                      ),
                      DW(1) & G(1) & implyR(1) & andL(-1) & notL(-2) & notR(2) & exhaustiveEqL2R()(-2) & hideL(-2) & QE
                    )
                  ),
                  hideR(1) & hideL(-2) & byUS(arith3)
                ),
                // reverse direction
                cut("-(f(|t_,t0|))' - 2*(t_-t0) > 0".asFormula) <(
                  cutR("<{t_'=1,c{|t_,t0|}& -f(|t_,t0|)-(t_-t0)^2>=0}>t_!=t0".asFormula)(1) <(
                    ODELiveness.dDR("-(f(|t_,t0|))'-2*(t_-t0)>=0".asFormula)(1)  <(
                      useAt(ODEInvariance.contAx,PosInExpr(1::Nil))(1) & id,
                      hideL(-1) & hideL(-3) & byUS(tt2)
                    ) ,
                    cohideR(1) & implyR(1) &
                      DWd(-1) & ODELiveness.kDomainDiamond("-f(|t_,t0|)-(t_-t0)^2>=0 & t_!=t0".asFormula)(1)<(
                      ODELiveness.dDR("-f(|t_,t0|)-(t_-t0)^2>=0".asFormula)(1) <(
                        id,
                        G(1) & closeT
                      ),
                      DW(1) & G(1) & implyR(1) & andL(-1) & notL(-2) & notR(2) & exhaustiveEqL2R()(-2) & hideL(-2) & QE
                    )
                  ),
                  hideR(1) & hideL(-2) & byUS(arith3)
                )),
              cohideR(2) & QE
            ),
          useAt(Ax.Kd,PosInExpr(1::Nil))(1) & useAt(Ax.Dcomp)(-1) & monb &
            implyR(1) & andR(1) <(
            andR(1) <(
              hideL(-1) & byUS(arith),
              useAt(Ax.DX)(-1) & prop),
            id
          )
        ),
    namespace)
  }

  private lazy val firstDerVar = remember("[{c{|y_,z_|}}]x_=g(t_) -> [{c{|y_,z_|}}]x_'=(g(t_))'".asFormula,
    implyR(1) & useAt(Ax.eqNormalize)(-1,1::Nil) &
      useAt(firstDer.fact(URename("t_".asVariable,"y_".asVariable,semantic=true))(URename("t0".asVariable,"z_".asVariable,semantic=true)))(-1) & monb &
      chase(-1,0::Nil) & useAt(Ax.eqNormalize)(1) & id,
    namespace
  )

  lazy val contBox : Lemma = {

    val tt = proveBy("!f()-t_>0 -> [{t_'=1,c}]!f()-t_>0".asFormula,
      implyR(1) & dI('full)(1)
    )

    val tt2 = proveBy("t_=g() ==> [{t_'=1,c}]t_>=g()".asSequent,
      dI('full)(1)
    )

    val arith = proveBy("f()>=0&true&x_-t_>0->!(t_=x_|!f()>=0)".asFormula,QE)

    val pr = proveBy("\\exists x_ (t_=x_ &x_-g()>0) <-> t_>g()".asFormula, QE)

    remember("f(|x_|) > 0 & t_ = g() -> \\exists x_ ( x_ - g() > 0 & [{t_'=1,c{|x_|}}](x_-t_>0 -> f(|x_|)>=0) )".asFormula,
      implyR(1) &
        cutL("<{t_'=1,c{|x_|}&f(|x_|)>=0}>\\exists x_ (t_=x_ & x_ - g() > 0)".asFormula)(-1) <(
          useAt(ODEInvariance.dBarcan,PosInExpr(1::Nil))(-1) &
            existsL(-1) & existsR(1) &  useAt(Ax.pVd, PosInExpr(1::Nil))(-1) & andL(-1) &
            andR(1) <(
              id,
              hideL(-2) &
                useAt(Ax.DCC)(1) & andR(1) <(
                boxd(1) & notR(1) &
                  cutL("<{t_'=1,c{|x_|}&true&x_-t_>0}>(t_=x_ | !f(|x_|)>=0)".asFormula)(-2) <( skip , cohideR(1) & implyR(1) & mond & prop) &
                  cutL("<{t_'=1,c{|x_|}&f(|x_|)>=0}>(t_=x_ | !f(|x_|)>=0)".asFormula)(-1) <( skip , cohideR(1) & implyR(1) & mond & prop) & andLi &
                  useAt(Ax.UniqIff,PosInExpr(0 :: Nil))(-1) & diamondd(-1) & notL(-1) & DW(1) & G(1) &
                  byUS(arith)
                ,
                G(1) & byUS(tt)
              )
            ),
          cohideR(2) & implyR(1) & useAt(pr)(1,1::Nil) &
            andL(-1) & ODELiveness.kDomainDiamond("t_!=g()".asFormula)(1) <(
            useAt(ODEInvariance.contAx,PosInExpr(1::Nil))(1) & id,
            hideL(-1) & dC("t_>=g()".asFormula)(1) <(
              DW(1) & G(1) & implyR(1) & andL(-1) & andL(-1) & hideL(-2) & QE,
              dR("true".asFormula)(1) <(
                byUS(tt2),
                cohideR(1) & useAt(boxTrueAxiom)(1)
              )
            )
          )
        ),
      namespace
    )
  }

  private lazy val impSplit = remember(
    "([b_{|^@|};]p(||) -> [a_{|^@|};]r(||)) & ([b_{|^@|};]q(||) -> [a_{|^@|};]s(||)) -> ([b_{|^@|};](p(||)&q(||)) -> [a_{|^@|};](r(||)&s(||)))".asFormula,
    implyR(1) & implyR(1) & boxAnd(-2) & boxAnd(1) & prop,
    namespace
  )

  // Prove the n-dimensional partial derivative axiom
  // [x'=f(x,t),t'=h()]x=g(t) -> [t':=h()](g(t))'=f(g(t),t)
  def partialDer(dim : Int) : ProvableSig = {

    if(dim < 1)
      throw new IllegalArgumentException("Axiom derivable for dimension >= 1 but got: "+dim)
    //Indices 1,2,...dim
    val indices = 1 to dim

    val tvar = "t_".asVariable
    val trhs = FuncOf(Function("h_", None, Unit, Real), Nothing)

    // The list of LHS variables x__1, x__2, ..., x__dim
    val xLHS = indices.map(i => BaseVariable("x_", Some(i)))
    val sort = (indices:+0).map(_ => Real).reduceRight(Tuple)
    val RHSfunc = indices.map(i => Function("f_", Some(i), sort, Real))
    // The application f_(x_) where x_ is written as a tuple of the right sort  (x_1,(x_2,(...))
    val RHSxarg = (xLHS:+tvar).reduceRight(Pair)
    val xRHS = RHSfunc.map { f => FuncOf(f, RHSxarg) }

    val gFunc = indices.map(i => Function("g_", Some(i), Real, Real))
    val gApp = gFunc.map { f => FuncOf(f, tvar) }
    val garg = (gApp:+tvar).reduceRight(Pair)
    val gRHS = RHSfunc.map {f => FuncOf(f,garg)}

    val tode = AtomicODE(DifferentialSymbol(tvar),trhs)
    val tassign = Assign(DifferentialSymbol(tvar),trhs)

    val xODE = DifferentialProduct((xLHS zip xRHS).map { case (x, rhs) => AtomicODE(DifferentialSymbol(x), rhs) }
      .reduceRight(DifferentialProduct.apply),tode)

    val eqs = (xLHS zip gApp).map(c => Equal(c._1,c._2)).reduceRight(And)
    val deqs = (xLHS zip gApp).map(c => Equal(DifferentialSymbol(c._1),Differential(c._2))).reduceRight(And)

    val gdeqs = (gApp zip gRHS).map(c => Equal(Differential(c._1),c._2)).reduceRight(And)

    val fml = Imply(Box(ODESystem(xODE, True),eqs),Box(tassign,gdeqs))

    proveBy(fml,
      implyR(1) &
      cutL(Box(ODESystem(xODE, True),And(eqs,deqs)))(-1)<(
        DE(-1) & useAt(Ax.DX)(-1) & implyL(-1) <( closeT,
          monb & (Dassignb(-1) * dim) &
            andL(-1) &
            // Get rid of f(x)=(g(t))' equalities
            (andL(-2) & exhaustiveEqR2L()(-2) & hideL(-2))* (dim-1) & exhaustiveEqR2L()(-2) & hideL(-2) &
            // Get rid of x=g(t) equalities
            (andL(-1) & exhaustiveEqL2R()(-1) & hideL(-1))* (dim-1) & exhaustiveEqL2R()(-1) & hideL(-1) &
            // Prove all remaining equalities
            (andR(1) <(byUS(Ax.equalReflexive), skip))* (dim-1) & byUS(Ax.equalReflexive)
        ),
        cohideR(2) & implyR(1) & boxAnd(1) & andR(1) <(
          id,
          implyRi &
          (useAt(impSplit,PosInExpr(1::Nil))(1) & andR(1) <(byUS(firstDerVar), skip))* (dim-1) & byUS(firstDerVar)
        )
      )
    )
  }

  // Prove the n-dimensional there-and-back-like axiom
  // P(x) -> [{x'=f(x)&q(x)}]<{x'=-f(x)&q(x)}>P(x)
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
          notL(-3) & andLi(keepLeft=false)(AntePos(1),AntePos(0)) & useAt(Ax.pVd,PosInExpr(0::Nil))(-1) &
          mond & SaturateTactic(andL('L)) & SaturateTactic(exhaustiveEqL2R(hide=true)('L)) & id,
          cohideR('Rlast) &
          implyR(1) & barcantac & mond &
          cut(cutfml2) <(
            existsL('Llast) * dim & andL('Llast) * (dim-1) & eqr2l & extac & prop,
            cohideR(2) & QE
          )
    ))
  }

  // todo: move to Ax.scala
  private lazy val dDcomp = {
    val pr0 = proveBy("(p() <-> q()) <-> (!p() <-> !q())".asFormula, prop)

    remember("==> <{c&q(||)}>p(||) <-> <{c&q(||)}><{c&q(||)}>p(||)".asSequent,
      useAt(pr0)(1) &
        useAt(Ax.notDiamond)(1, 0::Nil) &
        useAt(Ax.notDiamond)(1, 1::Nil) &
        useAt(Ax.notDiamond)(1, 1::1::Nil) &
        byUS(Ax.Dcomp),
      namespace
    )
  }

  private lazy val boxOrLeft = remember("[a;]p(||) -> [a;](p(||) | q(||))".asFormula,
    implyR(1) & monb & prop,
    namespace
  )

  private lazy val boxOrRight = remember("[a;]q(||) -> [a;](p(||) | q(||))".asFormula,
    implyR(1) & monb & prop,
    namespace
  )

  // Prove the def-expansion to box axiom
  // This currently requires a concrete ODE to do the rewrite --f(x) = f(x) in the context of an ODE
  // <x'=-f(x)>P(x)|<x'=f(x)>P(x) ->
  // [{x'=f(x)}] <x'=-f(x)>P(x) | [{x'=-f(x)}] <x'=f(x)>P(x)
  def defExpandToBox(ode: DifferentialProgram) : ProvableSig = {

    val odels = DifferentialProduct.listify(ode).map {
      case AtomicODE(x,e) => (x,e)
      case _ => throw new TacticInapplicableFailure("ODE def expansion only applicable to concrete ODEs")
    }

    val odeLHS = odels.map( _._1.x)

    val dim = odels.length
    val indices = 1 to dim
    val sort = indices.map(_ => Real).reduceRight(Tuple)

    val RHSodearg = odeLHS.reduceRight(Pair)
    val px = PredOf(Function("p_", None, sort, Bool), RHSodearg)
    val odeDom = PredOf(Function("q_", None, sort, Bool), RHSodearg)
    val oder = odels.map{ case (x, rhs) => AtomicODE(x, Neg(rhs)) }
          .reduceRight(DifferentialProduct.apply)

    // Fresh names
    val yLHS = indices.map(i => BaseVariable("y_", Some(i)))
    val xLHS = indices.map(i => BaseVariable("x_", Some(i)))

    // Expected expanded shape of a definition
    val expLeft = Diamond(ODESystem(oder,odeDom),px)
    val expRight = Diamond(ODESystem(ode,odeDom),px)
    val expdef = Or(expLeft,expRight)

    val tab = (xLHS zip odeLHS).foldLeft(thereAndBack(dim))((t,v) => t(URename(v._1,v._2)))

    val fwdSub = UnificationMatch(tab.conclusion.succ(0).sub(PosInExpr(1::0::0::Nil)).get,ode)
    val fwd = fwdSub.toForward(tab)
    val bwdSub = UnificationMatch(tab.conclusion.succ(0).sub(PosInExpr(1::0::0::Nil)).get,oder)
    val bwd = bwdSub.toForward(tab)

    val fml = Imply(expdef, Or(Box(ODESystem(ode,odeDom),expLeft),Box(ODESystem(oder,odeDom),expRight)))

    val stt = (pos:Int) => (odeLHS zip yLHS).foldLeft(skip:BelleExpr)((t,v) => DLBySubst.stutter(v._1)(pos) & boundRename(v._1,v._2)(pos) & t)

    proveBy(fml,
      implyR(1) & orR(1) & orL(-1) <(
        hideR(2) & stt(-1) &
        useAt(fwd)(-1) & monb & useAt(dDcomp)(1) & mond & stt(1) & id,
        hideR(1) & stt(-1) &
        useAt(bwd)(-1) & monb & ODEInvariance.rewriteODEAt(ode)(-1) & useAt(dDcomp)(1) & mond & stt(1) & id
      )
     )
  }

  /**  Derive differential axioms for list of interpreted functions fs
    *  The interpretation for each function must have the expected shape:
    *  . = g(.0) <-> <{x_1:=*; x_0:=.; t:=.0;} {x'=-f(x), t'=-(1) ++ x'=f(x), t'=1} > Init
    */
  def deriveDiffAxiom(fs : List[Function]) : List[ProvableSig] = {

    val dim = fs.length
    if(dim < 1)
      throw new IllegalArgumentException("Axiom derivable for dimension >= 1 but got: "+ fs.length)

    require(fs.forall(f => f.interp.isDefined), "Functions must be interpreted: " + fs)

    val ode = fs.head.interp.get match {
      case Diamond(Compose(_,Choice(_,ODESystem(ode,True))),_) => ode
      case _ => throw new IllegalArgumentException("Function interpretation not of expected shape: "+ fs.head.interp.get)
    }

    // Canonicalize the shape of the implicit definition
    val canonPr = canonicalize(ode,fs)
    // println("Canonicalized: ", canonPr)

    // Set up for partial derivatives

    // Using the first equation, derive [x'=f(x),t'=1](x = g(t)) | [x'=-f(x),t'=-1](x = g(t))
    val zers = (1 to dim-1).map(_ => 0).toList
    val renfml = canonPr.head.conclusion.succ(0).sub(PosInExpr( 1 :: zers)).get.asInstanceOf[Formula]
    val renode = renfml.sub(PosInExpr(1::0::Nil)).get.asInstanceOf[ODESystem]
    val renodeR = renfml.sub(PosInExpr(0::0::Nil)).get.asInstanceOf[ODESystem]
    val defExpPre = defExpandToBox(renode.ode)
    val unif = UnificationMatch(defExpPre.conclusion.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Formula],renfml)
    val defExp = unif.toForward(defExpPre)
    // println("Def expand: ",defExp)

    val equations = canonPr.map( p => p.conclusion.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Equal])
    val parDerPre = partialDer(equations.length)
    val equationsAnd = equations.reduceRight(And)
    val xLHS = (1 to dim).map(i => BaseVariable("x_", Some(i)))
    val zLHS = (1 to dim).map(i => BaseVariable("z_", Some(i)))
    val tab = (xLHS zip zLHS).foldLeft(parDerPre)((t,v) => t(URename(v._1,v._2)))
    val unif2 = UnificationMatch(tab.conclusion.succ(0).sub(PosInExpr(0::Nil)).get,Box(renode,equationsAnd))
    val unif3 = UnificationMatch(tab.conclusion.succ(0).sub(PosInExpr(0::Nil)).get,Box(renodeR,equationsAnd))
    val parDer = unif2.toForward(tab)
    val parDerR = unif3.toForward(tab)
    // println("Partial der: ",parDer)
    // println("Partial der R: ",parDerR)

    val pdfml = parDer.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]

    val eq1 = equations.head
    val pr1 = canonPr.head

    val pd = proveBy(pdfml,
      cut(Exists(eq1.left.asInstanceOf[Variable]::Nil,eq1)) <(
        existsL(-1) & useAt(pr1)(-1) & (existsL(-1) * (dim-1)) & useAt(defExp)(-1) & orL(-1) <(
          cutL(parDer.conclusion.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Formula])(-1) <(
            implyRi & byUS(parDer),
            cohideR(2) & implyR(1) & monb &
            canonPr.dropRight(1).foldRight(skip:BelleExpr)( (pr,t) =>
              andR(1)<(useAt(pr)(1) & (existsR(1) * (dim-1)) & orR(1) & hideR(2) & id, t)) &
            useAt(canonPr.last)(1) & (existsR(1) * (dim-1)) & orR(1) & hideR(2) & id
          ),
          cutL(parDerR.conclusion.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Formula])(-1) <(
            useAt(parDerR)(-1) &
              implyRi &
              (useAt(impSplit,PosInExpr(1::Nil))(1) & andR(1) <(byUS(flipPartial), skip))* (dim-1) &
              byUS(flipPartial),
              cohideR(2) & implyR(1) & monb &
              canonPr.dropRight(1).foldRight(skip:BelleExpr)( (pr,t) =>
                andR(1)<(useAt(pr)(1) & (existsR(1) * (dim-1)) & orR(1) & hideR(1) & id, t)) &
              useAt(canonPr.last)(1) & (existsR(1) * (dim-1)) & orR(1) & hideR(1) & id
          )
        ),
        cohideR(2) & existsR(eq1.right)(1) & byUS(Ax.equalReflexive)
      )
    )

    val pdA = chaseFor(6,6,e=>
      e match {
        case Box(_,And(_,_)) => List(Ax.boxAnd)
        case _ => List()
      },(s,p)=>pr=>pr)(SuccPosition(1))(pd)

    val ls = (1 to dim-1).foldLeft((pdA,List[ProvableSig]()))( (pr,d) => {
      val (l, r) = splitConj(pr._1)
      (r, l::pr._2)
    }
    )
    val splits = (ls._1::ls._2).reverse

    val pr = proveBy("(f(g(|t_|)))'=e(g(|t_|)) * g(|t_|)'".asFormula,
      useAt(DcomposeFull.fact(URename("y_".asVariable,"t_".asVariable,semantic=true)),PosInExpr(1::Nil))(1) & allR(1))

    val axs = splits.map( sp => {
      val u = UnificationMatch(pr.subgoals(0), sp.conclusion)
      sp(u.toForward(pr))
    })
    axs
  }

  private def listifyCompose(p:Program) : List[AtomicProgram] = p match{
    case Compose(l,r) => listifyCompose(l) ++ listifyCompose(r)
    case a : AtomicProgram => List(a)
    case _ => throw new IllegalArgumentException("Unable to flatten program to a list of atomic programs: "+ p)
  }

  /** Same as deriveDiffAxiom but generates the list of simultaneously defined functions by guessing names
    *
    * @param f an interpreted function with differential equations
    * @return list of proved differential axioms
    */
  def deriveDiffAxiomSing(f : Function) : List[(Function,ProvableSig)] = {
    require(f.interp.isDefined,"Function must be interpreted: " + f)

    val (assgn,q,r) = f.interp.get match {
      case Diamond(Compose(p,q),r) => (p,q,r)
      case _ => throw new IllegalArgumentException("Function interpretation not of expected shape: "+ f.interp.get)
    }

    val assgnList = listifyCompose(assgn)

    val arbs = assgnList.dropRight(2).map(p => p.asInstanceOf[AssignAny].x)
    val t0 = assgnList.last.asInstanceOf[Assign].x
    val x0 = assgnList.dropRight(1).last.asInstanceOf[Assign].x

    val temp = Variable("temp_")

    // Function name must match the guessed name
    require(f.name == x0.name,"Function interpretation not of expected shape: "+ f.interp.get)

    val names = x0::arbs
    val assgnraw = assgn.replaceAll(x0,temp)

    // Repeatedly swap other names in place of x0 for other functions in the chain
    // TODO: does this match the order of assignments generated by ODEToInterpreted?
    val swaps = names.map( a => {
      val assgn = assgnraw.replaceAll(a, x0).replaceAll(temp, a)
      val interp = Diamond(Compose(assgn, q), r)
      Function(a.name, None, f.domain, f.sort, Some(interp))
    })

    swaps zip deriveDiffAxiom(swaps)
  }

  // Split |- A & B into |- A, |- B
  private def splitConj(pr : ProvableSig) : (ProvableSig, ProvableSig) = {
    val concl = pr.conclusion.succ(0).asInstanceOf[And]

    val left = proveBy(concl.left,
      cut(concl)<(andL(-1) & id, cohideR(2) & byUS(pr))
    )

    val right = proveBy(concl.right,
      cut(concl)<(andL(-1) & id, cohideR(2) & byUS(pr))
    )

    (left,right)
  }

  // Canonicalize and give fixed names for variables
  // . = g(.0) <-> <{x_1:=*; x_0:=.; t:=.0;} {x'=-f(x), t'=-(1) ++ x'=f(x), t'=1} > Init
  // x_0 = g(t_) <-> \exists x_1 { x'=-f(x),t'=-(1) ++ x'=f(x),t'=1 } > Init
  private def canonicalize(ode: DifferentialProgram, fs : List[Function]) : List[ProvableSig] = {

    val odels = DifferentialProduct.listify(ode).map {
      case AtomicODE(x,e) => (x,e)
      case _ => throw new IllegalArgumentException("Unable to canonicalize ODEs: " + ode)
    }

    val odeLHS = odels.map( _._1.x)

    val timevar = "t_".asVariable
    val xLHS = (1 to fs.length).map(i => BaseVariable("z_", Some(i)))

    val axs = fs.map( f => Provable.implicitFuncAxiom(f))

    val vpairs = (xLHS.toList :+ timevar) zip odeLHS

    val axsS = axs.map(a => vpairs.foldLeft(a)((t,v) => t(URename(v._1,v._2))))

    val ss = ((1 to fs.length) zip axsS).map(ia =>
      ia._2(USubst(List(
        SubstitutionPair(DotTerm(Real,Some(0)), BaseVariable("z_", Some(ia._1))),
        SubstitutionPair(DotTerm(Real,Some(1)), timevar)
      )))
    )

    val sss = ss.map( s =>
      chaseFor(6,6,e=>
        e match {
          case Diamond(AssignAny(_),_) => List(Ax.randomd)
          case Diamond(Assign(_,_),_) => List(Ax.selfassignd)
          case Diamond(Compose(_,_),_) => List(Ax.composed)
          case Diamond(Choice(_,_),_) => List(Ax.choiced)
          case _ => List()
        },(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(ElidingProvable(s))
    ).toList

    sss
  }

  // Derive initial value axiom for an interpreted function g
  // The interpretation must have the expected shape:
  // . = g(.0) <-> <{x_1:=*; x_0:=.; t:=.0;} {x'=-f(x), t'=-(1) ++ x'=f(x), t'=1} > (init values)
  def deriveInitAxiom(f : Function) : ProvableSig = {
    require(f.interp.isDefined,"Function must be interpreted: " + f)

    val (assgn,inits) = f.interp.get match {
      case Diamond(Compose(assgn,Choice(_,ODESystem(ode,True))),inits) => (assgn,inits)
      case _ => throw new IllegalArgumentException("Function interpretation not of expected shape: "+ f.interp.get)
    }

    val m = FormulaTools.conjuncts(inits).map( fml =>
      fml match {
        case Equal(x:Variable,i) => (x,i)
        case _ => throw new IllegalArgumentException("Function interpretation not of expected shape: "+ f.interp.get)
      }
    ).toMap

    val assgnList = listifyCompose(assgn)

    val arbs = assgnList.dropRight(2).map(p => m(p.asInstanceOf[AssignAny].x))
    val t0 = m(assgnList.last.asInstanceOf[Assign].x)
    val x0 = m(assgnList.dropRight(1).last.asInstanceOf[Assign].x)

    val ax = ElidingProvable(Provable.implicitFuncAxiom(f))

    val pr = proveBy(
      Equal(FuncOf(f,t0),x0),
      commuteEqual(1) & useAt(ax)(1) & chase(1) &
      arbs.foldLeft(skip:BelleExpr)((tac,trm) => tac & existsR(trm)(1)) &
      allR(1) & implyR(1) &
      allR(1) & implyR(1) & orR(1) & hideR(1) & ODELiveness.dDX(1) & prop
    )

    pr
  }

  lazy val forallFwdBack : Lemma =
    remember("\\forall x P(x) <-> \\forall x (x = f() -> [{x'=1}++{x'=-1}]P(x))".asFormula,
      equivR(1) <(
        allR(1) & implyR(1) & abstractionb(1) & id,
        allR(1) & boundRename(Variable("x"),Variable("y"))(-1) &
          cut("\\exists y y = f()".asFormula) <(
            existsL(-2) & allL(-1) & implyL(-1) <(
              id,
              cut("x = f() | x > f() | x < f()".asFormula) <(
                orL(-3) <(
                  choiceb(-1) & andL(-1) & useAt(Ax.DX)(-3) & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & prop, //QE,
                  orL(-3) <(
                    cut("<{y'=1}>P(x)".asFormula) <(
                      cohideOnlyL(-4) & diamondd(-1) & notL(-1) & V(2) & prop,
                      hideR(1) & cutR("<{y'=1}>y=x".asFormula)(1) <(
                        hideL(-1) & ODELiveness.kDomainDiamond("y>=x".asFormula)(1) <(
                          ODELiveness.dV(None)(1) & QE,
                          ODEInvariance.dCClosure(1) <(
                            QE,
                            dW(1) & QE
                          )
                        ),
                        useAt(Ax.Kd,PosInExpr(1::Nil))(1) & choiceb(-1) & andL(-1) & cohideOnlyL(-3) & monb &
                          implyR(1) & exhaustiveEqL2R(-2) & prop
                      )
                    ),
                    cut("<{y'=-1}>P(x)".asFormula) <(
                      cohideOnlyL(-4) & diamondd(-1) & notL(-1) & V(2) & prop,
                      hideR(1) & cutR("<{y'=-1}>y=x".asFormula)(1) <(
                        hideL(-1) & ODELiveness.kDomainDiamond("y<=x".asFormula)(1) <(
                          ODELiveness.dV(None)(1) & QE,
                          ODEInvariance.dCClosure(1) <(
                            QE,
                            dW(1) & QE
                          )
                        ),
                        useAt(Ax.Kd,PosInExpr(1::Nil))(1) & choiceb(-1) & andL(-1) & cohideOnlyL(-4) & monb &
                          implyR(1) & exhaustiveEqL2R(-2) & prop
                      )
                    ),
                  ),
                ),
                cohideR(2) & QE
              )
            ),
            cohideR(2) & QE
          )
      ),
    namespace
  )

  lazy val forallFwdBackDirect : Lemma =
    remember("\\forall x_ (x_ = f() -> [{x_'=1}++{x_'=-1}]P(x_)) -> P(g())".asFormula,
      useAt(forallFwdBack,PosInExpr(1::Nil))(1,0::Nil) & implyR(1) & allL("g()".asTerm)(-1) & prop,
      namespace
    )

  // Helper to prove a property (typically of a user-provided interpreted function) by unfolding it into a differential equation proof
  // todo: decide what to pass as arguments

  @Tactic(names="propDiffUnfold",
    codeName="propDiffUnfold",
    premises="Γ |- P(t0), Δ ;; Γ, v=t0 |- [v'=1]P(v), Δ ;; Γ, v=t0 |- [v'=-1]P(v), Δ",
    conclusion="Γ |- P(v), Δ",
    displayLevel="browse")
  def propDiffUnfold(v:Term, t0: Term) : DependentPositionWithAppliedInputTactic = inputanon {(pos: Position, seq:Sequent) => {
    require(pos.isSucc && pos.isTopLevel, "differential equation unfolding only at top-level succedent")

    val fml = seq.sub(pos) match {
      case Some(e: Formula) => e
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    // Convenience rename if we happen to find a variable
    val targetVar = v match {
      case vv: Variable => vv
      case _ => Variable("x_")
    }

    val expAx = forallFwdBackDirect.fact(URename(targetVar, Variable("x_")))(USubst(List(SubstitutionPair("f()".asTerm, t0), SubstitutionPair("g()".asTerm, v))))

    useAt(expAx, PosInExpr(1 :: Nil))(pos) &
      allR(pos) & implyR(pos) &
      // Makes subsequent ODE proofs easier by proving the postcondition already true initially
      cutR(fml.replaceFree(v, targetVar))(pos) < (
        exhaustiveEqL2R('Llast) & hideL('Llast), //Rewrite the initial value x=0
        implyR(pos) &
          choiceb(pos) & andR(pos)
      )
  }}

}
