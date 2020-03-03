package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.cdgl.Proof._
import edu.cmu.cs.ls.keymaerax.core._
import scala.collection.immutable



object Proof {
  // de Bruijn indices
  type ProofVariable = Int
}

final case class Context(c:List[Formula]) {
  def asIndexedSeq: immutable.IndexedSeq[Formula] =
    c.to[immutable.IndexedSeq]
  def asSequent: Sequent = Sequent(this.asIndexedSeq, immutable.IndexedSeq())
  def entails(f:Formula): Sequent = {
    new Sequent(c.toIndexedSeq, immutable.IndexedSeq(f))
  }
  def rename(what: Variable, repl: Variable): Context = {
    Context.ofSequent(UniformRenaming(what,repl)(this.asSequent).head)
  }
  def extend(P:Formula): Context = {
    Context(P :: c)
  }
  def apply(p:ProofVariable): Formula = c(p)
}
object Context {
  def ofSequent(seq: Sequent): Context = {
    Context(seq.ante.toList)
  }
}

final case class Judgement(ante: Context, succ: Formula) {}

sealed trait Proof {}

/*                 *
 *  -------------------------------
 *   G |-  (): True
 */
case class Triv() extends Proof {}

/* G |- M: P   G |- N: Q
 * ----------------------------------------------
 * G |- <M,N>: <?P>Q
 */
case class DTestI(left: Proof, right: Proof) extends Proof {}

/* G |- M: <?P>Q
 * ----------------------------------------------
 * G |- piL(M): P
 */
case class DTestEL(child: Proof) extends Proof {}

/* G |- M: <?P>Q
 * ----------------------------------------------
 * G |- piR(M): Q
 */
case class DTestER(child: Proof) extends Proof {}

/* G_x^y, p:(x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- <x:=f_x^y in p. M> : <x:=f>P
 */
case class DAssignI(e:Assign, y:Variable, child: Proof) extends Proof {}

/* G |- M: <x:=f>p(x)
 * ----------------------------------------------
 * G |- <:=^-1>(M): p(f)
 */
case class DAssignE(e:Assign, child: Proof) extends Proof {}

/* G_x^y, p:(x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- <x :* f_x^y in p. M> : <x:=*>P
 */
case class DRandomI(e:Assign, y:Variable, child: Proof) extends Proof {}

/* G |- M: <x:=f>p(x)   G_x^y, p(x) |- N: Q
 * ----------------------------------------------
 * G |-  (unpack_x^y = M in N) : Q
 */
case class DRandomE(x:Variable, y:Variable, left: Proof, right: Proof) extends Proof {}

/* G |- M: <a><b>P
 * ----------------------------------------------
 * G |- <i M>: <a;b>P
 */
case class DComposeI(child: Proof) extends Proof {}

/* G |- M: <a;b>P
 * ----------------------------------------------
 * G |- <i^-1 M>: <a><b>P
 */
case class DComposeE(child: Proof) extends Proof {}

/* G |- M: <a>P
 * ----------------------------------------------
 * G |- injL[b](M): <a++b>P
 */
case class DChoiceIL(other:Program, child: Proof) extends Proof {}

/* G |- M: <b>P
 * ----------------------------------------------
 * G |- injR[a](M): <a++b>P
 */
case class DChoiceIR(other:Program, child: Proof) extends Proof {}

/* G |- A: <a++b>P   G,l:<a>P |- B:Q   G,r:<b>P |- C:Q
 * ----------------------------------------------
 * G |- (case A of l=>B | r=>C): Q
 */
case class DChoiceE(child:Proof, left:Proof, right:Proof) extends Proof {}

/* G |- M: P
 * ----------------------------------------------
 * G |- stop[a](M): <a*>P
 */
case class DStop(a:Program,child: Proof) extends Proof {}

/* G |- M: <a><a*>P
 * ----------------------------------------------
 * G |- (go M): <a*>P
 */
case class DGo(child: Proof) extends Proof {}
// TODO: Less args. Variant unnecessary

/* G |- A:J   m:met0=met>metz,v:J |- <a>(J & met<metz)  m:met=metz,v:J |- Q
 * ------------------------------------------------------------------------
 * G |- for_{met,metz}(A;mv.B;C): <a*>Q
 */
case class DRepeatI(metric: Term, metz:Term, mx:BaseVariable, init: Proof, step: Proof, post: Proof) extends Proof {}
// FP

/* G |- A: <a*>P   x:P |- B: Q   x:<a>Q |- C:Q
 * ----------------------------------------------
 * G |- FP(A,x.B,x.C): Q
 */
case class DRepeatE(child: Proof, post: Proof, step: Proof) extends Proof {}

/* G |- M: [a]P
 * ----------------------------------------------
 * G |- yield M: <a^d>P
 */
case class DDualI(child: Proof) extends Proof {}

/* G |- M: <a^d>P
 * ----------------------------------------------
 * G |- (yield^-1 M): [a]P
 */
case class DDualE(child: Proof) extends Proof {}

/* G_xs^ys, 0<=s<=dur |- M: Q_xs^sol(s)   G_xs^ys, 0<=dur |- N: P_xs^sol(dur)
 * ----------------------------------------------  sol solves x'=f&Q on [0,dur], s and t fresh
 * G |- DS[x'=f&Q,ys,sol,dur,s](M,N): <x'=f&Q>P
 */
case class DSolve(ode:ODESystem, ys:List[Variable],sol:List[Term], dur:Term, s:Variable, t:Variable, dc:Proof, post:Proof) extends Proof {}

/* G |- A: d>0 & v>0 & f-g >= -dv
 * G |- B: <t:=0><x'=f,t'=1&Q>t>=d
 * G |- C: [x'=f&Q](f'-g' >= eps)
 * f>= g |- D: P
 * ---------------------------------------------- d,v constant
 * G |- DV[f,g,d,eps,v](A,B,C,D): <x'=f&Q>P
 */
case class DV(f:Term, g:Term, d:Term, const:Proof, dur:Proof, rate:Proof, post:Proof) extends Proof {}

/* G, x:P |- M:Q
 * ----------------------------------------------
 * G |- (fn x:P => M): [?P]Q
 */
case class BTestI(p:ProofVariable, fml:Formula, child:Proof) extends Proof {}

/* G |- M: [?P]Q   G|- N:P
 * ----------------------------------------------
 * G |- (M N): Q
 */
case class BTestE(left:Proof, right:Proof) extends Proof {}

/* G_x^y, p:(x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- [x:=f_x^y in p. M] : [x:=f]P
 */
case class BAssignI(e:Assign, y:Variable, child: Proof) extends Proof {}

/* G |- M: [x:=f]p(x)
 * ----------------------------------------------
 * G |- [:=^-1](M): p(f)
 */
case class BAssignE(e:Assign, child: Proof) extends Proof {}

/* G |- G_x^y |- M:P
 * ----------------------------------------------
 * G |- (fn x^y => M): [x:=*]P
 */
case class BRandomI(x:Variable, y:Variable, child: Proof) extends Proof {}

/* G |- M: [x:=*]p(x)
 * ----------------------------------------------
 * G |- (M f): p(f)
 */
case class BRandomE(child: Proof, f:Term) extends Proof {}

/* G |- M: [a][b]P
 * ----------------------------------------------
 * G |- [i M]: [a;b]P
 */
case class BComposeI(child: Proof) extends Proof {}

/* G |- M: [a;b]P
 * ----------------------------------------------
 * G |- [i M]: [a][b]P
 */
case class BComposeE(child: Proof) extends Proof {}

/* G |- M: [a]P   G |- N: [b]P
 * ----------------------------------------------
 * G |- [M,N]: [a++b]P
 */
case class BChoiceI(left: Proof, right: Proof) extends Proof {}

/* G |- M: [a++b]P
 * ----------------------------------------------
 * G |- projL(M): [a]P
 */
case class BChoiceEL(child: Proof) extends Proof {}

/* G |- M: [a++b]P
 * ----------------------------------------------
 * G |- projR(M): [b]P
 */
case class BChoiceER(child: Proof) extends Proof {}

/* G |- A: J   G_xs^ys,x:J |- B: [a]J   G_xs^ys,x:J |- C:Q
 * ---------------------------------------------------------
 * G |- (A rep[ys] x:J. B in C): [a*]Q
 */
case class BRepeatI(pre: Proof, step: Proof, post: Proof) extends Proof {}

/* G |- M: [a*]P
 * ----------------------------------------------
 * G |- projL(M): P
 */
case class BRepeatEL(child: Proof) extends Proof {}

/* G |- M: [a*]P
 * ----------------------------------------------
 * G |- projR(M): [a][a*]P
 */
case class BRepeatER(child: Proof) extends Proof {}

/* G |- M: <a>P
 * ----------------------------------------------
 * G |- [yield M]: [a^d]P
 */
case class BDualI(child: Proof) extends Proof {}

/* G |- M: [a^d]P
 * ----------------------------------------------
 * G |- [yield^-1 M]: <a>P
 */
case class BDualE(child: Proof) extends Proof {}

/*  G_xs^ys, 0<=t, (\forall 0<=s<=t, Q_xs^sol(dur)) |- N: P_xs^sol(dur)
 * --------------------------------------------------------------------  sol solves x'=f&Q on [0,dur], s and t fresh
 * G |- BS[x'=f&Q,ys,sol,t,s](M,N): [x'=f&Q]P
 */
case class BSolve(ode:ODESystem, ys:List[Variable], sols:List[Term], s:Variable, t:Variable, dc:ProofVariable, post:Proof) extends Proof {}


/* G_xs^ys, x:Q |- M: P
 * ----------------------------------------------
 * G |- DW[ys](x.M): [x'=f & Q]P
 */
case class DW(ode:ODESystem, child: Proof) extends Proof {}

/* G |- M:[x'=f&Q]R   G |- N:[x'=f&(Q&R)]P
 * ----------------------------------------------
 * G |- DC(M,N): [x'=f&Q]P
 */
case class DC(inv: Formula, left: Proof, right: Proof) extends Proof {}

/* G |- M: P   G_xs^ys |- N: (P)'_x'^f
 * ----------------------------------------------
 * G |- DI(M,N): [x'=f & Q]P
 */
case class DI(pre: Proof, step: Proof) extends Proof {}

/* G, y=y0 |- M: [x'=f,y'=a(y)+b&Q]P
 * ----------------------------------------------
 * G |- DG[y,y0,a,b](M): [x'=f]P
 */
case class DG(y: Variable, y0: Term, a: Term, b:Term, child: Proof) extends Proof {}



/* G_x^y |- M:P
 * ----------------------------------------------
 * G |- (fn x^y => M): (\forall x, P)
 */
case class ForallI(x:Variable, y:Variable, child: Proof) extends Proof {}

/* G |- M: (\forall x, p(x))
 * ----------------------------------------------
 * G |- (M f): p(f)
 */
case class ForallE(child: Proof, f:Term) extends Proof {}


/* G_x^y, p:(x=f_x^y) |- M: P
 * ----------------------------------------------
 * G |- <x = f_x^y in p. M> : \exists x, P
 */
case class ExistsI(e:Assign, y:Variable, pchild: Proof) extends Proof {}

/* G |- M: (exists x, p(x))   G_x^y, p(x) |- N: Q
 * ----------------------------------------------
 * G |- (unpack_x^y = M in N) : Q
 */
case class ExistsE(x:Variable, y:Variable, left: Proof, right: Proof) extends Proof {}

/* G |- M: P   G |- N:Q
 * ----------------------------------------------
 * G |- (M,N): P & Q
 */
case class AndI(left: Proof, right: Proof) extends Proof {}

/* G |- M: P & Q
 * ----------------------------------------------
 * G |- projL(M): P
 */
case class AndEL(child: Proof) extends Proof {}

/* G |- M: P & Q
 * ----------------------------------------------
 * G |- projR(M): Q
 */
case class AndER(child: Proof) extends Proof {}

/* G |- M: P
 * ----------------------------------------------
 * G |- injL[Q](M): P | Q
 */
case class OrIL(other: Formula, child: Proof) extends Proof {}

/* G |- M: Q
 * ----------------------------------------------
 * G |- injR[P](M): P | Q
 */
case class OrIR(other: Formula, child: Proof) extends Proof {}

/* G |- A:(P|Q)   G,l:P |- B:R    G,r:Q |- C:R
 * ----------------------------------------------
 * G |- (case A of l=>B | r=>C): R
 */
case class OrE(child:Proof, left:Proof, right:Proof) extends Proof {}

/* G,x:P |- M:Q
 * ----------------------------------------------
 * G |- (fn x:P => M): (P -> Q)
 */
case class ImplyI(fml:Formula, child:Proof) extends Proof {}

/* G |- M: (P -> Q)   G |- N: P
 * ----------------------------------------------
 * G |- (M N): Q
 */
case class ImplyE(left:Proof, right:Proof) extends Proof {}

/* G,x:P |- M: Q   G,x:Q |- N:P
 * ----------------------------------------------
 * G |- (M,N)[x:P,Q]
 */
case class EquivI(fml:Equiv, left:Proof, right:Proof) extends Proof {}

/* G |- M: (P <-> Q)   G |- N: P
 * ----------------------------------------------
 * G |- (projL(M) N): Q
 */
case class EquivEL(child:Proof, assump:Proof) extends Proof {}

/* G |- M: (P <-> Q)   G |- N: Q
 * ----------------------------------------------
 * G |- (projR(M) N): P
 */
case class EquivER(child:Proof, assump:Proof) extends Proof {}

/* G, x:P |- M: False
 * ----------------------------------------------
 * G |- (fn x:P => M): !P
 */
case class NotI(p:Formula, child:Proof) extends Proof {}

/* G |- M: !P   G |- N: P
 * ----------------------------------------------
 * G |- (M N): False
 */
case class NotE(left:Proof, right:Proof) extends Proof {}

/*       *
 * ----------------------------------------------
 * G,x:P |- x:P
 */
case class Hyp(p:ProofVariable) extends Proof {}


/* G |- M: [a]J   G_xs^ys, x:J |- N:Q
 * ----------------------------------------------
 * G |-  (M o x:J. N)[ys] : [a]Q
 */
case class Mon(left: Proof, right: Proof) extends Proof {}

/* G |- M: Q
 * ---------------------------------------------- (Q -> P is valid first-order arithmetic)
 * G |- QE[P](M) : P
 */
case class QE(p:Formula, child: Proof) extends Proof {}
