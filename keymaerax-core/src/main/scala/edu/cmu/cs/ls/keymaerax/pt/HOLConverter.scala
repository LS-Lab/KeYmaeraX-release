package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

/** Converts kyx expressions to subset used by hol formalization.
  * Just different enough from Isabelle syntax that it's not so easy to unify them just yet.
  *
  * @author Brandon Bohrer*/
object HOLConverter {

  def apply(t:Term):String = {
    val c = '\"'
    t match {
      case Number(n) => s"(Const ${n.toIntExact}w)"
      //@todo: more robust please
      case FuncOf(Function(n,_,_,_,_),_) => s"(Var $c$n$c)"
      case BaseVariable(n,None,_) => s"(Var $c$n$c)"
      case BaseVariable(n,Some(i),_) => s"(Var $c${n}_$i$c)"
      case Plus(l,r) => s"(Plus ${apply(l)} ${apply(r)})"
      case Times(l,r) => s"(Times ${apply(l)} ${apply(r)})"
    }
  }

  //@todo not needed yet - FOL_R only so far
  def apply(dp:DifferentialProgram):String = {
    ???
  }

  //@todo not needed yet - FOL_R only so far
  def apply(p:Program):String = {
    ???
  }

  def apply(f:Formula):String = {
    f match {
      case And(p,q) => s"(And ${apply(p)} ${apply(q)})"
      case Or(p,q) => s"(Or ${apply(p)} ${apply(q)})"
      case Imply(p,q) => s"(Or ${apply(q)} (Not ${apply(p)}))"
      case Not(p) => s"(Not ${apply(p)})"
      case Equiv(p,q) => s"(Or (And ${apply(p)} ${apply(q)}) (And (Not ${apply(p)}) (Not ${apply(q)})))"
      case NotEqual(l,r) => s"(Not (And (Leq ${apply(l)} ${apply(r)}) (Leq ${apply(r)} ${apply(l)})))"
      case Equal(l,r) => s"(Equals ${apply(l)} ${apply(r)})"
      case LessEqual(l,r) => s"(Leq ${apply(l)} ${apply(r)})"
      case Less(l,r) => s"(And (Leq ${apply(l)} ${apply(r)}) (Not (Leq ${apply(r)} ${apply(l)})))"
      case Greater(l,r) => s"(And (Leq ${apply(r)} ${apply(l)}) (Not (Leq ${apply(l)} ${apply(r)})))"
      case GreaterEqual(l,r) => s"(Leq ${apply(r)} ${apply(l)})"

    }
  }

  def monitorFmlDef(f:Formula):String = {
    "val monitor_fml = ``" + apply(f) + "`` |> (DEPTH_CONV wordsLib.WORD_GROUND_CONV) |> rconc;;"
  }
}
