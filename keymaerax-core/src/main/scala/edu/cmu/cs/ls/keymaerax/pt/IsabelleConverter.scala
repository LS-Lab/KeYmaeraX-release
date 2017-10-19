package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._


class IsabelleConverter {
  type ID = String
  type Isequent = (List[Iformula],List[Iformula])
  type Irule = (List[Isequent],Isequent)

  case class IRat(num:Number,den:Number)

  sealed trait Itrm {}
  case class IVar(id:ID) extends Itrm {}
  case class IConstr(rat:IRat) extends Itrm {}
  case class IFunction(f:ID, args:List[Itrm]) extends Itrm {}
  case class IPlus(left:Itrm, right:Itrm) extends Itrm {}
  case class ITimes(left:Itrm, right:Itrm) extends Itrm {}
  case class IDiffVar(child:Itrm, right:Itrm) extends Itrm {}
  case class IDifferential(child:Itrm, right:Itrm) extends Itrm {}

  sealed trait IODE {}
  case class IOVar(id:ID) extends IODE {}
  case class IOSing(x:ID, t:Itrm) extends IODE {}
  case class OProd(left:IODE,right:IODE) extends IODE {}

  sealed trait Ihp {}
  case class IPvar(id:ID) extends Ihp {}
  case class IAssign(id:ID, t:Itrm) extends Ihp {}
  case class IDiffAssign(id:ID, t:Itrm) extends Ihp {}
  case class ITest(child:Iformula) extends Ihp {}
  case class IEvolveODE(ode:IODE, con:Iformula) extends Ihp {}
  case class IChoice(left:Ihp,right:Ihp) extends Ihp {}
  case class ISequence(left:Ihp,right:Ihp) extends Ihp {}
  case class ILoop(child:Ihp) extends Ihp {}

  sealed trait Iformula {}
  case class IGeq(left:Itrm, right:Itrm) extends Iformula {}
  case class IProp(id:ID, args:List[Itrm]) extends Iformula {}
  case class INot(child:Iformula) extends Iformula {}
  case class IAnd(left:Iformula,right:Iformula) extends Iformula {}
  case class IExists(x:ID, child:Iformula) extends Iformula {}
  case class IDiamond(prog:Ihp, post:Iformula) extends Iformula {}
  case class IInContext(id:ID, child:Iformula) extends Iformula {}

  def apply(t:Term):Itrm = {
    ???
  }

  def apply(f:Formula):Iformula = {
   ???
  }

  def apply(o:DifferentialProgram):IODE = {
    ???
  }

  def apply(hp:Program):Ihp = {
    ???
  }

  def apply(seq:Sequent):Isequent = {
    ???
  }

  def apply(pr:Provable):Irule = {
    ???
  }
}
