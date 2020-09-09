package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Play.number
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, DifferentialSymbol}

class DemonException(val msg: String) extends Exception (msg)

trait DemonStrategy[T] {
  // NodeID is used to allow demon strategy to determine which statement is being executed.
  // We use integer IDs rather than passing the actual AST node so that the same DemonStrategy interface
  // would work as foreign-function interface for low-level languages, where we wish to pass only basic types.
  type NodeID = Int
  def init(): Unit = ()
  def readLoop(id: NodeID): Boolean
  def readChoice(id: NodeID): Boolean
  def readAssign(id: NodeID, x: Ident): T
  def writeAssign(id: NodeID, x: Ident, f: T): Unit
}

trait BasicDemonStrategy {
  type NodeID = Int
  val env: Environment
  val readInitState: Map[Ident, number]
  def readDemonLoop(id: NodeID): Boolean
  def readDemonChoice(id: NodeID): Boolean
  // @TODO: Should there be separate function for ODE
  def readDemonAssign(id: NodeID, baseVar: String, varIndex: Option[Int]): number
  def writeAngelAssign(id: NodeID, baseVar: String, varIndex: Option[Int], value: number): Unit

  def valFor(x: Ident): Play.number = {
    if (env.contains(x)) env.get(x)
    else  {
      val v = readInitState(x)
      //println(s"Wrapper valFor read-assigned $x -> $v")
      env.set(x, v)
      v
    }
  }
}

class WrappedDemonStrategy (bds: BasicDemonStrategy)(val env: Environment) extends DemonStrategy[number] {
  val initState: Map[Ident, number] = bds.readInitState
  override def readLoop(id: NodeID): Boolean =
    (IDCounter.getOriginal(id), IDCounter.get(id)) match {
      case (Some(ALoop(conv, body)), _) =>
        !env.holds(conv) // if formula holds, continue
      case (Some(_), _) => throw new DemonException("Demon expected to be given loop, but was not. Are you playing an angel strategy against an incompatible Demon?")
      case (None, Some(DLoop(_body))) => bds.readDemonLoop(id)
      case (None, _) => throw new DemonException("Demon expected to be given loop, but was not. Are you playing an angel strategy against an incompatible Demon?")
    }

  override def readChoice(id: NodeID): Boolean =
    (IDCounter.getOriginal(id), IDCounter.get(id)) match {
      case (Some(ASwitch((fml, as) :: _right :: _)), _) =>
        env.holds(fml) // if formula holds, left branch
      case (Some(_), _) => throw new DemonException("Demon expected to be given choice, but was not. Are you playing an angel strategy against an incompatible Demon?")
      case (None, Some(DChoice(l, r))) => bds.readDemonChoice(id)
      case (None, _) => throw new DemonException("Demon expected to be given choice, but was not. Are you playing an angel strategy against an incompatible Demon?")
    }

  override def readAssign(id: NodeID, x: Ident): number = {
    val base = x match {case bv: BaseVariable => BaseVariable(bv.name) case ds: DifferentialSymbol => DifferentialSymbol(BaseVariable(ds.name))}
    val name = base match {case bv: BaseVariable => bv.name case ds: DifferentialSymbol => ds.name + "'"}
    if (!env.contains(x) && initState.contains(base)) {
      //println(s"Wrapper read-assigned $x -> ${initState(x)}")
      env.set(x, initState(base))
      return initState(base)
    }
    val res = bds.readDemonAssign(id, name, x.index)
    //println(s"Wrapper star-assigned $base -> $res")
    env.set(base, res)
    res
  }

  override def writeAssign(id: NodeID, x: Ident, f: number): Unit = {
    val name = x match {case bv: BaseVariable => bv.name case ds: DifferentialSymbol => ds.name + "'"}
    val base = x match {case bv: BaseVariable => BaseVariable(bv.name) case ds: DifferentialSymbol => DifferentialSymbol(BaseVariable(ds.name))}
    IDCounter.getOriginal(id) match {
      case Some(_) => ()
      case _ =>
        bds.writeAngelAssign(id, name, x.index, f)
        env.set(base, f)
        env.set(x, f)
    }
  }
}