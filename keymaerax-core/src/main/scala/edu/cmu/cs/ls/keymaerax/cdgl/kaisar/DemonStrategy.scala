/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Interfaces for Demon strategies, both high-level and low-level
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
//import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Play.number
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, DifferentialSymbol}

class DemonException(val msg: String) extends Exception (msg)

/** Interface for drivers implementing Demon strategies / implementing an environment or hardware/simulation platform
  * @see [[BasicDemonStrategy]] */
trait DemonStrategy[T] {
  // NodeID is used to allow demon strategy to determine which statement is being executed.
  // We use integer IDs rather than passing the actual AST node so that the same DemonStrategy interface
  // would work as foreign-function interface for low-level languages, where we wish to pass only basic types.
  type NodeID = Int
  /** Hook for any additional initialization */
  def init(stringArg:Option[String] = None, intArgs: List[Int] = List()): Unit = ()
  def exit(): Unit = ()
  /** @return whether the driver wishes to continue executing the given loop */
  def readLoop(id: NodeID): Boolean
  /** @return whether the driver wishes to take the right branch of the given choice */
  def readChoice(id: NodeID): Boolean
  /** @return the numeric value the driver wishes to assign to [[x]] */
  def readAssign(id: NodeID, x: Ident): T
  /** Hook to perform actuation, reports fact that Angel assigned x:=f  */
  def writeAssign(id: NodeID, x: Ident, f: T): Unit
  def reportViolation(): Unit
}

/** Wrappable interface for Demon strategies. While this interface is not "simpler" than [[DemonStrategy]],
  * it is designed to work seamlessly with the output of [[SimpleStrategy.apply]]. i.e., if you wish to write a raw
  * [[DemonStrategy]], you will have to be familiar with the [[SimpleStrategy.apply]] implementation, but not if you
  * write [[BasicDemonStrategy]].
  * Also simplifies initial-state computation.
  * @see [[DemonStrategy]]
  * @see WrappedDemonStrategy*/
trait BasicDemonStrategy[number <: Numeric[number, Ternary]] {
  type NodeID = Int
  val env: Environment[number]
  val readInitState: Map[Ident, number]
  def readDemonLoop(id: NodeID): Boolean
  def readDemonChoice(id: NodeID): Boolean
  // @TODO: Should there be separate function for ODE? Yes.
  def readDemonAssign(id: NodeID, baseVar: String, varIndex: Option[Int]): number
  def writeAngelAssign(id: NodeID, baseVar: String, varIndex: Option[Int], value: number): Unit
  def reportViolation(): Unit
  def init(stringArg: Option[String], intArgs:List[Int]): Unit
  def exit(): Unit
  /** Get the current value for variable [[x]], initializing if necessary */
  def valFor(x: Ident): number = {
    if (env.contains(x)) env.get(x)
    else  {
      val v = readInitState(x)
      //println(s"Wrapper valFor read-assigned $x -> $v")
      env.set(x, v)
      v
    }
  }
}

/** Produces an executable [[DemonStrategy]] from high-level [[BasicDemonStrategy]] interface, fit for use with
  * [[SimpleStrategy.apply]]. The major contribution is that [[WrappedDemonStrategy]] automatically remembers the Angelic choices from
  * the ambient Angelic strategy, and makes Demon simulate those Angelic choices automatically, leaving you to implement
  * only the true Demon operations.
  * */
class WrappedDemonStrategy[number <: Numeric[number, Ternary]] (bds: BasicDemonStrategy[number])(val env: Environment[number]) extends DemonStrategy[number] {
  val initState: Map[Ident, number] = bds.readInitState
  override def reportViolation(): Unit = bds.reportViolation()
  override def readLoop(id: NodeID): Boolean =
    (IDCounter.getOriginal(id), IDCounter.get(id)) match {
      case (Some(ALoop(conv, body)), _) =>
        env.holds(conv) == KnownTrue() // if formula holds, continue
      case (Some(AForLoop(idx, idx0, conv, body, inc, guardEpsilon)), _) =>
        env.holds(conv) == KnownTrue() // if formula holds, continue
      case (Some(_), _) => throw new DemonException("Demon expected to be given loop, but was not. Are you playing an angel strategy against an incompatible Demon?")
      case (None, Some(SLoop(_body))) => bds.readDemonLoop(id)
      case (None, _) => throw new DemonException("Demon expected to be given loop, but was not. Are you playing an angel strategy against an incompatible Demon?")
    }

  override def readChoice(id: NodeID): Boolean =
    (IDCounter.getOriginal(id), IDCounter.get(id)) match {
      case (Some(ASwitch((fml, as) :: _right :: _)), _) =>
        env.holds(fml) != KnownTrue() // return value true ==> go right, so go left when formula is true or unknown
      case (Some(_), _) => throw new DemonException("Demon expected to be given choice, but was not. Are you playing an angel strategy against an incompatible Demon?")
      case (None, Some(SChoice(l, r))) => bds.readDemonChoice(id)
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
  override def init(stringArg: Option[String], intArgs:List[Int]): Unit = bds.init(stringArg, intArgs)
  override def exit(): Unit = bds.exit()
}