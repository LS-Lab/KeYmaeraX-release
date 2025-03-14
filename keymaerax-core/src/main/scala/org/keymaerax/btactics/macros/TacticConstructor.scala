/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

sealed trait TacticConstructor {
  def args: IndexedSeq[ArgInfo]

  /**
   * This method is supposed to type check and/or convert the input arguments based on the [[ArgInfo]]s provided when
   * the constructor was created. However, this will have to wait until the `@Tactic` macro no longer exists and all
   * related types can be moved to the core. Until then, the `ReflectiveExpressionBuilder` in the core will have to do
   * the type checking and conversion.
   */
  def construct(args: Seq[Any]): Any
}

final case class TacticConstructor0()(f: () => Any) extends TacticConstructor {
  override def args: IndexedSeq[ArgInfo] = IndexedSeq()
  override def construct(args: Seq[Any]): Any = {
    val Seq() = args
    f()
  }
}

object TacticConstructor0 {
  def create[R]()(f: () => R): TacticConstructor0 = TacticConstructor0()(f.asInstanceOf[() => Any])
}

final case class TacticConstructor1(arg1: ArgInfo)(f: Any => Any) extends TacticConstructor {
  override def args: IndexedSeq[ArgInfo] = IndexedSeq(arg1)
  override def construct(args: Seq[Any]): Any = {
    val Seq(val1) = args
    f(val1)
  }
}

object TacticConstructor1 {
  def create[A1, R](arg1: ArgInfo)(f: (A1) => R): TacticConstructor1 =
    TacticConstructor1(arg1)(f.asInstanceOf[Any => Any])
}

final case class TacticConstructor2(arg1: ArgInfo, arg2: ArgInfo)(f: (Any, Any) => Any) extends TacticConstructor {
  override def args: IndexedSeq[ArgInfo] = IndexedSeq(arg1, arg2)
  override def construct(args: Seq[Any]): Any = {
    val Seq(val1, val2) = args
    f(val1, val2)
  }
}

object TacticConstructor2 {
  def create[A1, A2, R](arg1: ArgInfo, arg2: ArgInfo)(f: (A1, A2) => R): TacticConstructor2 =
    TacticConstructor2(arg1, arg2)(f.asInstanceOf[(Any, Any) => Any])
}

final case class TacticConstructor3(arg1: ArgInfo, arg2: ArgInfo, arg3: ArgInfo)(f: (Any, Any, Any) => Any)
    extends TacticConstructor {
  override def args: IndexedSeq[ArgInfo] = IndexedSeq(arg1, arg2, arg3)
  override def construct(args: Seq[Any]): Any = {
    val Seq(val1, val2, val3) = args
    f(val1, val2, val3)
  }
}

object TacticConstructor3 {
  def create[A1, A2, A3, R](arg1: ArgInfo, arg2: ArgInfo, arg3: ArgInfo)(f: (A1, A2, A3) => R): TacticConstructor3 =
    TacticConstructor3(arg1, arg2, arg3)(f.asInstanceOf[(Any, Any, Any) => Any])
}

final case class TacticConstructor4(arg1: ArgInfo, arg2: ArgInfo, arg3: ArgInfo, arg4: ArgInfo)(
    f: (Any, Any, Any, Any) => Any
) extends TacticConstructor {
  override def args: IndexedSeq[ArgInfo] = IndexedSeq(arg1, arg2, arg3, arg4)
  override def construct(args: Seq[Any]): Any = {
    val Seq(val1, val2, val3, val4) = args
    f(val1, val2, val3, val4)
  }
}

object TacticConstructor4 {
  def create[A1, A2, A3, A4, R](arg1: ArgInfo, arg2: ArgInfo, arg3: ArgInfo, arg4: ArgInfo)(
      f: (A1, A2, A3, A4) => R
  ): TacticConstructor4 = TacticConstructor4(arg1, arg2, arg3, arg4)(f.asInstanceOf[(Any, Any, Any, Any) => Any])
}

final case class TacticConstructor10(
    arg1: ArgInfo,
    arg2: ArgInfo,
    arg3: ArgInfo,
    arg4: ArgInfo,
    arg5: ArgInfo,
    arg6: ArgInfo,
    arg7: ArgInfo,
    arg8: ArgInfo,
    arg9: ArgInfo,
    arg10: ArgInfo,
)(f: (Any, Any, Any, Any, Any, Any, Any, Any, Any, Any) => Any)
    extends TacticConstructor {
  override def args: IndexedSeq[ArgInfo] = IndexedSeq(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10)
  override def construct(args: Seq[Any]): Any = {
    val Seq(val1, val2, val3, val4, val5, val6, val7, val8, val9, val10) = args
    f(val1, val2, val3, val4, val5, val6, val7, val8, val9, val10)
  }
}

object TacticConstructor10 {
  def create[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, R](
      arg1: ArgInfo,
      arg2: ArgInfo,
      arg3: ArgInfo,
      arg4: ArgInfo,
      arg5: ArgInfo,
      arg6: ArgInfo,
      arg7: ArgInfo,
      arg8: ArgInfo,
      arg9: ArgInfo,
      arg10: ArgInfo,
  )(f: (A1, A2, A3, A4, A5, A6, A7, A8, A9, A10) => R): TacticConstructor10 =
    TacticConstructor10(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10)(
      f.asInstanceOf[(Any, Any, Any, Any, Any, Any, Any, Any, Any, Any) => Any]
    )
}
