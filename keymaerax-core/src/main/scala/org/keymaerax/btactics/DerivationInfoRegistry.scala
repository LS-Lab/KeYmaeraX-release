/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import io.github.classgraph.ClassGraph
import org.keymaerax.bellerophon.*
import org.keymaerax.btactics.macros.*
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.{Configuration, Logging}

import java.lang.reflect.{Field, InvocationTargetException}
import scala.annotation.{nowarn, tailrec}
import scala.language.implicitConversions

/**
 * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics) with meta information of relevant
 * names and display names and visualizations for the user interface.
 */
object DerivationInfoRegistry extends Logging {
  import scala.language.implicitConversions

  @nowarn("msg=match may not be exhaustive")
  def convert(arg: ArgInfo, exprs: List[Expression]): Either[Any, String] = {
    (arg, exprs) match {
      case (_: NumberArg, (v: Number) :: Nil) => Left(v)
      case (_: NumberArg, v :: Nil) => Right("Expected a number but got " + v.prettyString)
      case (_: VariableArg, (v: Variable) :: Nil) => Left(v)
      case (_: VariableArg, v :: Nil) => Right("Expected a variable but got " + v.prettyString)
      case (_: TermArg, (t: Term) :: Nil) => Left(t)
      case (_: TermArg, t :: Nil) => Right("Expected a term but got " + t.prettyString)
      case (_: FormulaArg, (f: Formula) :: Nil) => Left(f)
      case (_: FormulaArg, f :: Nil) => Right("Expected a formula but got " + f.prettyString)
      case (_: ExpressionArg, (e: Expression) :: Nil) => Left(e)
      case (_: ExpressionArg, e :: Nil) => Right("Expected an expression but got " + e.prettyString)
      case (ListArg(ai: ArgInfo), fmls) if fmls.forall(_.kind == FormulaKind) =>
        val res = fmls.map(e => convert(ai, List(e)))
        res.find({
          case _: Left[Any, String] => false
          case _: Right[Any, String] => true
        }) match {
          case Some(Right(err)) => Right(err)
          case None => Left(res.map({ case Left(v) => v }))
        }
      case _ => Right(
          "Expected: " + arg.sort + ", found: " + exprs.map(_.kind).mkString(",") + " " +
            exprs.map(_.prettyString).mkString(",")
        )
    }
  }

  /** Locate the derivation info for said tactic */
  @tailrec
  def locate(t: BelleExpr): Option[DerivationInfo] = t match {
    case n: NamedBelleExpr =>
      try { Some(DerivationInfo.ofCodeName(n.name)) }
      catch { case _: Exception => None }
    case AppliedPositionTactic(n, _) => locate(n)
    case AppliedBuiltinTwoPositionTactic(n, _, _) => locate(n)
    // @todo probably more cases
    case _ => None
  }

  /** Evaluate the field of a Scala object and register it with the global [[DerivationInfo]] object. */
  private def registerDerivationFromField(clazz: Class[_], instance: AnyRef, field: Field): Unit = {
    // Val fields are private but have public getter functions of the same name.
    val getter = clazz.getMethod(field.getName)

    // Exceptions that occur during reflection are wrapped in an InvocationTargetException.
    // We unwrap and rethrow so from the outside it looks like we just evaluated the derivation normally.
    val valueAny =
      try { getter.invoke(instance) }
      catch { case e: InvocationTargetException => throw e.getCause }

    val value = valueAny.asInstanceOf[DerivationInfo]
    DerivationInfo.register(value)
  }

  /**
   * Find and register all fields of a Scala object which are marked with the [[Derivation]] annotation.
   *
   * @return
   *   A list of fields that failed to initialize and register, along with the cause.
   */
  private def registerDerivationsFromObject(clazz: Class[?]): Seq[String] = {
    // An object's instance can be located through its public static final MODULE$ field.
    val moduleField =
      try clazz.getField("MODULE$")
      catch {
        case _: NoSuchFieldException =>
          val className = clazz.getName
          val annotationName = classOf[Derivation].getSimpleName
          return Seq(s"$className is not a Scala object, but it contains @$annotationName annotations")
      }

    // We pass null since the field is static.
    val instance = moduleField.get(null)

    clazz
      .getDeclaredFields
      .toSeq
      .filter(_.isAnnotationPresent(classOf[Derivation]))
      .flatMap(field =>
        try {
          registerDerivationFromField(clazz, instance, field)
          None
        } catch {
          case t: Throwable =>
            val className = field.getDeclaringClass.getName
            val fieldName = field.getName

            if (Configuration.getBoolean(Configuration.Keys.DEBUG).getOrElse(false)) {
              // For debugging, the stack trace might be useful.
              println()
              println(s"Error while registering (in $className) $fieldName: $t")
              t.printStackTrace(System.out)
            }

            Some(s"Error while registering (in $className) $fieldName")
        }
      )
  }

  /**
   * Find and register all fields marked with the [[Derivation]] annotation globally. The fields must be Scala object
   * fields, and they must be of type [[DerivationInfo]].
   *
   * This function is implemented without using the Scala 2 reflection API. Hopefully this will make it easier to
   * upgrade to Scala 3 later.
   *
   * @return
   *   A list of fields that failed to initialize and register, along with the cause.
   */
  private def registerDerivationsGlobally(): Seq[String] = {
    import scala.jdk.CollectionConverters.*
    new ClassGraph()
      .enableAllInfo()
      .scan()
      .getClassesWithFieldAnnotation(classOf[Derivation])
      .asScala
      .toSeq
      .flatMap(info => registerDerivationsFromObject(info.loadClass()))
  }

  /** Has the global DerivationInfo list been initialized? */
  def isInit: Boolean = DerivationInfo._allInfo.nonEmpty

  /**
   * Initialize global DerivationInfo list. This is surprisingly tricky because DerivationInfo is attached to tactic
   * (and axiom and rule) definitions, which are scattered throughout the prover. Here we maintain a global list of
   * files that can contain @Tactic definitions. Those classes are reflected and all annotated definitions are
   * evaluated. Having been modified by the @Tactic macro, those definitions all contain a function call which adds
   * their TacticInfo object to the global list. While this process does not require evaluating tactics in full, it does
   * require loading a number of classes, which triggers their static initializers and thus requires some attention to
   * initialization order.
   *
   * @return
   *   a list of errors encountered during initialization
   */
  def init(initLibrary: Boolean = true): Seq[String] = {
    // Initialization is relatively slow, so only initialize once
    if (isInit) return Nil

    // Remember that initialization is in progress,
    DerivationInfo._initStatus = DerivationInfo.InitInProgress
    if (!initLibrary) return Nil // Advanced use - user takes over in-progress initialization

    try registerDerivationsGlobally()
    finally DerivationInfo._initStatus = DerivationInfo.InitComplete
  }
}
