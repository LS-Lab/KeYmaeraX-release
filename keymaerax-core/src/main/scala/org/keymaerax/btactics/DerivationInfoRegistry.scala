/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import io.github.classgraph.ClassGraph
import org.keymaerax.Logging
import org.keymaerax.bellerophon.*
import org.keymaerax.btactics.macros.*
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation

import java.lang.reflect.{Field, InvocationTargetException, Method}
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
    case n: NamedBelleExpr => try { Some(DerivationInfo.ofCodeName(n.name)) } catch { case _: Exception => None }
    case AppliedPositionTactic(n, _) => locate(n)
    case AppliedBuiltinTwoPositionTactic(n, _, _) => locate(n)
    // @todo probably more cases
    case _ => None
  }

  /** Evaluate the method of a Scala object and register it with the global [[DerivationInfo]] object. */
  private def registerDerivationFromMethod(clazz: Class[?], instance: AnyRef, method: Method): Unit = {
    // Exceptions that occur during reflection are wrapped in an InvocationTargetException.
    // We unwrap and rethrow so from the outside it looks like we just evaluated the derivation normally.
    val valueAny = try { method.invoke(instance) } catch { case e: InvocationTargetException => throw e.getCause }

    val value = valueAny.asInstanceOf[DerivationInfo]
    DerivationInfo.register(value)
  }

  /** Evaluate the field of a Scala object and register it with the global [[DerivationInfo]] object. */
  private def registerDerivationFromField(clazz: Class[?], instance: AnyRef, field: Field): Unit = {
    // Lazy vals are named something$lzy1 or similar by the compiler.
    // They have a getter function with the original name that is also annotated.
    // We collect annotated methods separately, so we can just skip here.
    if (field.getName.contains('$')) return

    // Val fields are private but have public getter functions of the same name.
    val getter = clazz.getMethod(field.getName)

    registerDerivationFromMethod(clazz, instance, getter)
  }

  private def tryRegistering(clazz: Class[?], name: String, op: => Unit): Option[String] =
    try {
      op
      None
    } catch {
      case t: Throwable =>
        val className = clazz.getDeclaringClass.getName
        // For debugging, the stack trace might be useful.
        logger.debug(s"Error while registering (in $className) $name", t)
        Some(s"Error while registering (in $className) $name")
    }

  /**
   * Find and register all fields of a Scala object which are marked with the [[Derivation]] annotation.
   *
   * @return A list of fields that failed to initialize and register, along with the cause.
   */
  private def registerDerivationsFromObject(clazz: Class[?]): Seq[String] = {
    // An object's instance can be located through its public static final MODULE$ field.
    val moduleField =
      try clazz.getField("MODULE$")
      catch {
        case _: NoSuchFieldException =>
          // When annotating objects, the corresponding class fields are also annotated.
          // So we just ignore anything that's not a Scala object.
          return Seq()
      }

    // We pass null since the field is static.
    val instance = moduleField.get(null)

    val methodErrors = clazz
      .getDeclaredMethods
      .toSeq
      .filter(_.isAnnotationPresent(classOf[Derivation]))
      .flatMap(method => tryRegistering(clazz, method.getName, registerDerivationFromMethod(clazz, instance, method)))

    val fieldErrors = clazz
      .getDeclaredFields
      .toSeq
      .filter(_.isAnnotationPresent(classOf[Derivation]))
      .flatMap(field => tryRegistering(clazz, field.getName, registerDerivationFromField(clazz, instance, field)))

    methodErrors ++ fieldErrors
  }

  /**
   * Find and register all fields marked with the [[Derivation]] annotation globally. The fields must be Scala object
   * fields, and they must be of type [[DerivationInfo]].
   *
   * This function is implemented without using the Scala 2 reflection API. Hopefully this will make it easier to
   * upgrade to Scala 3 later.
   *
   * @return A list of fields that failed to initialize and register, along with the cause.
   */
  private def registerDerivationsGlobally(): Seq[String] = {
    import scala.jdk.CollectionConverters.*
    val scan = new ClassGraph().enableAllInfo().scan()
    val withFieldAnnotation = scan.getClassesWithFieldAnnotation(classOf[Derivation]).asScala.toSet
    val withMethodAnnotation = scan.getClassesWithMethodAnnotation(classOf[Derivation]).asScala.toSet
    val withAnnotation = withFieldAnnotation | withMethodAnnotation
    withAnnotation.toSeq.sorted.flatMap(info => registerDerivationsFromObject(info.loadClass()))
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
   * @return a list of errors encountered during initialization
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
