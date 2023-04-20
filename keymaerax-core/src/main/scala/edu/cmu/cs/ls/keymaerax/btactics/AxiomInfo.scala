/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.Logging
import org.reflections.Reflections
import org.reflections.scanners.Scanners

import scala.annotation.tailrec
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.language.implicitConversions
import scala.collection.mutable
import scala.reflect.runtime.{universe => ru}
import scala.util.Try

/**
  * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics)
  * with meta information of relevant names and display names and visualizations for the user interface.
  */
object DerivationInfoRegistry extends Logging {
  import scala.language.implicitConversions

  def convert(arg: ArgInfo, exprs: List[Expression]): Either[Any, String]  = {
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
        res.find({case _: Left[Any, String] => false case _: Right[Any, String] => true}) match {
          case Some(Right(err)) => Right(err)
          case None => Left(res.map({case Left(v) => v}))
        }
      case _ => Right("Expected: " + arg.sort + ", found: " + exprs.map(_.kind).mkString(",") + " " + exprs.map(_.prettyString).mkString(","))
    }
  }

  /** Locate the derivation info for said tactic */
  @tailrec
  def locate(t: BelleExpr): Option[DerivationInfo] = t match {
    case n: NamedBelleExpr => try { Some(DerivationInfo.ofCodeName(n.name)) } catch { case _: Exception => None }
    case AppliedPositionTactic(n, _) => locate(n)
    case AppliedBuiltinTwoPositionTactic(n, _, _) => locate(n)
    //@todo probably more cases
    case _ => None
  }

  ////////////////////////////////////////////////////////
  // Assemble above derivation infos in [[allInfo]] registry
  ////////////////////////////////////////////////////////

  /** We need to force the right-hand side of every tactic definition to evaluate, which requires passing in arguments
    * to every "def" of a tactic. Subtly, it's ok for these arguments to be dummies, because we're not actually
    * interpreting the tactic on a Provable, just creating a BelleExpr without interpreting that BelleExpr */
  private def instantiateArg(ai: String): Any = {
    ai match {
      case "Number" | "Term" | "Expression" => Number(0)
      case "String" => ""
      case "Variable" => Variable("x")
      case "Formula" => True
      case "Generator" => FixedGenerator(Nil)
      case "SubstitutionPair"  =>  SubstitutionPair(Nothing, Nothing)
      case "PosInExpr" => PosInExpr()
      case "Option" => None
      case "List" => Nil
    }
  }

  /* Apply a reflected method with well-typed dummy arguments (for its side effects)*/
  private def applyMirror(m: ru.MethodMirror, argSyms: List[ru.Symbol]): Unit = {
    val args = argSyms.map((theSymbol: ru.Symbol) => theSymbol.info.typeConstructor.toString.split('.').last)
    args match {
      // If [[m]] is a tactic, determine and instantiate correct argument types
      case Nil => m()
      case _ =>
        val arguments = args.map(instantiateArg)
        m(arguments:_*)
    }
  }


  /* Initialize TacticInfo for all @Tactic annotations in given class [[cl]]*/
  private def initClass(cl: Class[_], tpe: ru.Type): Unit = {
    // @TODO: Reduce code duplication
    /* Collect fields and methods of class */
    val fields  = cl.getDeclaredFields.filter(f => classOf[BelleExpr].isAssignableFrom(f.getType))
    val methods = cl.getDeclaredMethods.filter(f => classOf[BelleExpr].isAssignableFrom(f.getReturnType))
    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(tpe.termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    /*  @Tactic and friends disappear during compilation, but they replace themselves with @InternalAnnotation
     *  which we use here to identify annotated fields, which must be executed in order to initialize TacticInfos*/
    //@note lazy vals have a "hidden" getter method that does the initialization
    val keptFields = fields.filter(fn => { tpe.member(ru.TermName(fn.getName)).alternatives.flatMap(_.annotations).exists(_.tree.tpe.typeSymbol.toString == "InternalAnnotation")})
    val fieldFields = keptFields.map(fn => (fn, tpe.member(ru.TermName(fn.getName)).asMethod.getter.asMethod))
    val methodFields: mutable.ArraySeq[(String, ru.MethodSymbol)] = methods.flatMap(fn => {
      val mem = tpe.member(ru.TermName(fn.getName))
      /* Overoaded values are considered terms (not methods), and have a list of alternatives, which might be annotated.
      * In this case, we are only interested in the alternative that was actually annotated, not the whole method*/
      if (mem.isTerm && mem.asTerm.isOverloaded) {
        mem.asTerm.alternatives.filter(_.annotations.exists(_.tree.tpe.typeSymbol.name.toString == "InternalAnnotation"))
          .map(c => (fn.getName, c.asMethod))
      } else if (mem.annotations.exists(_.tree.tpe.typeSymbol.name.toString == "InternalAnnotation")){
        mutable.ArraySeq((fn.getName, mem.asMethod))
      } else {
        mutable.ArraySeq()
      }})
    val fieldMirrors = fieldFields.map({case (x, y) => (x, im.reflectMethod(y))})
    val methodMirrors = methodFields.map({case (x, y) => (x, im.reflectMethod(y))})
    val failures = mutable.Buffer.empty[(String,Throwable)]
    methodMirrors.indices.foreach(idx => {
      try {
        val (_, fm) = methodMirrors(idx)
        /* Type signature of function needed in order to generate well-typed arguments */
        val argSyms = fm.symbol.typeSignature.paramLists.headOption.getOrElse(Nil)
        // NB: allInfo gets updated automatically when touching each field/method
        applyMirror(fm, argSyms)
      } catch {
        case e: Throwable =>
          failures += (methodFields(idx)._1 -> e)
          logger.warn("WARNING: Failed to initialize @Tactic.", e)
      }
    })
    if (failures.nonEmpty)
      throw new Exception(s"WARNING: Encountered $failures method failures when trying to initialize @Tactic in ${cl.getName}. Unable to initialize:\n" + failures.map(_._1).mkString("\n"), failures.head._2)
    fieldMirrors.indices.foreach(idx => {
      try {
        val (fn, fm) = fieldMirrors(idx)
        val argSyms = tpe.member(ru.TermName(fn.getName)).asMethod.typeSignature.paramLists.headOption.getOrElse(Nil)
        applyMirror(fm, argSyms)
      } catch {
        case e: Throwable =>
          failures += (keptFields(idx).getName -> e)
          logger.warn("WARNING: Failed to initialize @Tactic.", e)
      }
    })
    if (failures.nonEmpty)
      throw new Exception(s"WARNING: Encountered $failures field failures when trying to initialize @Tactic in ${cl.getName}. Unable to initialize:\n" + failures.map(_._1).mkString("\n"), failures.head._2)
  }

  /* Has the global DerivationInfo list been initialized? */
  def isInit: Boolean = DerivationInfo._allInfo.nonEmpty
  /* Initialize global DerivationInfo list. This is surprisingly tricky because DerivationInfo is attached to tactic
  * (and axiom and rule) definitions, which are scattered throughout the prover. Here we maintain a global list of files
  * that can contain @Tactic definitions. Those classes are reflected and all annotated definitions are evaluated.
  * Having been modified by the @Tactic macro, those definitions all contain a function call which adds their TacticInfo
  * object to the global list. While this process does not require evaluating tactics in full, it does require loading
  * a number of classes, which triggers their static initializers and thus requires some attention to initialization order.
  *
  * Sanity checks ensure a runtime error is raised if @Tactic is used outside the allowed classes.
  * */
  def init(initLibrary: Boolean = true): Unit = {
    /* Initialization is relatively slow, so only initialize once*/
    if (isInit) return
    // Remember that initialization is in progress,
    DerivationInfo._initStatus = DerivationInfo.InitInProgress
    if (!initLibrary) return // Advanced use - user takes over in-progress initialization
    // Initialize derived axioms and rules, which automatically initializes their AxiomInfo and RuleInfo too
    // To allow working with restricted functionality: continue initialization despite potential errors in
    // deriving axioms, throw exception at end of initialization
    val deriveErrors = Try(Ax.prepopulateDerivedLemmaDatabase()).toEither

    // Search and initialize tactic providers (provide @Tactic-annotated methods)
    val reflections = new Reflections("edu.cmu.cs.ls.keymaerax.btactics")
    val tacticProviderTypes = reflections.get(Scanners.SubTypes.of(classOf[TacticProvider]).asClass())
    val instances = tacticProviderTypes.map(_.getField("MODULE$").get().asInstanceOf[TacticProvider])
    val objects = instances.map(_.getInfo)
    objects.foreach({case (cl, ct) => initClass(cl, ct)})

    /* Check that the list of annotated tactics we processed matches the list of named BelleExprs which have been
     * constructed so far. This can catch some named tactics that were never annotated, or catch some annotated files
     * that were forgotten in our list of files.
    */
    // NB: This check used to be an assertion in NamedTactic, but that doesn't work if a tactic is mentioned before registration.
    // Instead, check the names after everything is initialized.
    val overimplemented = mutable.Set[String]()
    DerivationInfo._seenNames.foreach((n: String) => {
      if (n != "Error" && !DerivationInfo.hasCodeName(n) && !n.startsWith("_"))
        overimplemented += n
    })
    assert(overimplemented.isEmpty, s"@Tactic init failed: NamedBelleExpr(s) named ${overimplemented.mkString(", ")} but this name does not appear in DerivationInfo's list of codeNames.")
    val unimplemented = mutable.Set[String]()
    DerivationInfo._allInfo.foreach({ case (_, di: DerivationInfo) =>
      if (!DerivationInfo._seenNames.contains(di.codeName)) {
        di match {
          // Axioms and rules are not tracked
          case _: CoreAxiomInfo | _: AxiomaticRuleInfo | _: DerivedAxiomInfo => ()
          case _ => unimplemented += di.codeName
        }
      }
    })
    assert(unimplemented.isEmpty, s"@Tactic init failed: Following DerivationInfo never implemented as @Tactic: " + unimplemented.mkString(", "))
    DerivationInfo._initStatus = DerivationInfo.InitComplete
    deriveErrors match {
      case Left(t) => throw t
      case _ => // nothing to do
    }
  }

  ////////////////////////////////////////////////////////
  // End of derivation infos in [[allInfo]] registry
  ////////////////////////////////////////////////////////

}


