/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.NamedBelleExpr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest
import org.scalatest.Matchers

import scala.collection.immutable.Range
import scala.reflect.runtime.{universe => ru}
import scala.reflect.runtime.universe.typeTag

/**
 * Tests code names of tactics and AxiomInfo for compatibility for TacticExtraction.
 *
 * @author Andre Platzer
 */
@IgnoreInBuildTest
class CodeNameChecker extends TacticTestBase with Matchers {
  //@todo also reflect through all DerivedAxioms to check they've been added to AxiomInfo
  "Tactic codeNames versus AxiomInfo codeNames" should "agree" in withMathematica { _ =>
    val all = DerivationInfo.allInfo
    for (info <- all) {
      //println("Checking " + info.codeName)
      instantiateSomeBelle(info) match {
          // made compile by reflection or generalizing type hierarchy for some BelleExpr
        case Some(b: NamedBelleExpr) =>
          if (info.codeName != b.name)
            println("TEST(WARNING): codeName should be changed to a consistent name: " + info.codeName + " alias " + info.canonicalName + " gives " + b.name)
        case Some(b: BelleExpr) => println("TEST: belleExpr does not have a codeName: " + info.codeName + " alias " + info.canonicalName + " gives " + b)
        case None => println("TEST(INFO): cannot instantiate belleExpr " + info.codeName + " alias " + info.canonicalName)
      }
    }
  }

  "Derived axioms" should "all be specified in AxiomInfo" in withMathematica { _ =>
    val lemmas = DerivedAxioms.getClass.getDeclaredFields.filter(f => classOf[Lemma].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[DerivedAxioms.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    //@note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => ru.typeOf[DerivedAxioms.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    val fieldMirrors = fields.map(im.reflectMethod)

    Range(0, fieldMirrors.length-1).foreach(idx => {
      try {
        val axiom = fieldMirrors(idx)().asInstanceOf[Lemma]
        //println("Checking " + axiom.name)
        try {
          ProvableInfo.ofStoredName(axiom.name.getOrElse(fail("Derived axiom without name defined in " + fieldMirrors(idx).symbol.name)))
        } catch {
          case _: Throwable => println("TEST(WARNING): codeName of axiom " + axiom.name + " not found in DerivationInfo, should be added/changed to a consistent name")
        }

      } catch {
        case _: Throwable => println("TEST(INFO): cannot instantiate derived axiom " + fieldMirrors(idx).symbol.name)
      }
    })
  }

  /** get some silly BelleExpr from info by feeding it its input in a type-compliant way. */
  private def instantiateSomeBelle(info: DerivationInfo): Option[BelleExpr] =
  try {
    val e = info.inputs.foldLeft(info.belleExpr) ((t,_) => t match {
      case expr: TypedFunc[Formula, _] if expr.argType.tpe <:< typeTag[Formula].tpe => expr(True)
      case expr: TypedFunc[Variable, _] if expr.argType.tpe <:< typeTag[Variable].tpe => expr(Variable("dummy"))
      case expr: TypedFunc[Term, _] if expr.argType.tpe <:< typeTag[Term].tpe => expr(Number(42))
      case expr: TypedFunc[Expression, _] if expr.argType.tpe <:< typeTag[Expression].tpe => expr(Variable("dummy"))
      case expr: TypedFunc[Option[Formula], _] if expr.argType.tpe <:< typeTag[Option[Formula]].tpe  => expr(Some(True))
      case expr: TypedFunc[Option[Variable], _] if expr.argType.tpe <:< typeTag[Option[Variable]].tpe => expr(Some(Variable("dummy")))
      case expr: TypedFunc[Option[Term], _] if expr.argType.tpe <:< typeTag[Option[Term]].tpe => expr(Some(Number(42)))
      case expr: TypedFunc[Option[Expression], _] if expr.argType.tpe <:< typeTag[Option[Expression]].tpe => expr(Some(Variable("dummy")))
    })
    e match {
      case t: BelleExpr => Some(t)
      case _ => println("WARNING: input() and belleExpr() function seem incompatible for DerivationInfo: " + info); None
    }
  } catch {
    case _: NotImplementedError => None
  }
}
