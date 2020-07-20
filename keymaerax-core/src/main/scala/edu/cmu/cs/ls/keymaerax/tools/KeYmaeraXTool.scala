/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleInterpreter, LazySequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics.{Ax, ConfigurableGenerator, DerivationInfoRegistry, TactixInit, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser

import scala.collection.immutable.Map

/**
 * The KeYmaera X tool, initializes the pretty printer.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
object KeYmaeraXTool extends Tool {
  /** @inheritdoc */
  override val name: String = "KeYmaera"

  /** Indicates whether the tool is initialized. */
  private var initialized = false

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = {
    if (KeYmaeraXParser.LAX_MODE)
      //@note Careful, this disables contract checking in printing!
      PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXNoContractPrettyPrinter.pp)
    else
      PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.pp)

    BelleInterpreter.setInterpreter(LazySequentialInterpreter())
    DerivationInfoRegistry.init()

    val generator = new ConfigurableGenerator[GenProduct]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p->(generator.products.getOrElse(p, Nil) :+ (inv, None))))
    TactixInit.invSupplier = generator

    initialized = true
  }

  /** @inheritdoc */
  override def restart(): Unit = { }

  /** @inheritdoc */
  override def shutdown(): Unit = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    initialized = false
  }

  /** @inheritdoc */
  override def isInitialized: Boolean = initialized

  /** @inheritdoc */
  override def cancel(): Boolean = true
}
