/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

import org.keymaerax.bellerophon.ReflectiveExpressionBuilder
import org.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import org.keymaerax.btactics.TactixInit
import org.keymaerax.parser.{ArchiveParser, DLArchiveParser, DLParser}

/**
 * This object aims to centralize as much global state as possible, with the ultimate goal of eliminating global state.
 * Even if global state can't be fully eliminated, having a central place where it is accessed and modified should help
 * a lot with understanding and refactoring.
 *
 * Currently, the following bits of global state are known:
 *   - [[org.keymaerax.Configuration]]
 *   - [[org.keymaerax.UpdateChecker]] (in webui subproject)
 *   - [[org.keymaerax.bellerophon.BelleInterpreter]]
 *   - [[org.keymaerax.btactics.TactixInit]]
 *   - [[org.keymaerax.btactics.ToolProvider]]
 *   - [[org.keymaerax.core.PrettyPrinter]]
 *
 * If you stumble across any other global state, add it to the list!
 */

object GlobalState {
  val parser = new DLParser

  val archiveParser: ArchiveParser = new DLArchiveParser(
    new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(TactixInit.invGenerator), _))
  )
}
