package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct

import scala.collection.immutable.Nil

/**
  * Initialization routine needs to set some global fields without causing TactixLibrary to initialize, so those fields
  * are set here and can then be referenced from TactixLibrary
  */
object TactixInit {
  /** "Generator" that provides (hardcoded or user-provided) loop invariants and differential invariants to use.
    * @see [[TactixLibrary]]
    * @see [[InvariantGenerator]] */
  var invSupplier: Generator[GenProduct] = FixedGenerator(Nil)
  /** Default generator for loop invariants to use.
    * @see [[TactixLibrary]]
    * @see [[InvariantGenerator]] */
  var loopInvGenerator: Generator[GenProduct] = InvariantGenerator.cached(InvariantGenerator.loopInvariantGenerator) //@note asks invSupplier
  // reinitialize with empty caches for test case separation
  /** Default generator for differential invariants to use.
    * @see [[TactixLibrary]]
    * @see [[InvariantGenerator]] */
  var differentialInvGenerator: Generator[GenProduct] = InvariantGenerator.cached(InvariantGenerator.differentialInvariantGenerator) //@note asks invSupplier
}
