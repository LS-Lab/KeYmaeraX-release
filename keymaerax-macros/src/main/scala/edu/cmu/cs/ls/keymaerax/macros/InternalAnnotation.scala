package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.{ClassfileAnnotation, StaticAnnotation}

/* @Tactic, @Axiom, @ProofRule macros consume their annotations, so we need to output an *extra* annotation to help
   runtime reflection find the annotated fields. */
class InternalAnnotation(/*val codeName: String, val inputs: List[ArgInfo]*/) extends StaticAnnotation with ClassfileAnnotation

