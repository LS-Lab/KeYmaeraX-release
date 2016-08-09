package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.core.Lemma
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXExtendedLemmaParser

/**
  * Common logic shared by most lemma DB implementations. Most lemma DB's can (and should) be implemented
  * by extending this class and implementing the abstract methods for basic storage operations.
  *
  * Created by bbohrer on 8/3/16.
  */
abstract class LemmaDBBase extends LemmaDB {
  def readLemmas(ids: List[LemmaID]):Option[List[String]]
  def writeLemma(id: LemmaID, lemma:String)
  def createLemma():LemmaID

  override def get(ids: List[LemmaID]): Option[List[Lemma]] = {
    readLemmas(ids).map(_.map(Lemma.fromString)) //@todo This should be over-ridden in every implementation so maybe we should just leave it abstract.
  }

  private val REDUNDANT_CHECKS = false
  private def saveLemma(lemma:Lemma, id:LemmaID): Unit = {
    if (REDUNDANT_CHECKS) {
      //@see[[edu.cmu.cs.ls.keymaerax.core.Lemma]]
      val parse = KeYmaeraXExtendedLemmaParser(lemma.toString)
      assert(parse._1 == lemma.name, "reparse of printed lemma's name should be identical to original lemma")
      assert(parse._2 == lemma.fact.conclusion +: lemma.fact.subgoals, s"reparse of printed lemma's fact ${lemma.fact.conclusion +: lemma.fact.subgoals}should be identical to original lemma ${parse._2}")
      assert(parse._3 == lemma.evidence, "reparse of printed lemma's evidence should be identical to original lemma")
    }

    writeLemma(id, lemma.toString)
    val lemmaFromDB = get(id)
    get(id) match {
      case None => throw new IllegalStateException("Lemma was not successfully inserted in database.")
      case Some(got) =>
        if (got != lemma) {
          remove(id)
          throw new IllegalStateException(s"Lemma in DB differed from lemma in memory -> deleted\n\tOriginal: ${lemma.toString}\n\tReloaded: ${got.toString}")
        }
    }
  }

  override def  add(lemma: Lemma): LemmaID = {
    val id = this.synchronized {
      // synchronize to make sure concurrent calls use distinct ID's
      lemma.name match {
        case Some(n) =>
          val got = get(n)
          require(got == None || got == Some(lemma),
            "Lemma name '" + n + ".alp' must be unique, or file content must be the lemma: \n" + lemma)
          n
        case None => createLemma()
      }
    }
    saveLemma(lemma, id)
    id.toString
  }
}
