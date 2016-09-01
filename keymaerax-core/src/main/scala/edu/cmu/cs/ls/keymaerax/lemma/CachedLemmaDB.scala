/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review 2016-08-16
  */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.core.Lemma

import scala.collection.mutable

/**
  * Extends an arbitrary LemmaDB with caching functionality
  * to reduce the cost of repeated accesses to the same Lemma
  * within a given KeYmaeraX session.
  *
  * Created by bbohrer on 8/3/16.
  */
class CachedLemmaDB (db: LemmaDB) extends LemmaDB {
  private var cachedLemmas: mutable.Map[LemmaID, Lemma] = mutable.Map()

  override def get(lemmaIDs:List[LemmaID]): Option[List[Lemma]] = {
    /* Get as many lemmas as possible from the cache */
    val (cached, uncached) = lemmaIDs.zipWithIndex.partition{case (x,_) => cachedLemmas.contains(x)}
    val fromCache = cached.map{case (x,i) => (cachedLemmas(x), i)}
    val (uncachedIDs, uncachedIdxs) = uncached.unzip
    /* Use a single get() call for performance when getting uncached lemmas */
    try {
      val fromDB = db.get(uncachedIDs).map(_.zip(uncachedIdxs))
      fromDB.map{ list =>
        cachedLemmas ++= fromCache.map{case (lemma, idx) => (lemmaIDs(idx), lemma)}
        /* Preserve original order when combining cached vs. uncached lemmas*/
        (list ::: fromCache).sortWith{case ((_,i), (_,j)) => i < j}.map(_._1)
      }
    }
    catch {
      case e:Throwable => {
        println("Error while trying to retrieve lemma")
        e.printStackTrace()
        None
      }
    }
  }

  override def add(lemma: Lemma): LemmaID = {
    val id = db.add(lemma)
    cachedLemmas += ((id,lemma))
    id
  }

  override def deleteDatabase() = {
    cachedLemmas.clear()
    db.deleteDatabase()
  }

  override def remove(id:LemmaID): Unit = {
    cachedLemmas -= id
    db.remove(id)
  }
}
