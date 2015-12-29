package edu.cmu.cs.ls.keymaerax.bellerophon

/**
  * A bidirectional mapping
  * @author Nathan Fulton
  */
class BiMap[S, T](private val underlyingMap: Map[S, T]) extends Map[S, T] {
  override def +[TPrime >: T](kv: (S, TPrime)): BiMap[S, TPrime] = {
    if(underlyingMap.keySet.contains(kv._1) || underlyingMap.values.toSet.contains(kv._2))
      throw new Exception("Bidirectional maps must be bijective.")
    else
      new BiMap(underlyingMap + kv)
  }

  override def get(key: S): Option[T] = underlyingMap.get(key)

  override def -(key: S): BiMap[S, T] = new BiMap(underlyingMap - key)

  def inverse : BiMap[T, S] = new BiMap(underlyingMap.map(kvp => (kvp._2, kvp._1)))

  override def iterator: Iterator[(S, T)] = underlyingMap.iterator
}
