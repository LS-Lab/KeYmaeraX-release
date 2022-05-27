/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

/**
  * Bellerophon labels for proof branches.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.label()]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.Idioms.<()]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.BelleLabels]]
  */
trait BelleLabel {
  /** The label. */
  val label: String
  /** The label pretty string. */
  def prettyString: String
  /** All sublabels from root label to leave label. */
  def components: List[BelleLabel]
  /** Appends a label to the end of this label. */
  def append(l: BelleLabel): BelleLabel
  /** Returns true if `l` is a suffix of this label (ignoring top- vs.sub-label differences), false otherwise. */
  def endsWith(l: BelleLabel): Boolean = components.map(_.label).endsWith(l.components.map(_.label))
}

/** Conversion functions for labels from/to strings. */
object BelleLabel {
  val LABEL_SEPARATOR: String = "::"
  val LABEL_DELIMITER: String = "//"

  /** Converts a string to a label. */
  def fromString(s: String): List[BelleLabel] = {
    s.split(LABEL_SEPARATOR).map(topLabel => {
      val labels = topLabel.split(LABEL_DELIMITER)
      val parent = BelleTopLevelLabel(labels.head)
      labels.tail.foldLeft[BelleLabel](parent)({ case (p, label) => BelleSubLabel(p, label) })
    }).toList
  }

  /** Converts a label to a string. */
  def toPrettyString(labels: List[BelleLabel]): String = labels.map(_.prettyString).mkString(LABEL_SEPARATOR)
}
/** A top-level label for a BelleProvable */
case class BelleTopLevelLabel(label: String) extends BelleLabel {
  require(!label.contains(BelleLabel.LABEL_DELIMITER), s"Label should not contain the sublabel delimiter ${BelleLabel.LABEL_DELIMITER}")
  require(!label.contains(BelleLabel.LABEL_SEPARATOR), s"Label should not contain the label separator ${BelleLabel.LABEL_SEPARATOR}")
  override def prettyString: String = label
  override def components: List[BelleLabel] = this :: Nil
  override def append(l: BelleLabel): BelleLabel = l match {
    case tl: BelleTopLevelLabel => BelleSubLabel(this, tl.label)
    case sl: BelleSubLabel => BelleSubLabel(this.append(sl.parent), sl.label)
    case BelleStartTxLabel | BelleRollbackTxLabel => BelleLabelTx(this, None)
  }
}
/** Label transaction with rollback point `r` and collected labels `c` since rollback point. */
case class BelleLabelTx(r: BelleLabel, c: Option[BelleLabel], label: String = "") extends BelleLabel {
  override def prettyString: String = r.prettyString
  override def components: List[BelleLabel] = this +: r.components
  override def append(l: BelleLabel): BelleLabel = l match {
    case tl: BelleTopLevelLabel => copy(c = Some(c.map(_.append(tl)).getOrElse(tl)))
    case sl: BelleSubLabel => copy(c = Some(c.map(_.append(sl)).getOrElse(sl)))
    case BelleStartTxLabel => BelleLabelTx(this, None)
    case BelleRollbackTxLabel => BelleLabelTx(r, None)
    case BelleCommitTxLabel => r match {
      case BelleStartTxLabel => c.getOrElse(throw new IllegalArgumentException("Unable to commit empty label transaction"))
      case _ => c.map(r.append).getOrElse(r)
    }
    // shorthand for label(rollback) & label(l) & label(commit)
    case BelleLabelTx(BelleSubLabel(BelleRollbackTxLabel, l), None, _) => copy(c = Some(BelleTopLevelLabel(l))).append(BelleCommitTxLabel)
  }
}
/** Rollback a label transaction. */
object BelleRollbackTxLabel extends BelleLabel {
  override val label = ""
  override def prettyString: String = label
  override def components: List[BelleLabel] = this :: Nil
  override def append(l: BelleLabel): BelleLabel = l
}
/** Commits a label transaction. */
object BelleCommitTxLabel extends BelleLabel {
  override val label = ""
  override def prettyString: String = label
  override def components: List[BelleLabel] = this :: Nil
  override def append(l: BelleLabel): BelleLabel = l
}
object BelleStartTxLabel extends BelleLabel {
  override val label = ""
  override def prettyString: String = label
  override def components: List[BelleLabel] = this :: Nil
  override def append(l: BelleLabel): BelleLabel = l
}
/** A sublabel for a BelleProvable */
case class BelleSubLabel(parent: BelleLabel, label: String)  extends BelleLabel {
  require(!label.contains(BelleLabel.LABEL_DELIMITER), s"Label should not contain the sublabel delimiter ${BelleLabel.LABEL_DELIMITER}")
  require(!label.contains(BelleLabel.LABEL_SEPARATOR), s"Label should not contain the label separator ${BelleLabel.LABEL_SEPARATOR}")
  override def prettyString: String = parent.prettyString + BelleLabel.LABEL_DELIMITER + label
  override def components: List[BelleLabel] = parent.components :+ this
  override def append(l: BelleLabel): BelleLabel = l match {
    case tl: BelleTopLevelLabel => BelleSubLabel(this, tl.label)
    case sl: BelleSubLabel => BelleSubLabel(parent.append(sl.parent), sl.label)
    case BelleStartTxLabel | BelleRollbackTxLabel => BelleLabelTx(this, None)
    case _ => BelleSubLabel(this, l.label)
  }
}
