package edu.cmu.cs.ls.keymaerax.parser

/**
  * The location where a Terminal is located in an input stream.
  * @note Serializable to make sure sbt test allows Location in ParseException errors.
  */
sealed trait Location extends Serializable {
  /** Beginning of this location */
  def begin: Location
  /** End of this location */
  def end: Location
  /** Beginning line or -1 */
  def line: Int
  /** Beginning column or -1 */
  def column: Int
  /** The range from this region to the other region, inclusive. Starting here and ending at other. */
  //@todo review choices
  def --(other: Location): Location

  /** Returns the current location offset by `numLines` lines. */
  def addLines(numLines : Int) : Location

  /** whether `other` location is adjacent right after this location with no whitespace in between */
  def adjacentTo(other: Location): Boolean = end match {
    case Region(_,_,l,c) => other.begin match {
      case Region(ol,oc,_,_) => l==ol&&c+1==oc
      case SuffixRegion(ol,oc) => l==ol&&c+1==oc
      case UnknownLocation => throw new IllegalArgumentException("Cannot compare adjacency with unknown regions: " + this + " compared to " + other)
    }
    // Nothing is adjacent after a SuffixRegion that goes till the end of the file
    case _: SuffixRegion => false
    case UnknownLocation => throw new IllegalArgumentException("Cannot compare adjacency with unknown regions: " + this + " compared to " + other)
  }

  def spanTo(other: Location): Region = Region(this.begin.line, this.begin.column, other.begin.line, other.begin.column)
}

object UnknownLocation extends Location {
  override def toString = "<somewhere>"
  def begin: Location = this
  def end: Location = this
  def line: Int = -1
  def column: Int = -1
  def addLines(numLines: Int): Location = this
  def --(other: Location): Location = this
}

/** A region from line:column till endLine:endColumn, inclusive */
case class Region(line: Int, column: Int, endLine: Int, endColumn: Int) extends Location {
  require(line <= endLine || (line == endLine && column <= endColumn),
    "A region cannot start after it ends.")
  def begin: Location = Region(line, column, line, column)
  def end: Location = Region(endLine, endColumn, endLine, endColumn)
  def --(other: Location): Location = other match {
    case os: Region => Region(line, column, os.endLine, os.endColumn)
    case _: SuffixRegion => this
    case UnknownLocation => UnknownLocation
  }
  def addLines(numLines: Int): Location = Region(line + numLines, column, endLine + numLines, endColumn)

  override def toString: String = line + ":" + column + (if (column!=endColumn || line!=endLine) " to " + endLine + ":" + endColumn else "")
}

object Region {
  /** A point Region consisting only of one line:column */
  def apply(line: Int, column: Int): Region = Region(line, column, line, column)

  /** Returns the region in `s` that spans from `startIdx` to `endIdx`. */
  def in(s: String, startIdx: Int, endIdx: Int): Region = {
    def lineColumn(i: Int) = {
      if (i == 0) {
        (1, 1)
      } else {
        val lines = s.substring(0, i).lines.toList
        (lines.length, lines.lastOption.map(_.length).getOrElse(0))
      }
    }
    val (sl, sc) = lineColumn(startIdx)
    val (el, ec) = lineColumn(endIdx)
    Region(sl, sc, el, ec)
  }
}
/**
  * Like a region, but extends until the end of the input.
  * @param line The starting line.
  * @param column The ending line.
  */
case class SuffixRegion(line: Int, column: Int) extends Location {
  def begin: Location = Region(line, column, line, column)
  def end: Location = UnknownLocation
  def --(other: Location): Location = this
  def addLines(numLines: Int): Location = SuffixRegion(line + numLines, column)
  override def toString: String = line + ":" + column + " to " + EOF
}