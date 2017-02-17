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

  /** whether other location is adjacent to this location with no whitespace in between */
  def adjacentTo(other: Location): Boolean = end match {
    case Region(_,_,l,c) => other.begin match {
      case Region(ol,oc,_,_) => l==ol&&c+1==oc
    }
  }

  def spanTo(other: Location) = Region(this.begin.line, this.begin.column, other.begin.line, other.begin.column)
}

object UnknownLocation extends Location {
  override def toString = "<somewhere>"
  def begin = this
  def end = this
  def line = -1
  def column = -1
  def addLines(numLines: Int): Location = this
  def --(other: Location): Location = this
}
case class Region(line: Int, column: Int, endLine: Int, endColumn: Int) extends Location {
  require(line <= endLine || (line == endLine && column <= endColumn),
    "A region cannot start after it ends.")
  def begin = Region(line, column, line, column)
  def end = Region(endLine, endColumn, endLine, endColumn)
  def --(other: Location): Location = other match {
    case os: Region => Region(line, column, os.endLine, os.endColumn)
    case _: SuffixRegion => this
    case UnknownLocation => UnknownLocation
  }
  def addLines(numLines: Int): Location = Region(line + numLines, column, endLine + numLines, endColumn)

  override def toString = line + ":" + column + (if (column!=endColumn || line!=endLine) " to " + endLine + ":" + endColumn else "")
}
/**
  * Like a region, but extends until the end of the input.
  * @param line The starting line.
  * @param column The ending line.
  */
case class SuffixRegion(line: Int, column: Int) extends Location {
  def begin = Region(line, column, line, column)
  def end = UnknownLocation
  def --(other: Location) = this
  def addLines(numLines: Int): Location = SuffixRegion(line + numLines, column)
  override def toString = line + ":" + column + " to " + EOF
}