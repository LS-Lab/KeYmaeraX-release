package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core.{DifferentialSymbol, Function, NamedSymbol, Real, Sort, Tuple, Unit, Variable, insist, Ensures}
import MathematicaConversion.MExpr
import edu.cmu.cs.ls.keymaerax.tools.ConversionException

/**
  * Name conversion to/from Mathematica. Prefixes all names with a namespace prefix. Refuses to convert
  * interpreted symbols.
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
private[tools] object MathematicaNameConversion {
  // a prefix that Mathematica accepts but NamedSymbol would refuse to make disjoint by construction
  private val NAMESPACE_PREFIX = "kyx`"
  // replacements for unsupported symbols _
  private val INDEX_SEP        = "$i$"
  private val UNDERSCORE_REPL  = "$u$"

  /** Indicates whether `e` is a name convertible to a KeYmaera X variable or function symbol. */
  def isConvertibleName(e: MExpr): Boolean = e.symbolQ && e.asString.startsWith(NAMESPACE_PREFIX)

  /**
    * Converts a KeYmaera name into a Mathematica symbol. Masks names as follows:
    * {{{
    * base + index     ---> NAMESPACE_PREFIX + base + INDEX_SEP + index
    * base only        ---> NAMESPACE_PREFIX + base
    * }}}
    * @param ns The KeYmaera name to convert.
    * @return The Mathematica symbol.
    * @note Interpreted function symbols are not allowed.
    */
  def toMathematica(ns: NamedSymbol): MExpr = {
    val name: String = ns match {
      case Function(_, _, _, _, Some(_)) => throw ConversionException("Name conversion of interpreted function symbols not allowed: " + ns.name)
      case DifferentialSymbol(_) => throw ConversionException("Name conversion of differential symbols not allowed: " + ns.toString)
      case _ => maskName(ns)
    }
    MathematicaOpSpec.symbol(name)
  } ensures (r => isConvertibleName(r), "Symbol names expected as result")

  /**
    * Converts a Mathematica name into its corresponding KeYmaera X named symbol (Variable or Function). Distinguishes
    * between variables and functions (Symbol -> Variable, Expr with arguments -> Function). In
    * each case, decomposes the Mathematica name based upon the possible forms of the name:
    * {{{
    * NAMESPACE_PREFIX + base + INDEX_SEP + index ---> name + index
    * NAMESPACE_PREFIX + base               ---> name only
    * }}}
    * @param e The Mathematica 'name'
    * @return The named symbol.
    * @note Refuses to convert interpreted function symbols (i.e., any name not prefixed with kyx)
    */
  def toKeYmaera(e: MExpr): NamedSymbol = {
    if (e.symbolQ) {
      val (name, index) = unmaskName(e.asString)
      Variable(name, index, Real)
    } else {
      val (name, index) = unmaskName(e.head.asString)
      val fnDomain = convertFunctionDomain(e.args)
      Function(name, index, fnDomain, Real, interp = None)
    }
  }

  /** Converts a nested list of arguments into nested tuples of reals */
  private def convertFunctionDomain(arg: MExpr): Sort = {
    if (arg.listQ) {
      assert(arg.args.length == 2, "Pair arguments have been turned into lists of length 2")
      val theArgs = arg.args
      Tuple(convertFunctionDomain(theArgs(0)), convertFunctionDomain(theArgs(1)))
    } else {
      Real
    }
  }
  /** Converts a nested list of arguments into nested tuples of reals */
  protected def convertFunctionDomain(args: Array[MExpr]): Sort = {
    assert(args.length <= 2, "Functions have at most 2 arguments (second can be a nested list) " + args.mkString(","))
    args.map(convertFunctionDomain).reduceRightOption(Tuple).getOrElse(Unit)
  }

  /** Masks a name, i.e., replaces _ with $u$, adds the namespace prefix kyx, and merges name and index (separated by $i$) */
  private def maskName(ns: NamedSymbol): String = uncheckedMaskName(ns) ensures(r => {
    val (name, idx) = uncheckedUnmaskName(r); name == ns.name && idx == ns.index
  }, "Unmasking a masked name should produce original unmasked name" +
    "\n Original unmasked name" + ns.prettyString +
    "\n Masked name " + uncheckedMaskName(ns) +
    "\n Reunmasked to " + uncheckedUnmaskName(uncheckedMaskName(ns)))

  /** Masking without contracts. */
  private def uncheckedMaskName(ns: NamedSymbol): String = {
    insist(ns.sort==Real, "still only accepting reals for conversion")
    //Ensure that none of the "special" strings occur in the variable name.
    //@note $ cannot occur by [[NamedSymbol]] data structure invariant isLetterOrDigit ('$'.isLetterOrDigit == false)
    assert(!ns.name.contains("$"), "Character '$' not allowed in variable names")
    //@note kyx` cannot occur by [[NamedSymbol]] data structure invariant isLetterOrDigit ('`'.isLetterOrDigit == false)
    assert(!ns.name.contains(NAMESPACE_PREFIX), "String '" + NAMESPACE_PREFIX + "' not allowed in variable names")
    //@note double-check separators (UNDERSCORE_REPL and INDEX_SEP contain $ so are checked with above)
    assert(!ns.name.contains(UNDERSCORE_REPL), "String '" + UNDERSCORE_REPL + "' not allowed in variable names")
    assert(!ns.name.contains(INDEX_SEP), "String '" + INDEX_SEP + "' not allowed in variable names")

    //@solution (name conflicts): symmetric name conversion in unmaskName, contract disjointNames in KeYmaeraToMathematica and MathematicaToKeYmaera
    ns match {
      case Function(_, _, _, _, Some(_)) => throw ConversionException("Name conversion of interpreted function symbols not allowed: " + ns.name)
      case DifferentialSymbol(_) => throw ConversionException("Name conversion of differential symbols not allowed: " + ns.toString)
      case _ =>
        assert(ns.name.count(c => c == '_') <= 1, "At most one _ in names")
        val identifier = ns.name.replaceAllLiterally("_", UNDERSCORE_REPL)
        NAMESPACE_PREFIX + (ns.index match {
          case Some(idx) => identifier + INDEX_SEP + idx
          case None      => identifier
        })
    }
  }

  /** Unmasks a name, i.e., adds _ for $u$, removes the namespace prefix kyx, and splits at $i$ into the name and its index. */
  private def unmaskName(maskedName: String): (String, Option[Int]) = uncheckedUnmaskName(maskedName) ensures(r => {
    r._1 == "Apply" || maskName(Variable(r._1, r._2, Real)) == maskedName
  }, "Masking an unmasked name should produce original masked name" +
     "\n Original masked name " + maskedName +
     "\n Unmasked name " + uncheckedUnmaskName(maskedName) +
     "\n Remasked to " + uncheckedMaskName(Variable(uncheckedUnmaskName(maskedName)._1, uncheckedUnmaskName(maskedName)._2, Real)))

  /** Unmasking without contracts. */
  private[tools] def uncheckedUnmaskName(maskedName: String): (String, Option[Int]) = {
    val uscoreMaskedName = maskedName.replaceAllLiterally(UNDERSCORE_REPL, "_")
    if (uscoreMaskedName.startsWith(NAMESPACE_PREFIX)) {
      val strippedName = uscoreMaskedName.substring(NAMESPACE_PREFIX.length)
      strippedName.indexOf(INDEX_SEP) match {
        case -1 => (strippedName, None)
        case i =>
          val (name, index) = strippedName.splitAt(i)
          //@note not stripPrefix, it is .substring with a redundant .startsWith already guaranteed by .indexOf+.splitAt
          (name, Some(Integer.parseInt(index.substring(INDEX_SEP.length))))
      }
    } else throw ConversionException("Name conversion of unprefixed (" + NAMESPACE_PREFIX + ") names not allowed: " + uscoreMaskedName)
  }
}
