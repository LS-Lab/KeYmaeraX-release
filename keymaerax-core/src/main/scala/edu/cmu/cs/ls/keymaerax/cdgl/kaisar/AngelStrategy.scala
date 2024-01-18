/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Executable representation for Angelic strategies.
  * Translations to Angelic strategies and to simplified Demon subset.
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.StringOps


// @TODO: Massive memory leak, use local data structure instead
/** Used for allocating unique integer IDs */
object IDCounter {
  // Tracks every allocated ID associated to its node
  var idMap: Map[Int, AngelStrategy] = Map()
  // For nodes which arise from a demonization translation, track the original Angel node corresponding to each ID
  var originMap: Map[Int, AngelStrategy] = Map()
  // Map node IDs to source line and column
  var sourceLocationMap:Map[Int, (Int, Int)] = Map()
  var count: Int = 0

  var sourceFile: List[String] = Nil
  var fullSourceFile: Option[String] = None

  def setSourceFile(str: String): Unit = { sourceFile = (str:StringOps).linesIterator.toList; fullSourceFile = Some(str) }

  // can use fullSourceFile if performance too slow
  def prettyIndex(int: Int): (Int, Int) = {
    sourceFile match {
      case Nil => (0, int)
      case _ =>
        val res = KaisarProgramParser.prettyIndex(int, sourceFile)
        val altRes = KaisarProgramParser.prettyIndex(int, fullSourceFile.get)
        res
    }
  }

  def set(i: Int, as: AngelStrategy): Unit = {
    idMap = idMap.+(i -> as)
    count = (count + 1).max(i)
    as.location match {
      case Some(loc) =>
        sourceLocationMap = sourceLocationMap.+(i -> loc)
      case None => ()
    }
  }
  def next(as: AngelStrategy): Int = {
    val res = count
    count = count + 1
    idMap = idMap.+(res -> as)
    res
  }
  def contains(n: Int): Boolean = idMap.contains(n)
  def hasOriginal(n: Int): Boolean = originMap.contains(n)
  def get(n: Int): Option[AngelStrategy] = idMap.get(n)
  def getLocation(n: Int): Option[(Int, Int)] = sourceLocationMap.get(n)
  def apply(n: Int): AngelStrategy = idMap(n)
  def getOriginal(n: Int): Option[AngelStrategy] = originMap.get(n)
  def original(n: Int): AngelStrategy = originMap(n)
  def setOriginal(n: Int, as: AngelStrategy): Unit = (originMap = originMap.+(n -> as))

  // Should be something that never appears in strategies or CdGL expressions
  val MAP_SEPARATOR: String = "|->"
  // For serializing / reloading idMap
  def idMapString: String = {
    idMap.toList.sortBy({ case (k, v) => k }).map({ case (k, v) => k + MAP_SEPARATOR + StrategyPrinter(v) }).mkString("\n")
  }

  // For serializing / reloading originMap
  def originMapString: String = {
    originMap.toList.sortBy({case (k, v) => k}).map({case (k,v) => k + MAP_SEPARATOR + StrategyPrinter(v)}).mkString("\n")
  }

  def sourceLocMapString: String = {
    sourceLocationMap.toList.sortBy({case (k, v) => k}).
      map({case (k,(l,c)) =>
        k + MAP_SEPARATOR + l + "," + c}).
      mkString("\n")
  }

  private def parseIntPair(str: String):(Int,Int) = {
    val strs = str.split(',')
    (strs(0).toInt, strs(1).toInt)
  }

  private def parseMap[T](f: String => T, mapString: String): Map[Int, T] = {
    val lines = (mapString: StringOps).linesIterator.toList
    var theMap: Map[Int, T] = Map()
    lines.foreach {line =>
      val i = line.indexOf(MAP_SEPARATOR)
      if (i < 0) throw new Exception("Could not parse strategy ID map metadata")
      val numStr = line.take(i).trim()
      val stratStr = line.drop(i + MAP_SEPARATOR.length).trim()
      val num = numStr.toInt
      val strat = f(stratStr)
      theMap = theMap.+(num -> strat)
    }
    theMap
  }

  def loadSourceLocMap(locMapString: String): Unit = {
    sourceLocationMap = parseMap(parseIntPair, locMapString)
    println(sourceLocationMap)
  }

  def loadIdMap(idMapString: String): Unit = {
    idMap = parseMap(StrategyParser(_), idMapString)
    println(idMap)
  }

  def loadOriginMap(originMapString: String): Unit = {
    idMap = parseMap(StrategyParser(_), idMapString)
    println(originMap)
  }


  def clear(): Unit = {
    idMap = Map()
    originMap = Map()
  }
}

/** Directly executable, simply-typed strategy for Angel player */
sealed trait AngelStrategy {
  var nodeID: Int = IDCounter.next(this)
  var location: Option[(Int, Int)] = None
  def rememberSourceStatement(st: ASTNode): AngelStrategy = {
    val loc = st.location.map(i => IDCounter.prettyIndex(i))
    loc.foreach(l =>
      location = Some(l)
    )
    IDCounter.set(this.nodeID, this)
    this
  }
  def rememberSourceLocation(loc: (Int, Int)): AngelStrategy = {
    location = Some(loc)
    IDCounter.set(this.nodeID, this)
    this
  }
}
/** A simple strategy is one where Angel makes no choices, only Demon */
sealed trait SimpleStrategy extends AngelStrategy {
  def rememberSourceStrategy(as: AngelStrategy): SimpleStrategy = {
    as.location.foreach(l => location = Some(l))
    IDCounter.set(this.nodeID, this)
    this
  }
}

/** Demon must pass test f. Strategies are weak-test, assume f is decidable */
case class STest(f: Formula) extends SimpleStrategy
/** Deterministic assignment. Works identically for Angel/Demon.*/
case class SAssign(x: Ident, f: Term) extends SimpleStrategy
/** Nondeterministic assignment resolved by demon */
case class SAssignAny(x: Ident) extends SimpleStrategy
/** Demonic loop */
case class SLoop(s: AngelStrategy) extends SimpleStrategy
// Note: binary compose is better for backend execution, but n-ary composition looks much nicer in debugger.
/** (n-ary) sequential composition, identical for Demon vs Angel. */
case class SCompose(children: List[AngelStrategy]) extends SimpleStrategy
/** Demonic choice */
case class SChoice(l: AngelStrategy, r: AngelStrategy) extends SimpleStrategy
/** Differential equation with decidable domain constraint and Demonic duration */
case class SODE(ode: ODESystem) extends SimpleStrategy

/** Angelic while loop with decidable convergence/guard formula */
case class ALoop(conv: Formula, body: AngelStrategy) extends AngelStrategy
/* Angel for loop */
case class AForLoop(idx: Ident, idx0: Term, conv: Formula, body: AngelStrategy, idxUp: Term, guardDelta:Option[Term]) extends AngelStrategy
/** Angelic switch statement with decidable branch guards */
case class ASwitch(branches: List[(Formula, AngelStrategy)]) extends AngelStrategy
/** Differential equation with (concrete) angelic duration. */
case class AODE(ode: ODESystem, dur: Term) extends AngelStrategy

/** Smart constructors for DCompose */
object Composed {
  /** Smart constructor that filters out no-ops for readability */
  def apply(children: List[AngelStrategy]): AngelStrategy = {
    // Careful: Should distinguish "real" ?true from no-ops which should be eliminated
    val filtered = children.filter({case STest(True) => false case _ => true})
    filtered match {
      case Nil => STest(True)
      case as :: Nil => as
      case _ => SCompose(filtered)
    }
  }

  def apply(l: AngelStrategy, r: AngelStrategy): AngelStrategy = {
    apply(l :: r :: Nil)
  }

  def apply(children: List[SimpleStrategy]): SimpleStrategy = {
    // @TODO: Careful: Should distinguish "real" ?true from no-ops which should be eliminated
    // Note: flattening DCompose's would give more minimal trees, but the unflattened shape is nice in practice:
    // SSA blocks are kept together and can be easily collapsed in debugger
    val filtered = children.filter({case STest(True) => false case _ => true})
    filtered match {
      case Nil => STest(True)
      case as :: Nil => as
      case _ => SCompose(filtered)
    }
  }

  def apply(l: SimpleStrategy, r: SimpleStrategy): SimpleStrategy = {
    apply(l :: r :: Nil)
  }
}

object SimpleStrategy {
  /** Demonization pass which inlines Angelic strategies into Demon strategies.
    * The resulting Demon strategy is more complex in the sense that Demon must provide (or simulate) choices which Angel
    * previously made.
    * @see [[BasicDemonStrategy]] wrapper which automatically handles the added complexity of a Demonized strategy, so the
    * Demon driver can be programmed against the original game specification */
  def apply(fs: AngelStrategy): SimpleStrategy = {
    fs match {
      case SLoop(s) => SLoop(apply(s)).rememberSourceStrategy(fs)
      case SCompose(children) => SCompose(children.map(apply)).rememberSourceStrategy(fs)
      case SChoice(l, r) => SChoice(apply(l), apply(r)).rememberSourceStrategy(fs)
      case ALoop(conv, body) =>
        val loop = SLoop(Composed(STest(conv), apply(body))).rememberSourceStrategy(fs)
        IDCounter.setOriginal(loop.nodeID, fs)
        Composed(loop, STest(Not(conv)).rememberSourceStrategy(fs))
      case AForLoop(metX, met0, guard, body, metIncr, guardEpsilon) =>
        val loop = SLoop(Composed(List(STest(guard).rememberSourceStrategy(fs),
          apply(body),
          SAssign(metX, metIncr).rememberSourceStrategy(fs)))).rememberSourceStrategy(fs)
        IDCounter.setOriginal(loop.nodeID, fs)
        // @TODO: Also have guard even if not specified in model somehow
        Composed(List(SAssign(metX,met0).rememberSourceStrategy(fs),loop,
          STest(Metric.weakNegation(guard, guardEpsilon.getOrElse(Number(0)))).rememberSourceStrategy(fs)))
      case ASwitch(branches) =>
        val branchStrats = branches.map({case (f, fs) =>
          Composed(STest(f).rememberSourceStrategy(fs),
            apply(fs))})
        val pairs = branchStrats.zip(branches)
        val (xs, x) = (pairs.dropRight(1), pairs.last)
        val (choice, _) = xs.foldLeft[(SimpleStrategy, ASwitch)]((x._1, ASwitch(x._2 :: Nil)))({case ((accStrat, accOrig), (thisStrat, thisOrig)) =>
          val fullOrig = ASwitch(thisOrig :: accOrig.branches)
          val choice = SChoice(thisStrat, accStrat).rememberSourceStrategy(fs)
          IDCounter.setOriginal(choice.nodeID, fullOrig)
          (choice, fullOrig)
        })
        choice
      // @TODO: Proof rule somewhere should check duration variable binding side conditions
      case ss: SimpleStrategy => ss
      case _: AODE | _: SODE => throw new Exception("ODEs should be eliminated before SimpleStrategy conversion")
    }
  }
}

object AngelStrategy {
  /** Extract executable strategy for ODE from Kaisar proof. */
  private def ofODE(pode: ProveODE): AngelStrategy = {
    val tv = pode.timeVar.getOrElse(Variable("t"))
    val assignT = pode.duration match {
      case Some((_, f)) => SAssign(tv, f).rememberSourceStatement(pode)
      case None => SAssignAny(tv).rememberSourceStatement(pode)
    }
    val coll = pode.dc.collect
    val assms = (coll.assumptions.toList.map(_.f)).reduceRight[Formula](And)
    val invs = (coll.assumptions.toList.map(_.f) ++ coll.assertions.map(_.f)).reduceRight[Formula](And)
    val hasAsserts = pode.dc.collect.assertions.nonEmpty
    val isDemon = !pode.isAngelic
    (pode.solutions, hasAsserts && isDemon) match {
      // Generate tests if solution can't be expressed *or* if it's a demon ode with assertions, because that probably suggests we wanted to monitor the assertions
      case (None, _) | (_, true) =>
        val assignX = pode.ds.atoms.map(_.dp.xp.x).toList.map(x => SAssignAny(x).rememberSourceStatement(pode))
        val assignDX = pode.ds.atoms.map(_.dp).toList.map({ case AtomicODE(xp, e) => SAssign(xp, e).rememberSourceStatement(pode) })
        val conds = pode.timeVar match {
          case Some(t) if !pode.isAngelic => And(GreaterEqual(t, Number(0)), invs)
          case _ => invs
        }
        // test DC both initially and at end
        Composed(STest(conds).rememberSourceStatement(pode) :: assignT :: (assignX ++ assignDX.+:(STest(conds).rememberSourceStatement(pode))))
      case (Some(xfs), _) =>
        val setT = Composed(SAssignAny(tv).rememberSourceStatement(pode), STest(GreaterEqual(tv, Number(0))).rememberSourceStatement(pode))
        // @TODO: Should test all 0 <= s <= T  but c'est la vie
        val dc = STest(if (pode.isAngelic) assms else invs).rememberSourceStatement(pode)
        val solAssign = Composed(xfs.map({ case (x, f) => SAssign(x, f).rememberSourceStatement(pode) }))
        // test DC both at start and at end of ODE
        Composed(setT :: dc :: solAssign :: dc :: Nil)
    }
  }

  /** Main translation pass from Kaisar to strategies */
  private def body(pf: Statement, isPhi: Boolean): AngelStrategy = {
    pf match {
      case Assume(pat, f) => STest(f).rememberSourceStatement(pf)
      case BoxChoice(left, right) => SChoice(body(left, isPhi), body(right, isPhi)).rememberSourceStatement(pf)
      case InverseGhost(s) => body(s, isPhi).rememberSourceStatement(pf)
      case Modify(ids, mods) =>
        Composed(mods.map({
          case (x, None) => SAssignAny(x).rememberSourceStatement(pf)
          case (x, Some(f)) =>
            val res = SAssign(x, f).rememberSourceStatement(pf)
            if(isPhi)
              IDCounter.setOriginal(res.nodeID, STest(True).rememberSourceStatement(pf))
            res
        }))
      case Block(ss) => Composed(ss.map(body(_, isPhi)))
      case Switch(scrutinee, pats) => ASwitch(pats.map({ case (x, f, b) => (f, body(b, isPhi).rememberSourceStatement(b)) })).rememberSourceStatement(pf)
      case While(x, j, s) => ALoop(j, body(s, isPhi)).rememberSourceStatement(pf)
      case For(metX, met0, metIncr, conv, guard, s, gd) =>
        val bod = body(s, isPhi)
        AForLoop(metX, met0, guard.f, bod, metIncr, gd).rememberSourceStatement(pf)
      case BoxLoop(s, ih) => SLoop(body(s, isPhi)).rememberSourceStatement(pf)
      case pode: ProveODE =>
        val ode = ofODE(pode)
        // ODE does not have an "original" strategy, but we put it in map to indicate that it "was once an ODE"
        //if (pode.isAngelic)
        IDCounter.setOriginal(ode.nodeID, ode)
        ode.rememberSourceStatement(pf)
      case Phi(s) =>
        val block = body(s, isPhi = true)
        // Phi block does not have an "original" strategy, but we put it in map to indicate that it "is special"
        block
      case _: MetaNode | _: Note | _: Match | _: LetSym | _: Triv | _: Assert | _: Label | _: Ghost => STest(True).rememberSourceStatement(pf)
    }
  }

  /** Extract executable (Angelic) strategy from a (weak-test) Kaisar proof */
  def apply(pf: Statement): AngelStrategy = {
    val fv = VariableSets(pf).freeVars
    val main = body(pf, isPhi = false)
    val startLoc = (0, 0)
    val inits = fv.toList.map(SAssignAny).map(as => as.rememberSourceLocation(startLoc))
    val strat = Composed(inits.:+(main))
    strat
  }
}
