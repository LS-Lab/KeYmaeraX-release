package edu.cmu.cs.ls.keymaerax.btactics

import java.io.{File, FileWriter, FilenameFilter}
import java.lang.reflect.InvocationTargetException

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleProvable
import edu.cmu.cs.ls.keymaerax.btactics.Ax._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.btactics.macros.ProvableInfo
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, IgnoreInBuildTest, SummaryTest, UsualTest}
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags.OptimisticTest

import scala.reflect.runtime.{universe => ru}
import scala.collection.immutable
import scala.collection.immutable.Map

/**
  * Tests [[edu.cmu.cs.ls.keymaerax.btactics.Ax]]
  *
  * @see [[CodeNameChecker]]
  * @see [[DerivedAxiomsTests]]
  * @note Must be separate test suite from same tests withZ3, otherwise lazy vals in DerivedAxioms corrupt tests.
  */
@IgnoreInBuildTest // otherwise it deletes derived lemmas while other tests are running
@CheckinTest
@SummaryTest
@UsualTest
class Z3DerivedAxiomsTests extends TacticTestBase(registerAxTactics=None) {

  private def check(pi: ProvableInfo): Sequent = {
    println(pi.codeName + "\n" + pi.provable.conclusion)
    pi.provable shouldBe 'proved
    useToClose(pi)
    pi.provable.conclusion
  }

  private def useToClose(pi: ProvableInfo): Unit = {
    ProvableSig.startProof(pi.provable.conclusion)(pi.provable, 0) shouldBe 'proved
    //@note same test as previous line, just to make sure the lemma can be used by substitution
    theInterpreter(TactixLibrary.byUS(pi), BelleProvable.plain(ProvableSig.startProof(pi.provable.conclusion))) match {
      case BelleProvable(provable, _, _) => provable shouldBe 'proved
      case _ => fail()
    }
  }

  "Derived axioms and rules" should "prove one-by-one on a fresh lemma database" taggedAs KeYmaeraXTestTags.CheckinTest in withZ3 { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      getDerivedAxiomsMirrors.foreach({ case (name, fm) =>
        // delete all stored lemmas
        LemmaDBFactory.lemmaDB.deleteDatabase()
        // re-initialize DerivedAxioms singleton object to forget lazy vals of previous iterations
        val c = Ax.getClass.getDeclaredConstructor()
        c.setAccessible(true)
        withClue("Missing dependency in '" + name + "': inspect stack trace for occurrences of Axioms.scala for hints where to add missing dependency\n") {
          try {
            println("Deriving " + fm.symbol + "...")
            fm.bind(c.newInstance())()
            println("...done")
          } catch {
            case ex: InvocationTargetException =>
              val missingDependency = "Lemma ([^\\s]*) should".r.findFirstMatchIn(ex.getCause.getMessage).
                map(_.group(1)).getOrElse("<unknown>")
              fail("Missing dependency to '" + missingDependency + "'", ex.getCause)
          }
        }
      })
    }
  }

  "Derived Axioms" should "prove <-> reflexive" in {check(equivReflexive)}
  it should "prove !!" in {check(doubleNegation)}
  it should "prove exists dual" in {check(existsDual)}
  ignore should "prove all eliminate" taggedAs OptimisticTest in {check(alle)}
  ignore should "prove exists eliminate" taggedAs OptimisticTest in {check(existse)}
  it should "prove !exists" in {check(notExists)}
  it should "prove !all" in {check(notAll)}
//  it should "prove !all2" in {check(notAll2)}
  it should "prove ![]" in {check(notBox)}
  it should "prove !<>" in {check(notDiamond)}
  ignore should "prove all distribute" in {check(allDist)}
  it should "prove box dual" in {check(box)}
//  it should "prove K1" in {check(K1)}
//  it should "prove K2" in {check(K2)}
  //@todo nrf it should "prove box split" in {check(boxAnd)}
//  it should "prove box split left" in {check(boxSplitLeft)}
//  it should "prove box split right" in {check(boxSplitRight)}
  it should "prove [] split" in {check(boxAnd)}
  it should "prove [] conditional split" in {check(boxImpliesAnd)}
  it should "prove <> split" in {check(diamondOr)}
  it should "prove []~><> propagation" in {check{boxDiamondPropagation}}
  it should "prove <:=> assign" in {check(assigndAxiom)}
//  it should "prove <:=> assign v" in {check(dummyassigndVvariant)}
  it should "prove := assign dual" in {check(assignDual)}
  it should "prove all substitute" in withZ3 { qeTool => check(allSubstitute)}
  it should "prove [:=] equational" in withZ3 { qeTool => check(assignbequational)}
//  it should "prove [:=] assign equality exists" in {check(assignbExistsAxiom)}
  it should "prove exists and" in {check(existsAnd)}
  it should "prove [:=] assign exists" in {check(assignbexists)}
  it should "prove <:=> assign equality" in {check(assigndEqualityAxiom)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignb)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssignd)}
  //@todo it should "prove [':=] differential assign" in {check(assignDAxiomb)}
  it should "prove <':=> differential assign" in {check(Dassignd)}
  it should "prove <:*> assign nondet" in {check(randomd)}
  it should "prove <?> test" in {check(testd)}
  it should "prove <++> choice" in {check(choiced)}
  it should "prove <;> compose" in {check(composed)}
  it should "prove <*> iterate" in {check(iterated)}
  it should "prove <*> approx" in {check(loopApproxd)}
  it should "prove [*] approx" in {check(loopApproxb)}
  it should "prove II induction" in {check(IIinduction)}
  it should "prove [*] merge" in {check(loopMergeb)}
  it should "prove <*> merge" in {check(loopMerged)}
  it should "prove exists generalize" in {check(existsGeneralize)}
  it should "prove vacuous exists" in {check(existsV)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondet)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondet)}
  it should "prove & commute" in {check(andCommute)}
  it should "prove & assoc" in {check(andAssoc)}
  it should "prove !& deMorgan" in {check(notAnd)}
  it should "prove !| deMorgan" in {check(notOr)}
  it should "prove !-> deMorgan" in {check(notImply)}
  it should "prove !<-> deMorgan" in {check(notEquiv)}
  it should "prove domain commute" in {check(domainCommute)}
  it should "prove -> expand" in {check(implyExpand)}
  it should "prove PC1" in {check(PC1)}
  it should "prove PC2" in {check(PC2)}
  it should "prove PC3" in {check(PC3)}
  it should "prove -> tautology" in {check{implyTautology}}
  it should "prove ->'" in {check(Dimply)}
  it should "prove \\forall->\\exists" in {check(forallThenExists)}
  //it should "prove DI differential invariance from DI" in {check(DIinvariance)}
  it should "prove DI differential invariant from DI" in {check(DI)}
  it should "prove DIo open differential invariance >" in withZ3 {_ => check(DIoless)}
  it should "prove DW differential weakening" in {check(DW)}
  it should "prove DS no domain" in {check(DSnodomain)}
  it should "prove Dsol& differential equation solution" in {check(DSddomain)}
  //  it should "prove x' derive var" in {check(Dvar)}
  it should "prove x' derive variable" in {check(DvariableAxiom)}
  it should "prove x' derive var commuted" in withZ3 { qetool => check(DvariableCommutedAxiom)}
  it should "prove 'linear" in withZ3 { qetool => check(Dlinear)}
  it should "prove 'linear right" in withZ3 { qeTool => check(DlinearRight)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DX diamond differential skip" in {check(dDX)}
  it should "prove 0*" in withZ3 { qeTool => check(zeroTimes)}
  it should "prove 0+" in withZ3 { qeTool => check(zeroPlus)}
  it should "prove +0" in withZ3 { qeTool => check(plusZero)}
  it should "prove *0" in withZ3 { qeTool => check(timesZero)}
  it should "prove = reflexive" in withZ3 {qetool =>check(equalReflexive)}
  it should "prove = commute" in withZ3 { qetool =>check(equalCommute)}
  it should "prove <=" in withZ3 { qetool =>check(lessEqual)}
  it should "prove ! !=" in withZ3 { qetool =>check(notNotEqual)}
  it should "prove ! >=" in withZ3 { qetool =>check(notGreaterEqual)}
  it should "prove >= flip" in withZ3 { qetool =>check(flipGreaterEqual)}
  it should "prove > flip" in withZ3 { qetool =>check(flipGreater)}
  it should "prove <= flip" in withZ3 { qetool =>check(flipLessEqual)}
  it should "prove < flip" in withZ3 { qetool =>check(flipLess)}
  it should "prove + associative" in withZ3 { qeTool => check(plusAssociative)}
  it should "prove * associative" in withZ3 { qeTool => check(timesAssociative)}
  it should "prove + commute" in withZ3 { qeTool => check(plusCommute)}
  it should "prove * commute" in withZ3 { qeTool => check(timesCommute)}
  it should "prove distributive" in withZ3 { qeTool => check(distributive)}
  it should "prove + identity" in withZ3 { qeTool => check(zeroPlus)}
  it should "prove * identity" in withZ3 { qeTool => check(timesIdentity)}
  it should "prove + inverse" in withZ3 { qeTool => check(plusInverse)}
  it should "prove * inverse" in withZ3 { qeTool => check(timesInverse)}
  it should "prove positivity" in withZ3 { qeTool => check(positivity)}
  it should "prove + closed" in withZ3 { qeTool => check(plusClosed)}
  it should "prove * closed" in withZ3 { qeTool => check(timesClosed)}
  it should "prove <" in withZ3 { qeTool => check(less)}
  it should "prove ! <" in withZ3 { qeTool => check(notLess)}
  it should "prove ! <=" in withZ3 { qeTool => check(notLessEqual)}
  it should "prove >" in withZ3 { qeTool => check(greater)}
  it should "prove ! >" in withZ3 { qeTool => check(notGreater)}

  /** Axioms for arithmetic in core (some not yet provable with Z3) */
//  it should "prove != elimination" ignore withZ3 { qeTool => check(notEqualElim)}
//  it should "prove >= elimination" ignore withZ3 { qeTool => check(greaterEqualElim)}
//  it should "prove > elimination" ignore withZ3 { qeTool => check(greaterElim)}
  it should "prove 1>0" in withZ3 { qeTool => check(oneGreaterZero)}
  it should "prove nonnegative squares" in withZ3 { qeTool => check(nonnegativeSquares)}
  it should "prove >2!=" in withZ3 { qeTool => check(greaterImpliesNotEqual)}
  it should "prove > monotone" in withZ3 { qeTool => check(greaterMonotone)}

  it should "prove abs" in withZ3 { qeTool => check(abs)}
  it should "prove min" in withZ3 { qeTool => check(min)}
  it should "prove max" in withZ3 { qeTool => check(max)}
  //it should "prove +<= up" in withZ3 { qeTool => check(intervalUpPlus)}
  //it should "prove -<= up" in withZ3 { qeTool => check(intervalUpMinus)}
  it should "prove *<= up" in withZ3 { qeTool => check(intervalUpTimes)}
  it should "prove 1Div<= up" in withZ3 { qeTool => check(intervalUp1Divide)}
  //it should "prove Div<= up" in withZ3 { qeTool => check(intervalUpDivide)}
  it should "prove <=+ down" in withZ3 { qeTool => check(intervalDownPlus)}
  it should "prove <=- down" in withZ3 { qeTool => check(intervalDownMinus)}
  it should "prove <=* down" in withZ3 { qeTool => check(intervalDownTimes)}
  it should "prove <=1Div down" in withZ3 { qeTool => check(intervalDown1Divide)}
  //it should "prove <=Div down" in withZ3 { qeTool => check(intervalDownDivide)}
  it should "prove K& down" in withZ3 { qeTool => check(Kand)}
  it should "prove &-> down" in withZ3 { qeTool => check(andImplies)}

  "Derived Axiom Tactics" should "tactically prove <-> reflexive" in {check(equivReflexive)}
  it should "tactically prove !!" in {check(doubleNegation)}
  it should "tactically prove exists dual" in {check(existsDual)}
  ignore should "tactically prove all eliminate" taggedAs OptimisticTest in {check(alle)}
  ignore should "tactically prove exists eliminate" taggedAs OptimisticTest in {check(existse)}
  it should "tactically prove all distribute" in {check(allDist)}
  it should "tactically prove box dual" in {check(box)}
  it should "tactically prove <:=> assign" in {check(assigndAxiom)}
  it should "tactically prove [:=] equational" in withZ3 { qeTool => check(assignbequational)}
//  it should "tactically prove [:=] equational exists" in {check(assignbExistsAxiom, assignbEquationalT)}
  it should "tactically prove [:=] vacuous assign" in {check(vacuousAssignb)}
  it should "tactically prove <:=> vacuous assign" in {check(vacuousAssignd)}
  it should "tactically prove <':=> differential assign" in {check(Dassignd)}
  it should "tactically prove <++> choice" in {check(choiced)}
  it should "tactically prove <;> compose" in {check(composed)}
  it should "tactically prove <*> iterate" in {check(iterated)}
  it should "tactically prove exists generalize" in {check(existsGeneralize)}
  it should "tactically prove = reflexive" in withZ3 { qeTool => check(equalReflexive)}
  it should "tactically prove = commute" in withZ3 { qeTool => check(equalCommute)}
  it should "tactically prove <=" in withZ3 { qeTool => check(lessEqual)}
  it should "tactically prove ! !=" in withZ3 { qeTool => check(notNotEqual)}
  it should "tactically prove ! >=" in withZ3 { qeTool => check(notGreaterEqual)}
  it should "tactically prove >= flip" in withZ3 { qeTool => check(flipGreaterEqual)}
  it should "tactically prove > flip" in withZ3 { qeTool => check(flipGreater)}
  it should "tactically prove all substitute" in {check(allSubstitute)}
  it should "tactically prove vacuous exists" in {check(existsV)}
  it should "tactically prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondet)}
  it should "tactically prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondet)}
  it should "tactically prove \\forall->\\exists" in {check(forallThenExists)}
  //it should "tactically prove DI differential invariance" in {check(DIinvariance)}
  it should "tactically prove DI differential invariant" in {check(DI)}
  it should "tactically prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "tactically prove DW differential weakening" in {check(DW)}
  it should "tactically prove abs" in withZ3 { qeTool => check(abs)}
  it should "tactically prove min" in withZ3 { qeTool => check(min)}
  it should "tactically prove max" in withZ3 { qeTool => check(max)}
  it should "tactically prove openInvariantClosure" in withZ3 { _ => check(openInvariantClosure)}

  "Derived Rule" should "prove allG" in withZ3 { qeTool => allGeneralize.provable.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("p_(||)".asFormula))
  ) }

  it should "prove CT" in withZ3 { qeTool => CTtermCongruence.provable.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("f_(||) = g_(||)".asFormula))
  ) }

  it should "prove [] monotone" in withZ3 { qeTool => monbaxiom.provable.subgoals shouldBe List(
      Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula))
  ) }

  it should "prove [] monotone 2" in withZ3 { qeTool => monb2.provable.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq("q_(||)".asFormula), immutable.IndexedSeq("p_(||)".asFormula))
  ) }

  //@note must be last to populate the lemma database during build
  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in withZ3 { _ =>
    LemmaDBFactory.lemmaDB.deleteDatabase()
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val writeEffect = true
      // use a new instance of the DerivedAxioms singleton object to store all axioms to the lemma database
      val c = Ax.getClass.getDeclaredConstructor()
      c.setAccessible(true)
      c.newInstance().asInstanceOf[Ax.type].prepopulateDerivedLemmaDatabase()

      val cache = new File(Configuration.path(Configuration.Keys.LEMMA_CACHE_PATH))
      // see [[FileLemmaDB.scala]] for path of actual lemma files
      val lemmaFiles = new File(cache.getAbsolutePath + File.separator + "lemmadb").listFiles(new FilenameFilter() {
        override def accept(dir: File, name: String): Boolean = name.endsWith(".alp")
      }).map(_.getName.stripSuffix(".alp"))

      val lemmas = getDerivedAxiomsMirrors.map({ case (valName, m) => valName -> m().asInstanceOf[Lemma] })
      // we allow lazy val forwarding, but all of them have to refer to the same lemma
      val forwards = lemmas.groupBy({ case (_, lemma) => lemma }).filter(_._2.length > 1)
      println("Lemma forwards:\n" + forwards.map(f => f._1.name.getOrElse("<anonymous>") + " <- " + f._2.map(_._1).mkString("[", ",", "]")).mkString("\n"))
      // the lemma database only stores the one lemma referred to from one or more lazy vals
      lemmaFiles.length shouldBe lemmaFiles.distinct.length
      // the lemma database stores all the distinct lemmas in DerivedAxioms
      forwards.keys.flatMap(_.name).toList.diff(lemmaFiles) shouldBe empty

      if (writeEffect) {
        val versionFile = new File(cache.getAbsolutePath + File.separator + "VERSION")
        if (!versionFile.exists()) {
          if (!versionFile.createNewFile()) throw new Exception(s"Could not create ${versionFile.getAbsolutePath}")
        }
        assert(versionFile.exists())
        val fw = new FileWriter(versionFile)
        fw.write(edu.cmu.cs.ls.keymaerax.core.VERSION)
        fw.close()
      }
    }
  }

  /** Returns the reflection mirrors to access the lazy vals in DerivedAxioms. */
  private def getDerivedAxiomsMirrors = {
    val lemmas = Ax.getClass.getDeclaredFields.filter(f => classOf[Lemma].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[Ax.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    //@note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => fn -> ru.typeOf[Ax.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    fields.map(f => f._2.toString -> im.reflectMethod(f._2))
  }
}
