package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.Metric
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.VCP
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{SubstitutionHelper, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

object Context {
  // Contexts are proof statements showing what game has been played thus far
  type Context = Statement
  // fact identifier, fact formula, whether fact is from an assignment
  type Finder = ((Ident, Formula, Boolean)) => Boolean
  def empty: Context = Triv()
  def :+(con: Context, s: Statement): Context = {
    con match {
      case _: Triv  => s
      case BoxLoopProgress(bl, pr, ihv, ihf) => BoxLoopProgress(bl, :+(pr, s), ihv, ihf)
      case Block(ss) => Block(ss.:+(s))
      case sl => Block(List(sl, s))
    }
  }

  //def theorem(con: Context): Formula = con.conclusion

  def add(con: Context, x: Ident, fml: Formula): Context = {
    :+(con, Assume(x, fml))
  }

  def sameHead(e: Expression, f: Expression): Boolean = {
    (e, f) match {
      case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
        bcf1.reapply(bcf2.left, bcf2.right) == bcf2
      case (ucf1: UnaryCompositeFormula, ucf2: UnaryCompositeFormula) =>
        ucf1.reapply(ucf2.child) == ucf2
      // No matching in quantified vars or program, so reapply to q1/m1
      case (q1: Quantified, q2: Quantified) => q1.reapply(q1.vars, q2.child) == q2
      case (m1: Modal, m2: Modal) => m1.reapply(m1.program, m2.child) == m2
    }
  }

  // @TODO: generalize to all expressions.
  def matchAssume(e: Expression, f: Formula): Map[Ident, Formula] = {
    e match {
      case BaseVariable(x, _, _) => Map(Variable(x) -> f)
      case _ =>
        if (!sameHead(e, f))
          throw ProofCheckException(s"Pattern $e does not match formula $f")
        (e, f) match {
          case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
            matchAssume(bcf1.left, bcf2.left) ++ matchAssume(bcf1.right, bcf2.right)
          case (ucf1: BinaryCompositeFormula, ucf2: BinaryCompositeFormula) =>
            matchAssume(ucf1.left, ucf2.left)
          case (q1: Quantified, q2: Quantified) => matchAssume(q1.child, q2.child)
          case (m1: Modal, m2: Modal) =>matchAssume(m1.child, m2.child)
        }
    }
  }

  // find most recent element first
  def findAll(mod: Modify, finder: Finder, isGhost: Boolean): List[(Ident, Formula)] = {
    mod match {
      case Modify(TuplePat(pat :: pats), Left(Pair(l, r))) =>
        val left = findAll(Modify(pat, Left(l)), finder, isGhost)
        val right = findAll(Modify(TuplePat(pats), Left(r)), finder, isGhost)
        left ++ right
      case Modify(VarPat(x, Some(p)), Left(f)) if(finder(p, Equal(x, f), false)) =>
        // @TODO: Proper variable renaming
        List((p, Equal(x, f)))
      // default: proof variable name = program variable name
      case Modify(VarPat(x, None), Left(f)) if(finder(x, Equal(x, f), true)) =>
        if (isGhost) {
          List()
          // @TODO: Do we ever want to throw error
          //throw ProofCheckException(s"Ghost variable $x inaccessible because it would escape its scope")
        } else
          List((x, Equal(x, f)))
      case Modify(VarPat(x, Some(_)), Right(())) =>
        throw ProofCheckException("Nondeterministic assignment pattern should not bind proof variable")
      case Modify(_, _) => List()
    }
  }

  def findAll(dc: DomainStatement, f: Finder): List[(Ident, Formula)] = {
    dc match {
      case DomAssume(x, fml) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList//collectFirst({case (mx, mf) if mx == id => mf})
      case DomAssert(x, fml, _ ) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList//collectFirst({case (mx, mf) if mx == id => mf})
      case DomAnd(l, r) => findAll(l, f) ++ findAll(r, f)
      case DomWeak(dc) =>
        findAll(dc, f) match {
          case fml :: _ => throw ProofCheckException(s"Weakened domain constraint $dc binds formula $fml, should not be selected")
          case Nil => Nil
        }
      case DomModify(ap, term) => findAll(Modify(ap, Left(term)), f)
    }
  }

  def signature(con: Context): Set[Function] = {
    con match {
      case lf: LetFun => Set(lf.asFunction)
      case Block(ss) => ss.flatMap(signature).toSet
      case BoxChoice(l, r) => signature(l) ++ signature (r)
      case Switch(sel, pats) => pats.map(_._3).flatMap(signature).toSet
      case Ghost(s) => signature(s)
      case Was(now, was) => signature(now)
      // @TODO: These loop cases probably work, but subtle
      case While(_, _, body) => signature(body)
      case BoxLoop(body) => signature(body)
      case _: Triv | _: Assume | _: Assert | _: Note | _: PrintGoal | _: InverseGhost | _: ProveODE | _: Modify
           | _: Label | _: Match => Set()
    }
  }

  // @TODO: unsound
  def getAssignments(con: Context, x: Variable): List[Formula] =
    searchAll(con,
      {case (v@BaseVariable(xx, idx, _), Equal(BaseVariable(xxx, idxx,_), f), true) if x.name == xx && xx == xxx && idx == idxx => true
      case _ => false
      }, isGhost = false).map(_._2)

  // Look up latest definition of proof variable
  // @TODO: Does this handle state change properly?, Probably only works right for SSA form, or Blocks() needs to check for
  // free variable binding after reference for admissibility
  def searchAll(con: Context, f: Finder, isGhost: Boolean): List[(Ident, Formula)] = {
    con match {
      case _: Triv => Nil
      case Assume(x, g) => matchAssume(x, g).filter({ case (x, y) => f(x, y, false) }).toList
      case Assert(x, g, _) => matchAssume(x, g).filter({ case (x, y) => f(x, y, false) }).toList
      case Note(x, _, Some(g)) => if (f(x, g, false)) List((x, g)) else Nil
      case Note(x, _, None) => throw ProofCheckException("Note in context needs formula annotation") //if (f(x, True)) List((x, True)) else Nil
      //throw ProofCheckException("Note in context needs formula annotation")
      case mod: Modify => findAll(mod, f, isGhost)
      case Block(ss) =>
        def iter(ss: List[Statement], f: Finder): List[(Ident, Formula)] = {
          ss match {
            case Nil => Nil
            case (s: Phi) :: ss =>
              val ff: Finder = ({
                case ((x: Ident, fml: Formula, b: Boolean)) => f(x, substPhi(s, fml), b)
              })
              iter(ss, ff)
            case s :: ss =>
              val left =
                searchAll(s, f, isGhost) match {
                  case ((yx, yf)) :: _ =>
                    val surrounding = Block(ss.reverse)
                    val t = VariableSets(surrounding)
                    val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                    if (inter.nonEmpty) {
                      throw ProofCheckException(s"Fact $yx inaccessible because ghost variable(s) $inter would escape their scope")
                    }
                    List((yx, yf))
                  case Nil => Nil
                }
              left ++ iter(ss, f)
          }
        }

        iter(ss.reverse, f)
      case BoxChoice(l, r) =>
        val and: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            if (k1 != k2) throw ProofCheckException("recursive call found formula twice with different names")
            else (k1, And(v1, v2))
        }
        searchAll(l, f, isGhost) ++ searchAll(r, f, isGhost)
      // @TODO
      case Switch(sel, pats) =>
        val or: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            if (k1 != k2) throw ProofCheckException("recursive call found formula twice with different names")
            else (k1, Or(v1, v2))
        }
        val fmls = pats.flatMap({ case (v, e, s) => searchAll(s, f, isGhost) })
        if (fmls.isEmpty) Nil
        else List(fmls.reduceRight(or))
      case Ghost(s) => searchAll(s, f, isGhost = true)
      case Phi(s) => searchAll(s, f, isGhost = true)
      case InverseGhost(s) => Nil
      /*val xs = Context.taboos(InverseGhost(s)).vars
        search(s, f, isGhost) match {
          case Some(ml) =>
            // @TODO: distinguished exception
            throw ProofCheckException(s"Formula $f should not be selected from statement $s which is an inverse ghost")
          case None => None
        }*/
      case po: ProveODE => findAll(po.dc, f) // @TODO: Needs ghost arg?
      case Was(now, was) => searchAll(now, f, isGhost)
      case _: Label | _: LetFun | _: Match | _: PrintGoal => Nil
      // @TODO: These loop cases probably work, but subtle
      case While(_, _, body) => searchAll(body, f, isGhost)
      case BoxLoop(body) => searchAll(body, f, isGhost)
      case BoxLoopProgress(boxLoop, progress, ihVar, ihFml) =>
        val ihMatch = if(f(ihVar, ihFml, false)) List((ihVar, ihFml)) else List()
        ihMatch ++ searchAll(progress, f, isGhost)
    }
  }

  def findAll(con: Context, f: Finder): List[(Ident, Formula)] = {
    searchAll(con, f, isGhost = false)
  }
  def find(con: Context, f: Finder): Option[(Ident, Formula)] = {
    findAll(con, f).headOption
  }
  def getAll(con: Context, id: Ident, wantProgramVar: Boolean = false): List[Formula] = {
    // if(finder(x, Equal(x, f), true)) =>
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, v: Formula, gotProgramVar) =>
      if (wantProgramVar && gotProgramVar) {
        val Equal(y, f) = v
        id == y
      } else if (wantProgramVar) {
        false
      } else {
        id == x && !gotProgramVar
      }}
    searchAll(con, f, isGhost = false).map(_._2)
  }
  def get(con: Context, id: Ident, wantProgramVar: Boolean = false): Option[Formula] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, v: Formula, gotProgramVar) =>
      if (wantProgramVar && gotProgramVar) {
        val Equal(y, f) = v
        id == y
      } else if (wantProgramVar) {
        false
      } else {
        id == x && !gotProgramVar
      }}
    searchAll(con, f, isGhost = false).map(_._2).headOption
  }

  private def substPhi(phi: Phi, fml: Formula): Formula = {
    val mapping = phi.reverseMap
    val res = SubstitutionHelper.replacesFree(fml)({case v: Variable => mapping.get(v) case f => None})
    res
  }

  def lastFact(con: Context): Option[(Ident, Formula)] = {
    con match {
      case Assume(x: Variable, f) => Some((x, f))
      case Assert(x: Variable, f, _) => Some((x,f))
      case Note(x: Variable, pt, opt) => opt.map((x, _))
      case Modify(VarPat(x, Some(p)), Left(f)) => Some((p, Equal(x, f)))
      case Modify(VarPat(x, _), Left(f)) => Some((x, Equal(x, f)))
      case BoxChoice(l, r) =>
        (lastFact(l), lastFact(r)) match {
          case (Some(resL), Some(resR)) if resL == resR => Some(resL)
          case _ => None
        }
      case BoxLoop(body) => lastFact(body)
      case While(_, _, body) => lastFact(body)
      // Note: After SSA, last statement is phi node, so keep looking to find "real" node
      case Block(ss) =>
        // @TODO: Need a more general way to handle phi assignments
        ss.reverse match {
          case (phi: Phi) :: rest =>
            val fact = rest.map(lastFact).filter(_.isDefined).head
            fact.map({case (x, fml) => (x, substPhi(phi, fml))})
          case ss =>
            ss.map(lastFact).filter(_.isDefined).head
        }
      case Was(now, was) => lastFact(now)
      case Ghost(s) => lastFact(s)
      // Skips all meta nodes and inverse ghosts, for example
      case _ => None
    }
  }

  def contains(con: Context, id: Ident): Boolean = get(con, id).isDefined

  def unifyAll(con: Context, pat: Expression): List[(Ident, Formula)] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, fml: Formula, false) =>
      try {
        UnificationMatch(pat, fml)
        true
      } catch {
        case _: ProverException => false
      }
    case _ => false}
    searchAll(con, f, isGhost = false)
  }
  def unify(con: Context, pat: Expression): Option[(Ident, Formula)] = unifyAll(con, pat).headOption

  // Base name used for fresh variables generated during proof when no better variable name is available.
  val ghostVar: String = "ghost"
  // Extend context with a named assumption
  //def add(ident: String, f: Formula): Context = Context(proofVars.+((ident, f)))

  // @TODO: implement freshProgramVar too

  // A proof variable name which is not bound in the context.
  def fresh(con: Context, ident: String = ghostVar): Ident = {
    var i = 0
    while(contains(con, Variable(ident + i))) {
      i = i + 1
    }
    Variable(ident + i)
  }

  // Define the next gHost variable to be f
  def ghost(con: Context, f: Formula): Context = add(con, fresh(con), f)
}