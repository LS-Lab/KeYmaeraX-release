package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._

// @TODO: Add syntax for printable comments, insert comments about where controls need to be added
// @TODO: Add pretty-printer for Kaisar statements
object Totalizer {
  var useComments: Boolean = true

  /** Return pair of controller and plant, if any.
    * If the statement is all-plant or all-controller, we succeed with Triv() for the controller or plant respectively.
    * Failure only occurs when there is not a *unique* controller-plant pair, e.g. when different proof branches have
    * different ODEs. */
  def findController(s: Statement): Option[(Statement, Statement)] = {
    (s, peelPlant(KaisarProof.flatten(List(s)))) match {
      // found the plant
      case (_, Some((plant, rest))) =>
          Some((Triv(), KaisarProof.block(plant :: rest :: Nil)))
      // traverse block. As soon as one ODE is found, everything after that is plant
      case (Block(ss), _) =>
        def findLoop(ss: List[Statement]): Option[(Statement, Statement)] = {
          peelPlant(ss) match {
            case Some((plant, rest)) => Some(Triv(), KaisarProof.block(plant :: rest :: Nil))
            case None =>
              ss match {
                case Nil => Some((Triv(), Triv()))
                case s :: ss =>
                  findController(s) match {
                    case None => None
                    case Some((frontCtrl, Triv())) =>
                      findLoop(ss) match {
                        case None => None
                        case Some((backCtrl, backPlant)) => Some((KaisarProof.block(frontCtrl :: backCtrl :: Nil), backPlant))
                      }
                    case Some((ctrl, frontPlant)) => Some((ctrl, KaisarProof.block(frontPlant :: ss)))
                  }
              }
          }
        }
        val res = findLoop(ss)
        res
        /*val (found, aborted, ctrl, plant) =
          ss.foldLeft[(Boolean, Boolean, Statement, Statement)]((false, false, Triv(), Triv()))({case ((done, aborted, ctrl, plant), s) =>
            if (done || aborted) (done, aborted, ctrl, Context(plant).:+(s).s)
            else {
              findController(s) match {
                // found partial controller
                case Some((someCtrl, Triv())) => (done, aborted, Context(ctrl).:+(someCtrl).s, plant)
                // found plant which terminates the controller
                case Some((someCtrl, somePlant)) => (true, aborted, Context(ctrl).:+(someCtrl).s, Context(plant).:+(somePlant).s)
                case None => (done, true, ctrl, plant)
              }
            }
          })
        if (aborted) None else Some((ctrl, plant))*/
      case (BoxChoice(left, right), _) =>
        (findController(left), findController(right)) match {
          case (Some((cl, pl)), Some((cr, pr))) if pl == pr => Some((BoxChoice(cl, cr), pr))
          case _ => None
        }
      case (Switch(scrut, pats), _) =>
        val founds = pats.map{case ((x, fml, s)) => (x, fml, findController(s))}
        val (xs, fs, ss) = StandardLibrary.unzip3(founds)
        if (ss.contains(None))
          return None
        val (ctrls, plants) = ss.map(_.get).unzip
        val identical = plants.headOption.exists(hd => plants.forall(_ == hd))
        if (identical) {
          Some((Switch(scrut, StandardLibrary.zip3(xs, fs, ctrls)), plants.head))
        } else None
      // All other statements assumed to be a controller with no plant
      case (s, _) => Some(s, Triv())
    }
  }

  /** @return List of branches in branching statements Switch and BoxChoice */
  def toBranches(s: Switch): List[Statement] = s.pats.map(_._3)
  def toBranches(bc: BoxChoice): List[Statement] = {
    bc match {
      case BoxChoice(BoxChoice(a, b), c) => a :: toBranches(BoxChoice(b, c))
      case BoxChoice(a, bc: BoxChoice) => a :: toBranches(bc)
      case hp => List(hp)
    }
  }
  def toBranches(s: Statement): List[Statement] = {
    s match {
      case s: Switch => toBranches(s)
      case bc: BoxChoice => toBranches(bc)
      case _ => List(s)
    }
  }

  /** @return BoxChoice statement which chooses from list of branches */
  def toBoxChoice(ss: List[Statement]): Statement = {
    ss match {
      case Nil => Triv()
      case s :: Nil => s
      case s :: ss => BoxChoice(s, toBoxChoice(ss))
    }
  }

  /** Guess which branch of the branching statement serves as the best template for the fallback statement */
  // Heuristic: Take branch that shares the most bound vars with the fallback
  def guessBranch(branching: Statement, fallback: Option[Statement]): (Statement, Int) = {
    val branches = toBranches(branching).zipWithIndex
    // @TODO: heuristics for when there's no fallback
    val bv = fallback.map(fb => VariableSets(fb).boundVars).getOrElse(Set())
    val withBVs = branches.map({case (s, i) => (VariableSets(s).boundVars, s, i)})
    val byBoundVars = withBVs.sortBy({case (bbv, s, i) => ((bbv ++ bv) -- (bbv.intersect(bv))).size})
    val (_bv, s, i) :: _ = byBoundVars
    (s, i)
  }

  /** @return statement where assumptions have been made into assertions */
  def assertify(s: Statement): Statement = {
    val tf: ProofTraversal.TraversalFunction = new ProofTraversal.TraversalFunction {
      override def preS(kc: Context, kce: Context, s: Statement): Option[Statement] =
        s match {
          case Assume(x, f) => Some(Assert(x, f, Using(List(DefaultSelector), Auto())))
          case _ => None
        }
    }
    ProofTraversal.traverse(Context.empty, Context.empty, s, tf)
  }

  /** @return template where first assignment block is replaced by fallback or by heuristic if no fallback given */
  def replaceControls(template: Statement, fallback: Option[Statement]): Statement = {
    // Set assignments to 0 if you don't know what else to do
    def synthMod(x: Ident, rhs: Option[Term]): (Ident, Option[Term]) = {
      rhs match {
        case Some(_) => (x, rhs)
        case None => (x, Some(Number(0)))
      }
    }
    val (l, x, r) = splitAtAssigns(template)
    val (ll, rr) = (assertify(l), assertify(r))
    val newMods =
      fallback match {
        case Some(fall) => List(fall)
        case None =>
          val comments = if(useComments)  Comment("Auto-generated fallback controller: INSERT PROOF HERE IF NEEDED") :: Nil else Nil
          comments ++
          x.map({case Modify(ids, mods) => Modify(ids, mods.map(xs => synthMod(xs._1, xs._2)))})
      }
    KaisarProof.block(ll :: (newMods ++ List(rr)))
  }

  /** @return branching statement where branch i has been replaced with given branch */
  def joinBranch(branching: Statement, branch: Statement, i: Int): Statement = {
    branching match {
      case Switch(scrut, pats) if i < pats.length =>
        val (front, back) = (pats.take(i), pats.drop(i + 1))
        val (x, f, _) = pats(i)
        val newPats = front ++ ((x, f, branch) :: back)
        Switch(scrut, newPats)
      case bc: BoxChoice =>
        val branches = toBranches(bc)
        val (front, back) = (branches.take(i), branches.drop(i + 1))
        val newBranches = front ++ (branch :: back)
        toBoxChoice(newBranches)
    }
  }

  /** @return whether modify statement is timer initialization of given ODE */
  private def isTimeInit(modify: Modify, pode: ProveODE): Boolean = {
    val tvar = pode.timeVar.getOrElse(ProveODE.defaultTimeVariable)
    modify.boundVars.contains(tvar)
  }

  /** @return whether statement is a branching statement */
  def isBranch(s: Statement): Boolean = s match {case _: BoxChoice | _: Switch => true case _ => false}
  /** @return whether statement is a modify statement */
  def isModify(s: Statement): Boolean = s match {case _: Modify => true case _ => false}
  /** @return return initial plant, if any */
  def peelPlant(s: List[Statement]): Option[(Statement, Statement)] = {
    s match {
      //case (_: ProveODE) :: Nil => Some(s, Triv())
      case ((pode: ProveODE) :: rest) => Some(pode, KaisarProof.block(rest))
      case ((mod: Modify) :: (pode: ProveODE) :: rest) if isTimeInit(mod, pode) => Some(KaisarProof.block(mod :: pode :: Nil), KaisarProof.block(rest))
      case _ => None
    }
  }

  /** Returns header, branching statement, and footer, if any */
  def splitAtBranch(s: Statement): (Statement, Statement, Statement) = {
    s match {
      case _ if isBranch(s) => (Triv(), s, Triv())
      case Block(ss) =>
        val (front, back) = (ss.takeWhile(!isBranch(_)), ss.dropWhile(!isBranch(_)))
          back match {
            case Nil => (s, Triv(), Triv())
            case b :: bs => (KaisarProof.block(front), b, KaisarProof.block(bs))
          }
      case _ => (s, Triv(), Triv())
    }
  }

  /** Split at assignments */
  def splitAtAssigns(s: Statement): (Statement, List[Modify], Statement) = {
    s match {
      case Block(ss) =>
        val (left, rest) = (ss.takeWhile(!isModify(_)), ss.dropWhile(!isModify(_)))
        val (mods, right) = (rest.takeWhile(isModify).asInstanceOf[List[Modify]], rest.dropWhile(isModify))
        (KaisarProof.block(left), mods, KaisarProof.block(right))
      case mod: Modify => (Triv(), List(mod), Triv())
      case _ => (s, Nil, Triv())
    }
  }

  /** TODO: Skip over controllers that are obviously total */
  def mainBody(s: Statement, fallback: Option[Statement]): Option[Statement] = {
    findController(s).flatMap({case (ctrl, plant) =>
      val fullCtrl =
        splitAtBranch(ctrl) match {
          case (ctrl, Triv(), Triv()) =>
            fallback match {
              case Some(fb) => BoxChoice(ctrl, fb)
              case None => BoxChoice(ctrl, replaceControls(ctrl, None))
            }
          case (head, branching, footer) =>
            val (template, i) = guessBranch(branching, fallback)
            val fallen = replaceControls(template, fallback)
            val rebranch = joinBranch(branching, fallen, i)
            KaisarProof.block(head :: rebranch :: footer :: Nil)
        }
      Some(KaisarProof.block(fullCtrl :: plant :: Nil))
    })
  }

  /** @return first BoxLoop found in a possible block of statements */
  def findLoop(s: Statement, fallback: Option[Statement]): Option[Statement] = {
    s match {
      case bl: BoxLoop => mainBody(bl.s, fallback).map(BoxLoop(_))
      case Block(s :: ss) =>
        findLoop(s, fallback) match {
          case Some(found) => Some(Block(found :: ss))
          case None =>
            findLoop(Block(ss), fallback) match {
              case Some(founds) => Some(KaisarProof.block(s :: founds :: Nil))
              case None => None
            }
        }
      case _ => None
    }
  }

  /** Replace partial controllers with total controllers */
  def apply(s: Statement, fallback: Option[Statement]): Statement = {
    findLoop(s, fallback).getOrElse(s)
  }
}