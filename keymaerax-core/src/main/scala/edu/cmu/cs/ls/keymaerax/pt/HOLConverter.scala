package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

/** Converts kyx expressions to subset used by hol formalization.
  * Just different enough from Isabelle syntax that it's not so easy to unify them just yet.
  *
  * @author Brandon Bohrer*/
object HOLConverter {

  def apply(t:Term):String = {
    val c = '\"'
    t match {
      case Number(n) => s"(Const ${n.toIntExact}w)"
      //@todo: more robust please
      case FuncOf(Function(n,_,_,_,_),_) => s"(Var $c$n$c)"
      case BaseVariable(n,None,_) => s"(Var $c$n$c)"
      case BaseVariable(n,Some(i),_) => s"(Var $c${n}_$i$c)"
      case Plus(l,r) => s"(Plus ${apply(l)} ${apply(r)})"
      case Times(l,r) => s"(Times ${apply(l)} ${apply(r)})"
    }
  }

  //@todo not needed yet - FOL_R only so far
  def apply(dp:DifferentialProgram):String = {
    ???
  }

  //@todo not needed yet - FOL_R only so far
  def apply(p:Program):String = {
    ???
  }

  def apply(f:Formula):String = {
    f match {
      case And(p,q) => s"(And ${apply(p)} ${apply(q)})"
      case Or(p,q) => s"(Or ${apply(p)} ${apply(q)})"
      case Imply(p,q) => s"(Or ${apply(q)} (Not ${apply(p)}))"
      case Not(p) => s"(Not ${apply(p)})"
      case Equiv(p,q) => s"(Or (And ${apply(p)} ${apply(q)}) (And (Not ${apply(p)}) (Not ${apply(q)})))"
      case NotEqual(l,r) => s"(Not (And (Leq ${apply(l)} ${apply(r)}) (Leq ${apply(r)} ${apply(l)})))"
      case Equal(l,r) => s"(Equals ${apply(l)} ${apply(r)})"
      case LessEqual(l,r) => s"(Leq ${apply(l)} ${apply(r)})"
      case Less(l,r) => s"(And (Leq ${apply(l)} ${apply(r)}) (Not (Leq ${apply(r)} ${apply(l)})))"
      case Greater(l,r) => s"(And (Leq ${apply(r)} ${apply(l)}) (Not (Leq ${apply(l)} ${apply(r)})))"
      case GreaterEqual(l,r) => s"(Leq ${apply(r)} ${apply(l)})"

    }
  }

  def configFile(consts:Set[NamedSymbol],vars:List[Variable],bounds:Formula,init:Formula,outputFml:Formula):String = {
    val const_varsRHS = consts.toList.map({case Function(name,_,_,_,_) => "\"" + name + "()\""}).mkString(";")
    val sensor_pre_varsRHS = vars.map({case BaseVariable(name,_,_) => "\"" + name + "pre\""}).mkString(";")
    val sensor_varsRHS = vars.map({case BaseVariable(name,_,_) => "\""+name+"\""}).mkString(";")
    val ctrl_varsRHS = vars.map({case BaseVariable(name,_,_) => "\""+name+"post\""}).mkString(";")
    val bounds_fmlRHS = apply(bounds)
    val init_fmlRHS = apply(init)
    //@TODO: Appears to not be quite available
    //val plant_fmlRHS = apply(???)
    val ctrl_fmlRHS = apply(outputFml)
    val configFile =
      s"""
        |#The constant variable names
        |const_vars = [$const_varsRHS]
        |#The old sensor names (before plant)
        |sensor_pre_vars = [$sensor_pre_varsRHS]
        |#The new sensor names (after plant)
        |sensor_vars = [$sensor_varsRHS]
        |#The control variable names
        |ctrl_vars = [$ctrl_varsRHS]
        |#The bounds formula
        |bounds_fml = $bounds_fmlRHS
        |#The init formula
        |init_fml = $init_fmlRHS
        |#The control formula
        |ctrl_fml = $ctrl_fmlRHS
      """.stripMargin
      configFile
//    #The plant formula
//    plant_fml = Leq (Times (Var"V()") (Plus (Var"ep()") (Times (Const (-1w)) (Var("t"))))) (Var ("d"))
//    |#The default controller
//      default_body = case (const_ls:word32 list,sense_ls:word32 list) of (_,[d;v;t]) => [d; 0w; 0w] | _ => []

  }

  /*def monitorFmlDef(f:Formula):String = {
    "val monitor_fml = ``" + apply(f) + "`` |> (DEPTH_CONV wordsLib.WORD_GROUND_CONV) |> rconc;;"
  }*/
}
