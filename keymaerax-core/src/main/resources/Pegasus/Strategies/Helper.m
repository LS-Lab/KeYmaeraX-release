(* ::Package:: *)

(* Helpers for strategies that don't really standalone
	TODO: can consider moving into Primitives instead?
*)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]


BeginPackage["Helper`"];


(* TODO: need to figure out how to communicate "OLD" back *)


InjectOld::usage="InjectOld[problem_List,vars_List] augments the problem with variables remembering the initial state.
If vars is not given, then all variables in the ODE LHS are injected.";
SplitProblem::usage="SplitProblem[problem_List] splits a problem naturally along disjunctions in the precondition and conjunctions in the postcondition.
To make subsequent handling more straightforward, the structure will always be DNF and a list of lists: { disjunct_i{conjunct_ij} }";


Begin["`Private`"];


InjectOld[problem_List,oldvars_List]:=Module[{pre,post,vf,vars,Q,eqns,vfold,varsold,preold,old,reps},
{pre, { vf, vars, Q }, post} = problem;

old=Map[Symbol[StringJoin["old",SymbolName[#]]]&,oldvars];
eqns=MapThread[Equal,{oldvars,old}];
reps=MapThread[Rule,{oldvars,old}];
vfold=Join[vf,ConstantArray[0,Length[old]]];
varsold=Join[vars,old];
preold=pre//.reps;
{preold&&eqns/.{List->And},{vfold,varsold,Q},post}
];

InjectOld[problem_List]:=Module[{pre,post,vf,vars,Q,eqns},
{pre, { vf, vars, Q }, post} = problem;
InjectOld[problem,vars]
];


SplitProblem[{ pre_, ode_List, post_}]:=Module[
{prenorm,postnorm,prei,posti},

prenorm={Primitives`DNFNormalizeGtGeq[pre]//.{Or -> List}}//Flatten;
postnorm={Primitives`CNFNormalizeGtGeq[post]//.{And -> List}}//Flatten;
Print[prenorm,postnorm];
Map[Function[{prev},Map[{prev,ode,#}&,postnorm]],prenorm]
];


End[]
EndPackage[]
