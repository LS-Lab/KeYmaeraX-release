(* ::Package:: *)

(* Helpers for strategies that don't really standalone
	TODO: can consider moving into Primitives instead?
*)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]


BeginPackage["Helper`"];


(* TODO: need to figure out how to communicate "OLD" back *)


SplitAssums::usage="SplitAssums[ff,vars] returns the assumptions that depend only on vars and those that may depend on others"
InjectOld::usage="InjectOld[problem_List,vars_List] augments the problem with variables remembering the initial state.
If vars list is not given, then all variables in the ODE LHS are injected.";
SplitProblem::usage="SplitProblem[problem_List] splits a problem naturally along disjunctions in the precondition and conjunctions in the postcondition.
To make subsequent handling more straightforward, the structure will always be DNF and a list of lists: { disjunct_i{conjunct_ij} }";


Begin["`Private`"];


SplitAssums[ff_,vars_]:=Module[{ls},
ls = {ff//.And -> List}//Flatten;
{Select[ls,Complement[DeleteDuplicates@Cases[#, _Symbol, Infinity],vars]!={}&]//.List->And,
Select[ls,Complement[DeleteDuplicates@Cases[#, _Symbol, Infinity],vars]=={}&]//.List->And}
]


InjectOld[problem_List,oldvars_List]:=Module[{
pre,post,vf,vars,Q,eqns,preold,old,reps,constvars,constQ,pre1,pre2},
{pre, { vf, vars, Q }, post, {constvars,constQ}} = problem;

old=Map[Symbol[StringJoin["old",SymbolName[#]]]&,oldvars];
eqns=MapThread[Equal,{oldvars,old}];
reps=MapThread[Rule,{oldvars,old}];

{pre1,pre2} = SplitAssums[pre,oldvars];

preold=pre2//.reps;
{{pre1&&eqns/.{List->And},{vf,vars,Q},post, {old,preold}}, reps}
];

InjectOld[problem_List]:=Module[{pre,post,vf,vars,Q,eqns,constvars,constQ},
{pre, { vf, vars, Q }, post, {constvars,constQ}} = problem;
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
