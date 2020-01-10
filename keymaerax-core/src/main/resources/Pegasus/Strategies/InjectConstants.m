(* ::Package:: *)

(* Strategies for augmenting problems with additional constant parameters *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]


BeginPackage["InjectConstants`"]


(* TODO: need to figure out how to communicate "OLD" back *)


InjectOld::usage="InjectOld[problem_List,vars_List] augments the problem with variables remembering the initial state.
If vars is not given, then all variables in the ODE LHS are injected.";


Begin["`Private`"];


InjectOld[problem_List,oldvars_List]:=Module[{pre,post,vf,vars,Q,eqns,vfold,varsold,preold,old,reps},
{pre, { vf, vars, Q }, post} = problem;

old=Map[Symbol[StringJoin["old",SymbolName[#]]]&,oldvars];
eqns=MapThread[Equal,{oldvars,old}];
reps=MapThread[Rule,{oldvars,old}];
vfold=Join[vf,ConstantArray[0,Length[old]]]
varsold=Join[vars,old];
preold=pre//.reps;
{preold&&eqns/.{List->And},{vfold,varsold,Q},post}
];

InjectOld[problem_List]:=Module[{pre,post,vf,vars,Q,eqns},
{pre, { vf, vars, Q }, post} = problem;
InjectOld[problem,vars]
];


End[]
EndPackage[]
