(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["Dependency`",FileNameJoin[{Directory[],"Primitives","Dependency.m"}]]
Needs["GenericNonLinear`",FileNameJoin[{Directory[],"Strategies","GenericNonLinear.m"}]]


BeginPackage["DiffSaturation`"];


(* DiffSat.
SanityTimeout controls how long internal sanity check QE calls take.
StrategyTimeout controls how each sub-strategy call takes *)
DiffSat::usage="DiffSat[problem_List] Apply DiffSat on the input problem"
Options[DiffSat]= {StrategyTimeout -> Infinity};


Begin["`Private`"]


CheckSemiAlgInclusion[subset_,set_,vars_List]:=Module[{},
TrueQ[Reduce[ForAll[vars, Implies[subset,set]],Reals]]
]


FindConst[ff_,var_,symbols_]:=Module[{ls,repr},
ls = {ff//.And -> List}//Flatten;
repr = Select[Cases[ls,Equal[var,rhs_]->rhs],Not[MemberQ[symbols,#]]&]//DeleteDuplicates;
If[Length[repr]>1,Print["Detected multiple values for ",var,repr]];
If[Length[repr]==1,{var -> First[repr]},{}]
]


(* Add sym'=0 to the ODE if the dynamics of sym is undefined *)
AugmentWithParameters[problem_List]:=Module[{pre,post,f,vars,evoConst,symbols,parameters,newvars,newf,
paramrep,paramfixed,paramfree},
{ pre, { f, vars, evoConst }, post } = problem;
symbols=Complement[DeleteDuplicates@Cases[{pre, post, f, evoConst},_Symbol,Infinity], {True, False}];
parameters=Complement[symbols, vars];
(* If the parameters have fixed values in pre then substitute that *)
paramrep=Map[{#,FindConst[pre,#,symbols]}&,parameters];
paramfixed=Map[#[[2]]&,Select[paramrep,Length[#[[2]]]!=0 &]]//Flatten;
paramfree=Map[#[[1]]&,Select[paramrep,Length[#[[2]]]==0&]];
{ pre, { f, vars, evoConst }, post } = problem /. paramfixed;
newvars=Join[vars,paramfree];
newf=Join[f,Table[0,{i,Length[paramfree]}]];
{ pre, { newf, newvars, evoConst }, post }
]


DiffSat[parametricProb_List, opts:OptionsPattern[]]:=Catch[Module[
{problem,pre1,post1,pre,f,vars,evoConst,post,preImpliesPost,
postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,
polyList,invlist,cuts,cutlist,strat,hint,
curproblem,subproblem,deps,curdep,timeoutmultiplier},

(* Bring symbolic parameters into the dynamics *)
Print["Input Problem: ",parametricProb];
problem = AugmentWithParameters[parametricProb];
{ pre1, { f, vars, evoConst }, post1 }=problem;
pre = Primitives`DNFNormalizeGtGeq[pre1];
post=Primitives`DNFNormalizeGtGeq[post1];

Print["Augmented Problem: ", {pre, {f,vars,evoConst}, post}];

strategies = {
{GenericNonLinear`HeuInvariants, Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]},
{GenericNonLinear`FirstIntegrals, Symbol["kyx`ProofHint"]==Symbol["kyx`FirstIntegral"]},
{GenericNonLinear`DbxPoly, Symbol["kyx`ProofHint"]==Symbol["kyx`Darboux"]}
};

invlist=True;
cutlist={};

deps=Join[Dependency`VariableDependencies[problem],{vars}];

(* For each depednency *)
Do[
(* For each strategy *)
Print["Using dependencies: ",curdep];
Do[
{strat,hint}=strathint;
Print["Trying strategy: ",ToString[strat]," ",hint];

curproblem = {pre,{f,vars,evoConst},post};
subproblem=Dependency`FilterVars[curproblem,curdep];

(* Time constrain the cut *)
(* Compute polynomials for the algebraic decomposition of the state space *)
(*Print[subproblem];*)
inv=TimeConstrained[
	strat[subproblem]//DeleteDuplicates,
	OptionValue[StrategyTimeout],
	Print["Strategy timed out after: ",OptionValue[StrategyTimeout]];
	{True,{True}}];
	
(* Simplify invariant w.r.t. the domain constraint *)
cuts=Map[Assuming[evoConst, FullSimplify[#, Reals]]&, inv];

inv=cuts//.{List->And};

Print["Extracted (simplified) invariant(s): ",inv]

(* Needs something like this?
 ecvoConst=And[evoConst,inv[[1]]]; *)
(* Implementation sanity check *)
If[ListQ[cuts],,Print["ERROR, NOT A LIST: ",cuts];Throw[{}]];

If[TrueQ[inv], (*Print["Skipped"]*),
	invlist=And[invlist,inv];
	cutlist=Join[cutlist,Map[{#,hint}&,Select[cuts,Not[TrueQ[#]]&]]];
	evoConst=And[evoConst,inv]];

post=Assuming[evoConst, FullSimplify[post, Reals]];
Print["Cuts: ",cutlist];
Print["Evo: ",evoConst," Post: ",post];
invImpliesPost=CheckSemiAlgInclusion[evoConst, post, vars];
If[TrueQ[invImpliesPost], Print["Generated invariant implies postcondition. Returning."]; Throw[{{invlist,cutlist}, True}],
(*Print["Generated invariant does not imply postcondition. Bad luck; returning what I could find."]*)]
,{strathint, strategies}(* End Do loop *)]
,{curdep,deps}(* End Do loop *)];

(* Throw whatever invariant was last computed *)
Throw[{{invlist,cutlist}, False}]
]]


End[]
EndPackage[]
