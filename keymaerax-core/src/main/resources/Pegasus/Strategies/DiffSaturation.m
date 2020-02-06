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


DiffSat[problem_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,f,vars,evoConst,post,preImpliesPost,
postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,
polyList,invlist,cuts,cutlist,strat,hint,
curproblem,subproblem,deps,curdep,timeoutmultiplier,
constvars,constasms},

(* Bring symbolic parameters into the dynamics *)
Print["Input Problem: ", problem];

strategies = {
{GenericNonLinear`HeuInvariants, Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]},
{GenericNonLinear`FirstIntegrals, Symbol["kyx`ProofHint"]==Symbol["kyx`FirstIntegral"]},
{GenericNonLinear`DbxPoly, Symbol["kyx`ProofHint"]==Symbol["kyx`Darboux"]}
};

(* TODO: explicitly use the constvars and constasms below!! *)
{ pre, { f, vars, evoConst }, post, {constvars,constasms}}=problem;


post=Assuming[And[evoConst,constasms], FullSimplify[post, Reals]];

deps=Join[Dependency`VariableDependencies[{pre, { f, vars, evoConst }, post}],{vars}];

invlist=True;
cutlist={};

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
cuts=Map[Assuming[And[evoConst,constasms], FullSimplify[#, Reals]]&, inv];

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

post=Assuming[And[evoConst,constasms], FullSimplify[post, Reals]];
Print["Cuts: ",cutlist];
Print["Evo: ",evoConst," Post: ",post];
invImpliesPost=Primitives`CheckSemiAlgInclusion[And[evoConst,constasms], post, vars];
If[TrueQ[invImpliesPost], Print["Generated invariant implies postcondition. Returning."]; Throw[{{invlist,cutlist}, True}],
(*Print["Generated invariant does not imply postcondition. Bad luck; returning what I could find."]*)]
,{strathint, strategies}(* End Do loop *)]
,{curdep,deps}(* End Do loop *)];

(* Throw whatever invariant was last computed *)
Throw[{{invlist,cutlist}, False}]
]]


End[]
EndPackage[]
