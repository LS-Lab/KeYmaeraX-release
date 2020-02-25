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
DiffSat::usage="DiffSat[problem_List] Apply DiffSat on the input problem";
Options[DiffSat]= {UseDependencies -> True,StrategyTimeout->Infinity, MinimizeCuts->True};

FormatResult::usage="FormatResult[inv,cuts,proved]
	Formats the result in diff sat result into the right format.
	inv = the generated invariant,
	cuts = list of cuts building that invariant,
	proved = whether this invariant proves the given problem."


Begin["`Private`"]


FormatResult[inv_, cuts_List, proved_]:=Module[{formatcuts},
formatcuts = Map[ {#[[1]], Symbol["Hint"] -> #[[2]]} & ,cuts];
{
	Symbol["ResultType"] -> Symbol["DiffSat"],
	Symbol["Result"] -> {
		Symbol["Invariant"] -> inv,
		Symbol["Cuts"] -> formatcuts,
		Symbol["Proved"] -> proved
	}	
}
]


ReduceCuts[cutlist_List, problem_]:=Module[{pre,f,vars,evoConst,post,constvars,constasms,i,added,rest,cuts},

{ pre, { f, vars, evoConst }, post, {constvars,constasms}} = problem;
cuts=Map[#[[1]]&,cutlist];
added={};

For[i=1,i<=Length[cutlist],i++,
	rest=Drop[cuts,i]/.List->And;
	If[TrueQ[
	And[Primitives`CheckSemiAlgInclusion[And[evoConst,constasms,rest], post, vars],
	LZZ`InvSFast[rest, f, vars, And[evoConst,constasms]]]
	],
		Print["Skipped: ",cuts[[i]]]
		(*Print["INFO: ",rest,f,vars,And[evoConst,constasms],LZZ`InvSFast[rest, f, vars, And[evoConst,constasms]]]*)
		(* skip *),
		added=Join[added,{i}];
		evoConst=And[evoConst,cuts[[i]]]
	];
];

cutlist[[added]]
]


DiffSat[problem_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,f,vars,evoConst,post,preImpliesPost,
postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,
polyList,invlist,cuts,cutlist,strat,hint,
curproblem,subproblem,deps,curdep,timeoutmultiplier,
constvars,constasms,invs},

(* Bring symbolic parameters into the dynamics *)
Print["Input Problem: ", problem];

strategies = {
	{GenericNonLinear`HeuInvariants, Symbol["kyx`Unknown"]},
	{GenericNonLinear`FirstIntegrals, Symbol["kyx`FirstIntegral"]},
	{GenericNonLinear`DbxPoly, Symbol["kyx`Darboux"]},
	{GenericNonLinear`BarrierCert, Symbol["kyx`Barrier"]}
};

(* TODO: explicitly use the constvars and constasms below!! *)
{ pre, { f, vars, evoConst }, post, {constvars,constasms}} = problem;

post=Assuming[And[evoConst,constasms], FullSimplify[post, Reals]];
Print["Postcondition (simplify): ", post];
If[TrueQ[post],
	Print["Postcondition trivally implied by domain constraint. Returning."];
	Throw[FormatResult[True, {}, True]]
	];

deps=If[OptionValue[DiffSat,UseDependencies],
	Join[Dependency`VariableDependencies[{pre, { f, vars, evoConst }, post}],{vars}],
	{vars}
	];

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
subproblem = Dependency`FilterVars[curproblem,curdep];

(* Time constrain the cut *)
(* Compute polynomials for the algebraic decomposition of the state space *)
(*Print[subproblem];*)
invs = TimeConstrained[
	Block[{res},
	res = strat[subproblem];
	If[res==Null,  Print["Warning: Null invariant generated. Defaulting to True"]; res = {True}];
	res]//DeleteDuplicates,
	OptionValue[StrategyTimeout],
	Print["Strategy timed out after: ",OptionValue[StrategyTimeout]];
	{True}];

(* Simplify invariant w.r.t. the domain constraint *)
cuts=Map[Assuming[And[evoConst,constasms], FullSimplify[#, Reals]]&, invs];

inv=cuts//.{List->And};

Print["Extracted (simplified) invariant(s): ", inv]

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
If[TrueQ[invImpliesPost],
	Print["Generated invariant implies postcondition. Returning."];
	If[OptionValue[MinimizeCuts],
		Print["Reducing input cutlist: ", invlist, cutlist];
		cutlist=ReduceCuts[cutlist,problem];
		invlist=Map[#[[1]]&,cutlist]/.List->And;
		];
	Throw[FormatResult[invlist,cutlist, True]]
]
,{strathint, strategies}(* End Do loop *)]
,{curdep,deps}(* End Do loop *)];

(* Throw whatever invariant was last computed *)
Throw[FormatResult[invlist,cutlist, False]];
]]


End[]
EndPackage[]
