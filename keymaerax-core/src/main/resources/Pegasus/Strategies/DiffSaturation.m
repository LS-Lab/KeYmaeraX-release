(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["Dependency`",FileNameJoin[{Directory[],"Primitives","Dependency.m"}]]
Needs["GenericNonLinear`",FileNameJoin[{Directory[],"Strategies","GenericNonLinear.m"}]]
Needs["Format`",FileNameJoin[{Directory[],"Strategies","Format.m"}]]


BeginPackage["DiffSaturation`"];


(* DiffSat.
SanityTimeout controls how long internal sanity check QE calls take.
StrategyTimeout controls how each sub-strategy call takes *)
DiffSat::usage="DiffSat[problem_List] Apply DiffSat on the input problem";
Options[DiffSat]= {UseDependencies -> True, StrategyTimeout->Infinity, UseDI->True, MinimizeCuts->True};


Begin["`Private`"]


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


FullSimplifyReals[fml_]:=Module[{vars,varsreals},
vars = Cases[fml,_Symbol,Infinity];
varsreals=Map[# \[Element] Reals&,vars];
FullSimplify[fml,varsreals]
]


RunStrat[strat_, hint_, stratTimeout_, minimizeCuts_, subproblem_, vars_, inout_List]:=Module[
	{ (* copy of arguments *)
		timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post, problem,
		(* module internal *)
		timedInvs, inv, timedInvImpliesPost, invImpliesPost, timedCutlist},
{timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post, problem} = inout;
timedInvs = AbsoluteTiming[TimeConstrained[
	Block[{res},
		res = strat[subproblem];
		If[res==Null,  Print["Warning: Null invariant generated. Defaulting to True"]; res = {True}];
		res]//DeleteDuplicates,
	stratTimeout,
	Print["Strategy timed out after: ", stratTimeout];
	{True}]];
Print["Strategy ",ToString[strat]," duration: ",timedInvs[[1]]];
AppendTo[timingList,Symbol[ToString[strat]]->timedInvs[[1]]];
invs=timedInvs[[2]];

(* Simplify invariant w.r.t. the domain constraint *)
cuts=Map[Assuming[And[evoConst,constasms], FullSimplifyReals[#]]&, invs]//DeleteDuplicates;

inv=cuts//.{List->And};

Print["Extracted (simplified) invariant(s): ", inv];

If[Not[ListQ[cuts]],
	Throw[Format`FormatErr["DiffSat did not produce a list of cuts: "<>ToString[cuts],True]]];

If[TrueQ[inv], Print["Skipping trivial true"],
	invlist=And[invlist,inv];
	cutlist=Join[cutlist,Map[{#,hint}&,Select[cuts,Not[TrueQ[#]]&]]];
	evoConst=And[evoConst,inv]];

post=Assuming[And[evoConst,constasms], FullSimplifyReals[post]];
Print["Cuts: ",cutlist];
Print["Evo: ",evoConst," Post: ",post];

Print["InvList ", invlist];
If[Length[cuts] > 0, Sow[Format`FormatDiffSat[invlist, cutlist, timingList, False]]];

(* Check that postcondition is a DI. If so, add it to the invariant list
	TODO: extend with other options, like InvS or InvSFast?
*)
If[OptionValue[DiffSat,UseDI] && Not[TrueQ[post]],
	Block[{isDI},
	isDI = AbsoluteTiming[LZZ`InvSDI[post,subproblem[[2]][[1]], subproblem[[2]][[2]], And[evoConst,constasms]]];
	Print["DI inv check duration: ", isDI[[1]]];
    AppendTo[timingList,Symbol["InvCheck"]->isDI[[1]]];
	If[TrueQ[isDI[[2]]],
		Print["Postcondition proves by DI."];
		invlist=And[invlist,post];
		cutlist=Join[cutlist,{{post, Symbol["kyx`Unknown"] (*Symbol["kyx`DI"] *)}}];
		evoConst=And[evoConst,post];
		post=True
	]
	]	
];

timedInvImpliesPost=AbsoluteTiming[Primitives`CheckSemiAlgInclusion[And[evoConst,constasms], post, vars]];
Print["Invariant check duration: ", timedInvImpliesPost[[1]]];
AppendTo[timingList,Symbol["InvCheck"]->timedInvImpliesPost[[1]]];
invImpliesPost=timedInvImpliesPost[[2]];

If[TrueQ[invImpliesPost],
	Print["Generated invariant implies postcondition. Returning."];
	If[minimizeCuts,
		Print["Reducing input cutlist: ", invlist, cutlist];
		timedCutlist=AbsoluteTiming[ReduceCuts[cutlist,problem]];
		Print["Reducing cuts duration: ", timedCutlist[[1]]];
		AppendTo[timingList, Symbol["ReduceCuts"]->timedCutlist[[1]]];
		cutlist=timedCutlist[[2]];
		invlist=Map[#[[1]]&,cutlist]/.List->And;
	];
	Throw[Format`FormatDiffSat[invlist, cutlist, timingList, True]],
	(* Continue search, return the modified arguments *)
	Print["Generated invariant not yet sufficient. Continuing."];
	{timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post}
]
]

DiffSat[problem_List, collectedResults_List:{{},{}}, iteration_:1, opts:OptionsPattern[]]:=Catch[Module[
{pre,f,vars,origEvo,post,preImpliesPost,
postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,
polyList,invlist,cuts,cutlist,strat,hint,
curproblem,subproblem,deps,curdep,timeoutmultiplier,
constvars,constasms,invs,timingList,curvars,collectedCuts,evoConst,optionsNamespace},

(* Staggered Darboux: adapt degree by iteration *)
If[TrueQ[OptionValue[GenericNonLinear`DbxPoly, Staggered]],
	SetOptions[GenericNonLinear`DbxPoly, CurDeg ->
     If[OptionValue[GenericNonLinear`DbxPoly, EndDeg] < 0,
			 iteration,
			 Min[OptionValue[GenericNonLinear`DbxPoly, EndDeg], iteration]]]
	,
	SetOptions[GenericNonLinear`DbxPoly, CurDeg -> OptionValue[GenericNonLinear`DbxPoly, EndDeg]]
];

(* Bring symbolic parameters into the dynamics *)
Print["Input Problem: ", problem];

(* {method, proof hint, options namespace}; keep only activated ones with a timeout > 0 *)
strategies = Select[{
	{GenericNonLinear`PreservedState, Symbol["kyx`Unknown"], GenericNonLinear`PreservedState},
	{GenericNonLinear`HeuInvariants, Symbol["kyx`Unknown"], GenericNonLinear`HeuInvariants},
	{GenericNonLinear`FirstIntegrals, Symbol["kyx`FirstIntegral"], GenericNonLinear`FirstIntegrals},
	{GenericNonLinear`DbxPolyIntermediate, Symbol["kyx`Darboux"], GenericNonLinear`DbxPoly},
	{GenericNonLinear`BarrierCert, Symbol["kyx`Barrier"], GenericNonLinear`BarrierCert}
}, (OptionValue[Last[#], Timeout] > 0)&];

Print["Activated strategies: ", strategies];

(* TODO: explicitly use the constvars and constasms below!! *)
{ pre, { f, vars, origEvo }, post, {constvars,constasms}} = problem;

{ collectedCuts, evoConst } = collectedResults;
evoConst = evoConst/.{{} -> origEvo};

Print["consts: ",constasms];
post=Assuming[And[evoConst,constasms], FullSimplifyReals[post]];
Print["Postcondition (simplify): ", post];
If[TrueQ[post],
	Print["Postcondition trivally implied by domain constraint. Returning."];
	Throw[Format`FormatTriv[4]]
	];

deps=If[OptionValue[DiffSat,UseDependencies],
	Join[Dependency`VariableDependencies[{pre, { f, vars, evoConst }, post}],{vars}],
	{vars}
	]//DeleteDuplicates;

invlist=True;
cutlist=collectedCuts;
timingList={};

(* Fast check: extract from initial conditions *)
{timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post} =
    RunStrat[GenericNonLinear`PreservedState, Symbol["kyx`Unknown"],
			OptionValue[StrategyTimeout], OptionValue[MinimizeCuts],
			{ pre, { f, vars, evoConst }, post }, vars,
			{timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post, problem}];

(* For each dependency *)
Do[
(* For each strategy *)
Print["Using dependencies: ",curdep];
For[i=1, i<=Length[strategies], i++,
{strat,hint,optionsNamespace}=strategies[[i]];
Print["Trying strategy: ",ToString[strat]," ",hint];

curproblem = {pre,{f,vars,evoConst},post};
curvars=Join[curdep,constvars];
subproblem = Dependency`FilterVars[curproblem, curvars];

(* Time constrain the cut *)
(* Compute polynomials for the algebraic decomposition of the state space *)
(*Print[subproblem];*)

Module[{timedStratResult, duration, unusedBudget},
	Print["Method timeout: ", OptionValue[optionsNamespace, Timeout]];

	timedStratResult = AbsoluteTiming[
		RunStrat[strat, hint, OptionValue[StrategyTimeout], OptionValue[MinimizeCuts],
			subproblem, vars,
			{timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post, problem}]
	];

	duration = timedStratResult[[1]];
	Print["Method duration: ", duration];
	unusedBudget = Max[0, OptionValue[optionsNamespace, Timeout] - duration];
	Print["Unused budget: ", unusedBudget];

	(* Distribute unused budget evenly among the remaining methods (evenly among all if last before recursing).
	 * Assumes that strategies contains only activated ones with Timeout > 0. *)
	If[i < Length[strategies],
		Do[
			SetOptions[remaining[[3]], Timeout -> OptionValue[remaining[[3]], Timeout] + unusedBudget/(Length[strategies]-i)];
			Print["Modified timeouts: ", ToString[remaining[[1]]], " -> ", OptionValue[remaining[[3]], Timeout]];
			,
			{remaining, Drop[strategies,i]}
		],
		Do[
			SetOptions[remaining[[3]], Timeout -> unusedBudget/Length[strategies]];
			Print["Modified timeouts: ", ToString[remaining[[1]]], " -> ", OptionValue[remaining[[3]], Timeout]];
			,
			{remaining, strategies}
		]
	];

	{timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post} = timedStratResult[[2]]
]

(* End For loop *)]
,{curdep,deps}(* End Do loop *)];

If[Length[cutlist] > Length[collectedCuts],
	SetOptions[GenericNonLinear`DbxPoly, StartDeg -> 1],
	SetOptions[GenericNonLinear`DbxPoly, StartDeg -> iteration+1]
];

(* Not yet done, repeat with candidates so far as seeds, if any (as collected by cutlist and evoConst) *)
If[Length[cutlist] > Length[collectedCuts] ||
		(TrueQ[OptionValue[GenericNonLinear`DbxPoly, Staggered]] && OptionValue[GenericNonLinear`DbxPoly, StartDeg] <= OptionValue[GenericNonLinear`DbxPoly, EndDeg]),
	Print["Recursing into DiffSat with candidates so far as seeds."];
	DiffSat[problem, { cutlist, evoConst }, iteration+1],
	(* Throw whatever invariant was last computed *)
	Print["No new insights, exiting with last computed invariant."];
	Throw[Format`FormatDiffSat[invlist, cutlist, timingList, False]]
]

]]


End[]
EndPackage[]
