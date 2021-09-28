(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["Dependency`",FileNameJoin[{Directory[],"Primitives","Dependency.m"}]]
Needs["GenericLinear`",FileNameJoin[{Directory[],"Strategies","GenericLinear.m"}]]
Needs["GenericNonLinear`",FileNameJoin[{Directory[],"Strategies","GenericNonLinear.m"}]]
Needs["Format`",FileNameJoin[{Directory[],"Strategies","Format.m"}]]
Needs["Classifier`",FileNameJoin[{Directory[],"NewClassifier.m"}]]


BeginPackage["DiffSaturation`"]


(* DiffSat.
SanityTimeout controls how long internal sanity check QE calls take.
StrategyTimeout controls how each sub-strategy call takes *)
DiffSat::usage="DiffSat[problem_List, class_List] Apply DiffSat on the input problem, restricting strategies to those matching class"
Options[DiffSat]= {UseDependencies -> True, StrategyTimeout->Infinity, StrictMethodTimeouts -> True, UseDI->True, MinimizeCuts->True}



Begin["`Private`"]


ReduceCuts[cutlist_List, problem_, timeout_]:=Module[{pre,f,vars,evoConst,post,constvars,constasms,i,added,skipped,rest,cuts,stop},

{ pre, { f, vars, evoConst }, post, {constvars,constasms}} = problem;
cuts=Map[#[[1]]&,cutlist];
added={};
skipped={};
stop=False;

TimeConstrained[
	For[i=1,i<=Length[cutlist],i++,
		rest=Drop[cuts,i]/.List->And;
		Print[rest];
		If[stop,
			If[TrueQ[And[Primitives`CheckSemiAlgInclusion[And[evoConst,constasms],cuts[[i]], vars]]],
				(* skip i-th cut if already implied *)
				Print["Skipped: ",cuts[[i]]];
				AppendTo[skipped,{i}],
				added=Join[added,{i}];
				evoConst=And[evoConst,cuts[[i]]]
			],
			If[TrueQ[(*TimeConstrained[*)
				And[Primitives`CheckSemiAlgInclusion[And[evoConst,constasms,rest], post, vars],
						LZZ`InvSFast[rest, Join[f,Table[0,{i,Length[constvars]}]], Join[vars,constvars], And[evoConst,constasms]]]
				(*5,*) (* TODO configuration *)
				(*	False
				]*)
			],
				Print["Skipped: ",cuts[[i]]];
				AppendTo[skipped,{i}]
				(* skip *),
				added=Join[added,{i}];
				evoConst=And[evoConst,cuts[[i]]];
				stop=True
		]];
	];
	cutlist[[added]]
	,
	timeout
	,
	Print["Timeout reduceCuts: ", skipped];
	Delete[cutlist, skipped]
]
]


FullSimplifyReals[fml_]:=Module[{vars,varsreals},
vars = Cases[fml,_Symbol,Infinity];
varsreals=Map[# \[Element] Reals&,vars];
FullSimplify[fml,varsreals]
]


RunStrat[strat_, hint_, stratTimeout_, minimizeCuts_, subproblem_, vars_, inout_List]:=Module[
	{ (* copy of arguments *)
		timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem,
		(* module internal *)
		stratResult, timedInvs, inv, timedInvImpliesPost, invImpliesPost, timedCutlist},

{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem} = inout;

If[stratTimeout <= 1, Return[{False,inout}]]; (* very small timeouts seem to produce unreliable results *)

timedInvs = AbsoluteTiming[
  stratResult = Reap[TimeConstrained[
	Block[{res},
        res = strat[Join[subproblem,{{constvars,constasms}}]];
		If[res==Null,  Print["Warning: Null invariant generated. Defaulting to True"]; res = {True}];
		res]//DeleteDuplicates,
	stratTimeout, {}]];
	If[FailureQ[stratResult[[1]]] || Length[stratResult[[1]]] <= 0,
    (* Failure, timeout etc.: return last intermediate result, if any *)
    If[Length[stratResult[[2]]] > 0, stratResult[[2]][[1]][[-1]], {True}]
    ,
    (* Otherwise: method exhausted all its options *)
    stratResult[[1]]
  ]
];
Print["Strategy ",ToString[strat]," duration: ",timedInvs[[1]]];
AppendTo[timingList,Symbol[ToString[strat]]->timedInvs[[1]]];
invs=timedInvs[[2]];

(* Simplify invariant w.r.t. the domain constraint *)
cuts=Map[Assuming[And[evoConst,constasms], FullSimplifyReals[#]]&, invs]//DeleteDuplicates;

inv=cuts//.{List->And};

Print["Extracted (simplified) invariant(s): ", inv, " from raw candidates: ", invs];

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
	(* Must call InvSDI with the original problem ODE and vars *)
	isDI = AbsoluteTiming[LZZ`InvSDI[post,Join[problem[[2]][[1]],Table[0,{i,Length[constvars]}]], Join[problem[[2]][[2]],constvars], And[evoConst,constasms]]];
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

timedInvImpliesPost=AbsoluteTiming[Primitives`CheckSemiAlgInclusion[And[evoConst,constasms], post, Join[vars,constvars]]];
Print["Invariant check duration: ", timedInvImpliesPost[[1]]];
AppendTo[timingList,Symbol["InvCheck"]->timedInvImpliesPost[[1]]];
invImpliesPost=timedInvImpliesPost[[2]];

If[TrueQ[invImpliesPost],
	Print["Generated invariant implies postcondition. Returning."];
	{True,
	{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post,problem}}
	,
	(* Continue search, return the modified arguments *)
	Print["Generated invariant not yet sufficient. Continuing."];
	{False, {timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem}}
]
]

RedistributeTimeouts[strategies_List, icurrent_Integer, unusedBudget_, opts: OptionsPattern[]]:=Module[{remainingBudget},
	If[TrueQ[OptionValue[DiffSat, StrictMethodTimeouts]],
		(* Strict: reduce remaining budget of icurrent strategy, but don't redistribute *)
		SetOptions[strategies[[icurrent]][[3]], Timeout -> unusedBudget]
		,
		(* Non-strict: redistribute unused budget to other methods *)
		(*Print["Unused budget in ", icurrent, ": ", unusedBudget, " distributing shares of ", unusedBudget/(Length[strategies]-icurrent), " to ", Length[strategies]-icurrent, " remaining strategies"];*)
		(* Same timeout may occur multiple times: reduce by duration before increasing by share of unused budget *)
		If[icurrent < Length[strategies],
			SetOptions[strategies[[icurrent]][[3]], Timeout -> 0],
			(* Reset all to 0, to evenly redistribute below *)
			Do[SetOptions[s[[3]], Timeout -> 0], {s, strategies}]
		];

		(*Do[Print["Budget before redistributing: ", s, " -> ", OptionValue[s, Timeout]], {s, Map[#[[3]]&,strategies]//DeleteDuplicates}];*)
		(*Print["Total remaining budget before: ", Total[Map[OptionValue[#,Timeout]&,Map[#[[3]]&,strategies]//DeleteDuplicates]] + unusedBudget];*)

		(* Distribute unused budget evenly among the remaining methods.
		 * Assumes that strategies contains only activated ones with Timeout > 0. *)
		If[icurrent < Length[strategies],
			Do[
				SetOptions[remaining[[3]], Timeout -> OptionValue[remaining[[3]], Timeout] + unusedBudget/(Length[strategies]-icurrent)];
				(*Print["Modified timeouts: ", ToString[remaining[[1]]], " -> ", OptionValue[remaining[[3]], Timeout]];*)
				,
				{remaining, Drop[strategies,icurrent]}
			],
			Do[
				SetOptions[s[[3]], Timeout -> OptionValue[s[[3]], Timeout] + unusedBudget/Length[strategies]];
				(*Print["Modified timeouts: ", ToString[s[[1]]], " -> ", OptionValue[s[[3]], Timeout]];*)
				,
				{s, strategies}
			]
		]
	];
	remainingBudget = Total[Map[OptionValue[#, Timeout]&, Map[#[[3]]&, strategies]//DeleteDuplicates]];
	Print["Total remaining budget: ", remainingBudget];
	remainingBudget
]

DiffSat[problem_List, class_List, opts: OptionsPattern[]]:=Catch[Module[
	{i,pre,f,vars,origEvo,post,preImpliesPost,
		postInvariant,preInvariant,strategies,inv,andinv,relaxedInv,invImpliesPost,
		polyList,invlist,cuts,cutlist,strat,hint,isLinear,
		curproblem,subproblem,deps,curdep,timeoutmultiplier,
		constvars,constasms,invs,timingList,curvars,collectedCuts,evoConst,genDone,optionsNamespace,
		dummyproblem},

	(* Bring symbolic parameters into the dynamics *)
	Print["Input Problem: ", problem];

	(* {method, proof hint, options namespace, class flag}; keep only activated ones with a timeout > 0 *)
	(* For the class flag, 0 means the strategy should be tried for both linear and nonlinear systems.
		                     1 means linear only.
		                     2 means nonlinear only. *)
	strategies = Module[{activatedStrategies, dimension, classes, problemData,dbxMaxDegree, barrierMidDegree, barrierMaxDegree},
		{dimension, classes, problemData} = class;
		dbxMaxDegree = GenericNonLinear`DbxPolyEndDegree[problem, OptionValue[GenericNonLinear`DbxPoly,MaxDeg]];
		barrierMaxDegree = OptionValue[GenericNonLinear`BarrierCert,Deg];
		barrierMidDegree = Min[5, barrierMaxDegree];
		activatedStrategies = Select[{
			{GenericLinear`LinearMethod, Symbol["kyx`Unknown"] (*Symbol["kyx`LinearMethod"]*), GenericLinear`LinearMethod, 1},
			{GenericLinear`FirstIntegralsLin, Symbol["kyx`FirstIntegral"] (*Symbol["kyx`FirstIntegralsLin"]*), GenericLinear`FirstIntegralsLin, 1},
			{GenericNonLinear`PreservedState, Symbol["kyx`Unknown"], GenericNonLinear`PreservedState, 0},
			{GenericNonLinear`HeuInvariants, Symbol["kyx`Unknown"], GenericNonLinear`HeuInvariants, 0},
			{GenericNonLinear`FirstIntegrals, Symbol["kyx`FirstIntegral"], GenericNonLinear`FirstIntegrals, 2},
			{GenericNonLinear`DbxPolyIntermediate[#,1,2]&, Symbol["kyx`Darboux"], GenericNonLinear`DbxPoly, 0},
			{GenericNonLinear`BarrierCert[#,barrierMidDegree]&, Symbol["kyx`Barrier"], GenericNonLinear`BarrierCert, 0},
			{GenericNonLinear`HeuInvariants, Symbol["kyx`Unknown"], GenericNonLinear`HeuInvariants, 0},
			{GenericNonLinear`DbxPolyIntermediate[#,3,dbxMaxDegree]&, Symbol["kyx`Darboux"], GenericNonLinear`DbxPoly, 0},
			{GenericNonLinear`BarrierCert[#,barrierMaxDegree]&, Symbol["kyx`Barrier"], GenericNonLinear`BarrierCert, 0}
		}, (OptionValue[#[[3]], Timeout] > 0)&];
		classes/.{
			{"Linear"} -> Select[activatedStrategies, (#[[4]] <= 1)&],
			_List -> Select[activatedStrategies, (#[[4]] != 1)&]
		}
	];

	Print["Activated strategies: ", strategies];
	Print["Total budget: ", Total[Map[OptionValue[#,Timeout]&,Map[#[[3]]&,strategies]//DeleteDuplicates]]];

	(* TODO: explicitly use the constvars and constasms below!! *)
	{ pre, { f, vars, evoConst }, post, {constvars,constasms}} = problem;

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
	cutlist={};
	timingList={};

	If[Length[deps] > 1,
		(* Fast check: extract from initial conditions, but only when more than a single dependency cluster *)
		{genDone, {timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, dummyproblem}} =
				RunStrat[GenericNonLinear`PreservedState, Symbol["kyx`Unknown"],
					OptionValue[StrategyTimeout], OptionValue[MinimizeCuts],
					{ pre, { f, vars, evoConst }, post }, vars,
					{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem}];

		If[TrueQ[genDone],
			Print["Generated invariant implies postcondition. Returning."];
			If[OptionValue[MinimizeCuts],
				Print["Reducing input cutlist: ", invlist, cutlist];
				invlist=Map[#[[1]]&,cutlist]/.List->And;
			];
			Throw[Format`FormatDiffSat[invlist, cutlist, timingList, True]]
		]
	];

	(* For each dependency *)
	Do[
		(* For each strategy *)
		Print["Using dependencies: ",curdep];
		For[i=1, i<=Length[strategies], i++,
			{strat,hint,optionsNamespace,isLinear}=strategies[[i]];
			Print["Trying strategy: ",ToString[strat]," ",hint];

			curproblem = {pre,{f,vars,evoConst},post};
			curvars=Join[curdep,constvars];
			subproblem = Dependency`FilterVars[curproblem, curvars];

			(* Time constrain the cut *)
			(* Compute polynomials for the algebraic decomposition of the state space *)
			(*Print[subproblem];*)

			Module[{timedStratResult, duration, timedCutlist, stratTimeout, remainingBudget},
				stratTimeout = OptionValue[optionsNamespace, Timeout];
				Print["Method timeout: ", stratTimeout];

				timedStratResult = AbsoluteTiming[
					RunStrat[strat, hint, stratTimeout, OptionValue[MinimizeCuts],
						subproblem, vars,
						{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem}]
				];

				duration = timedStratResult[[1]];
				Print["Method duration: ", duration];
				remainingBudget = RedistributeTimeouts[strategies, i, Max[0, stratTimeout - duration]];

				{genDone, {timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, dummyproblem}} = timedStratResult[[2]];
				If[TrueQ[genDone],
					Print["Generated invariant implies postcondition. Returning."];
					If[OptionValue[MinimizeCuts] && remainingBudget>0,
						Print["Reducing input cutlist: ", invlist, cutlist];
						timedCutlist=AbsoluteTiming[ReduceCuts[cutlist, problem, remainingBudget]];
						Print["Reducing cuts duration: ", timedCutlist[[1]]];
						AppendTo[timingList, Symbol["ReduceCuts"]->timedCutlist[[1]]];
						cutlist=timedCutlist[[2]];
						invlist=Map[#[[1]]&,cutlist]/.List->And;
					];
					Throw[Format`FormatDiffSat[invlist, cutlist, timingList, True]]
					,
					(* not fully done yet, but perhaps cluster done? *)
					Module[{subpre,subf,subvars,subh,subpost,clusterDone},
						{subpre,{subf,subvars,subh},subpost} = subproblem;
						clusterDone = Primitives`CheckSemiAlgInclusion[And[evoConst,constasms], subpost, subvars];
						Print["Cluster done: ", clusterDone];
						If[clusterDone, Break[]]
					]
				];

				If[remainingBudget <= 0, Throw[Format`FormatDiffSat[invlist, cutlist, timingList, False]]]
			]

		(* End For loop *)
		];

		(* Redistribute for next dependencies cluster *)
		If[TrueQ[OptionValue[DiffSat, StrictMethodTimeouts]],
			Print["Strict method timeouts, skipping redistribution between dependency clusters"]
			,
			RedistributeTimeouts[strategies, Length[strategies], Total[Map[OptionValue[#,Timeout]&,Map[#[[3]]&,strategies]//DeleteDuplicates]]]
		]
		,
		{curdep,deps}
		(* End Do loop *)
	];
	Throw[Format`FormatDiffSat[invlist, cutlist, timingList, False]]

]]

DiffSatRecurse[problem_List, collectedResults_List:{{},{}}, dbxStaggeredStart_:1, opts:OptionsPattern[]]:=Catch[Module[
{i,pre,f,vars,origEvo,post,preImpliesPost,
postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,
polyList,invlist,cuts,cutlist,strat,hint,isLinear,
curproblem,subproblem,deps,curdep,timeoutmultiplier,
constvars,constasms,invs,timingList,curvars,collectedCuts,evoConst,optionsNamespace,dbxPolyStart,dbxPolyEnd},

(* Bring symbolic parameters into the dynamics *)
Print["Input Problem: ", problem];

dbxPolyStart = If[TrueQ[OptionValue[GenericNonLinear`DbxPoly, Staggered]], dbxStaggeredStart, 1];
dbxPolyEnd = GenericNonlinear`DbxPolyEndDegree[If[TrueQ[OptionValue[GenericNonLinear`DbxPoly, Staggered]],
	If[OptionValue[GenericNonLinear`DbxPoly,MaxDeg]<0, dbxStaggeredStart, Min[dbxStaggeredStart, OptionValue[GenericNonLinear`DbxPoly,MaxDeg]]],
	OptionValue[GenericNonLinear`DbxPoly,MaxDeg]]
];

(* {method, proof hint, linear/nonlinear flag, options namespace}; keep only activated ones with a timeout > 0 *)
(* For the flag, 0 means the strategy should be tried for both linear and nonlinear systems.  
		1 means linear only.
		2 means nonlinear only. *)
strategies = Select[{
  (*{GenericLinear`LinearMethod, Symbol["kyx`Unknown"] (*Symbol["kyx`LinearMethod"]*), GenericLinear`LinearMethod, 1},
  {GenericLinear`FirstIntegralsLin, Symbol["kyx`FirstIntegral"] (*Symbol["kyx`FirstIntegralsLin"]*), GenericLinear`FirstIntegralsLin, 1},*)
	{GenericNonLinear`PreservedState, Symbol["kyx`Unknown"], GenericNonLinear`PreservedState, 0},
	{GenericNonLinear`HeuInvariants, Symbol["kyx`Unknown"], GenericNonLinear`HeuInvariants, 0},
	{GenericNonLinear`FirstIntegrals, Symbol["kyx`FirstIntegral"], GenericNonLinear`FirstIntegrals, 2},
	{GenericNonLinear`DbxPolyIntermediate[#, dbxPolyStart, dbxPolyEnd]&, Symbol["kyx`Darboux"], GenericNonLinear`DbxPoly, 0},
	{GenericNonLinear`BarrierCert, Symbol["kyx`Barrier"], GenericNonLinear`BarrierCert, 0}
}, (OptionValue[#[[3]], Timeout] > 0)&];

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
{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem} =
    RunStrat[GenericNonLinear`PreservedState, Symbol["kyx`Unknown"],
			OptionValue[StrategyTimeout], OptionValue[MinimizeCuts],
			{ pre, { f, vars, evoConst }, post }, vars,
			{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem}];

(* For each dependency *)
Do[
(* For each strategy *)
Print["Using dependencies: ",curdep];
For[i=1, i<=Length[strategies], i++,
{strat,hint,optionsNamespace,isLinear}=strategies[[i]];
Print["Trying strategy: ",ToString[strat]," ",hint];

curproblem = {pre,{f,vars,evoConst},post};
curvars=Join[curdep,constvars];
subproblem = Dependency`FilterVars[curproblem, curvars];

(* Filter out inappropriate strategies based on linear/nonlinear classification *)
If[isLinear == 1 && Classifier`LinearSystemQ[f, vars] == False, Print["Problem is nonlinear but strategy is designed for linear systems, moving on"]; Continue[]];
If[isLinear == 2 && Classifier`LinearSystemQ[f, vars] == True, Print["Problem is linear but strategy is designed for nonlinear systems, moving on"]; Continue[]];

(* Time constrain the cut *)
(* Compute polynomials for the algebraic decomposition of the state space *)
(*Print[subproblem];*)


Module[{timedStratResult, duration, unusedBudget, genDone},
	Print["Method timeout: ", OptionValue[optionsNamespace, Timeout]];

	timedStratResult = AbsoluteTiming[
		RunStrat[strat, hint, OptionValue[StrategyTimeout], OptionValue[MinimizeCuts],
			subproblem, vars,
			{timingList, invs, cuts, invlist, cutlist, evoConst, constvars, constasms, post, problem}]
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

	{genDone, {timingList, invs, cuts, invlist, cutlist, evoConst, constasms, post, problem}} = timedStratResult[[2]];
	If[TrueQ[genDone],
		Print["Generated invariant implies postcondition. Returning."];
		If[minimizeCuts,
			Print["Reducing input cutlist: ", invlist, cutlist];
			timedCutlist=AbsoluteTiming[ReduceCuts[cutlist,problem]];
			Print["Reducing cuts duration: ", timedCutlist[[1]]];
			AppendTo[timingList, Symbol["ReduceCuts"]->timedCutlist[[1]]];
			cutlist=timedCutlist[[2]];
			invlist=Map[#[[1]]&,cutlist]/.List->And;
		];
		Throw[Format`FormatDiffSat[invlist, cutlist, timingList, True]]
	]
]

(* End For loop *)]
,{curdep,deps}(* End Do loop *)];

(* Not yet done, repeat with candidates so far as seeds, if any (as collected by cutlist and evoConst) *)
If[Length[cutlist] > Length[collectedCuts] ||
		(TrueQ[OptionValue[GenericNonLinear`DbxPoly, Staggered]] && dbxPolyStart <= dbxPolyEnd),
	Print["Recursing into DiffSat with candidates so far as seeds."];
	DiffSat[problem, { cutlist, evoConst },
		If[Length[cutlist] > Length[collectedCuts], 1, dbxStaggeredStart+1]
	],
	(* Throw whatever invariant was last computed *)
	Print["No new insights, exiting with last computed invariant."];
	Throw[Format`FormatDiffSat[invlist, cutlist, timingList, False]]
]

]]


End[]
EndPackage[]
