(* ::Package:: *)

Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] 
(*Needs["DiscreteAbstraction`",FileNameJoin[{Directory[],"Primitives","DiscreteAbstraction.m"}]] *)


BeginPackage["InvariantExtractor`"];

DWC::usage="DWC[problem_List, A0_List, cuts_List, useFirstRoundDW_]
    Iteratively refine evolution constraint using differential cuts before computing the abstraction.
    Set useFirstRoundDW to false when other checks in the strategy redundantly check for it (DiffSat does)."
(*
DWCLZR::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] 
    Iteratively refine evolution constraint using differential cuts before computing the abstraction."
*)


Begin["`Private`"]


DoNotSimplify[formula_, assumptions_]:=Module[{},
formula
]


Options[DWC]= {
	TransitionRemovalMethod->"LZZ-vanilla",
	Parallel->False,
	SimplifyInvariant->DoNotSimplify,
	Smallest->False,
	WorkingPrecision -> \[Infinity],
	Timeout-> \[Infinity],
	SufficiencyTimeout -> 0,
	DWTimeout -> 0
};

DWC[problem_List, A0_List, cuts_List, useFirstRoundDW_, retryCandidates_:True, checks_List:{"=",">","<",">=","<="}, opts:OptionsPattern[]]:=
Catch[
Module[{pre,post,GT,EQ,LT,p,f,vars,H0,constvars,constasms,allvars,allf},

{pre,{f,vars,H0},post,{constvars,constasms}} = problem;
allvars=Join[vars,constvars];
allf= Join[f,Table[0,{i,Length[constvars]}]];
SetOptions[Resolve,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWC, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> DoNotSimplify};
USEDW=And[useFirstRoundDW, Not[TrueQ[OptionValue[Smallest]/.{True->True, _->False}]]];

(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[OptionValue[SufficiencyTimeout] > 0,
	Print["Sufficiency check ", H0, " overlaps ", pre];
	If[TrueQ[TimeConstrained[Resolve[Not[Exists[Evaluate[allvars], constasms && H0 && pre]],Reals], OptionValue[SufficiencyTimeout], False]],
		Print["No overlap ", H0, " with ", pre]; Throw[{False, cuts}] ]
	,
	Print["Sufficiency check skipped"]
];

(* DW check: should be disabled on the very first call, because it is often redundant to checks outside the extractor. *)
If[USEDW && OptionValue[DWTimeout] > 0,
	If[TrueQ[TimeConstrained[Resolve[ForAll[Evaluate[allvars],Implies[constasms && H0, post]],Reals], OptionValue[DWTimeout], False]],
		Print["DW"]; Throw[{H0, cuts}] ]
	,
	Print["DW check skipped"]
];

Print["Simplifying"];

(* Main loop *)
Do[p=SIMPLIFY[A0[[i]],H0]; 

Print["Trying: ",p];

(* DC check 0 *)
If[(MemberQ[checks, "="] && TrueQ[Resolve[ForAll[Evaluate[allvars],Implies[H0 && pre && constasms, p==0]],Reals]]) && (TrueQ[LZZ`InvSFast[p==0, allf, allvars, H0 && constasms]]),
Print["DC on ", p==0];
Sow[Join[cuts, {p==0}]];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(constvars && H0 && p==0), Reals]},post,{constvars,constasms}}, If[retryCandidates, Delete[A0,i], Drop[A0,i]], Join[cuts,{p==0}], True]]
];

(* DC strict check 1 *)
If[(MemberQ[checks, ">"] && TrueQ[Resolve[ForAll[Evaluate[allvars],Implies[H0 && pre && constasms, p>0]],Reals]]) && (TrueQ[LZZ`InvSFast[p>0, allf, allvars, H0 && constasms]]),
Print["DC on ", p>0];
Sow[Join[cuts, {p>0}]];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p>0), Reals]},post,{constvars,constasms}}, If[retryCandidates, Delete[A0,i], Drop[A0,i]], Join[cuts,{p>0}], True]]
];

(* DC strict check 2 *)
If[(MemberQ[checks, "<"] && TrueQ[Resolve[ForAll[Evaluate[allvars],Implies[H0 && pre && constasms, p<0]],Reals]]) && (TrueQ[LZZ`InvSFast[p<0, allf, allvars, H0 && constasms]]),
Print["DC on ", p<0];
Sow[Join[cuts, {p<0}]];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p<0), Reals]},post,{constvars,constasms}}, If[retryCandidates, Delete[A0,i], Drop[A0,i]], Join[cuts,{p<0}], True]]
];

(* DC nonstrict check 1 *)
If[(MemberQ[checks, ">="] && TrueQ[Resolve[ForAll[Evaluate[allvars],Implies[H0 && pre && constasms, p>=0]],Reals]]) && (TrueQ[LZZ`InvSFast[p>=0, allf, allvars, H0 && constasms]]),
Print["DC on ", p>=0];
Sow[Join[cuts, {p>=0}]];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p>=0), Reals]},post,{constvars,constasms}}, If[retryCandidates, Delete[A0,i], Drop[A0,i]], Join[cuts,{p>=0}], True]]
];

(* DC nonstrict check 2 *)
If[(MemberQ[checks, "<="] && TrueQ[Resolve[ForAll[Evaluate[allvars],Implies[H0 && pre && constasms, p<=0]],Reals]]) && (TrueQ[LZZ`InvSFast[p<=0, allf, allvars, H0 && constasms]]),
Print["DC on ", p<=0];
Sow[Join[cuts, {p<=0}]];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p<=0), Reals]},post,{constvars,constasms}}, If[retryCandidates, Delete[A0,i], Drop[A0,i]], Join[cuts,{p<=0}], True]]
];

,{i,1,Length[A0]}]; (* End of main loop *)

Print["No more cuts ... "];

Throw[{H0, cuts}]
]]


Options[DWCLZR]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->FullSimplify, WorkingPrecision -> \[Infinity]};

DWCLZR[precond_, postcond_, system_List, A0_List, opts:OptionsPattern[]]:=Catch[
Module[{GT,EQ,LT,p,f=system[[1]],vars=system[[2]],H0=system[[3]]},

SetOptions[Resolve,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWCLZR, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];


(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[TrueQ[Resolve[ForAll[Evaluate[vars],Not[H0 && precond]],Reals]], Throw[False] ]; 

(* DW check *)
If[TrueQ[Resolve[ForAll[Evaluate[vars],Implies[H0, postcond]],Reals]], Throw[H0] ]; 

(* Main loop *)
Do[p=A0[[i]];

(* DC check 1 *)
If[(TrueQ[Resolve[ForAll[Evaluate[vars],Implies[H0 && precond, p>=0]],Reals]]) && (TrueQ[LZZ`InvSFast[p>=0, f, vars, H0]]),
Print["DC on ", p>=0];
Throw[DWCLZR[precond,postcond,{f,vars,(H0 && p>=0)}, Delete[A0,i]]]
];

(* DC check 2 *)
If[(TrueQ[Resolve[ForAll[Evaluate[vars],Implies[H0 && precond, p<0]],Reals]]) && (TrueQ[LZZ`InvSFast[p<=0, f, vars, H0]]),
Print["DC on ", p<=0];
Throw[DWCLZR[precond,postcond,{f,vars, (H0 && p<=0)}, Delete[A0,i]]]
]; 

(* DDC check 
If[TrueQ[TrueQ[LZZ`InvSFast[p==0, f, vars, H0]] && TrueQ[LZZ`InvSFast[p==0, -f, vars, H0]]],
Print["DDC on ", p==0];
GT=DWCLZR[precond,postcond,{f,vars, (H0 && p<0 )},Delete[A0,i]];
EQ=DWCLZR[precond,postcond,{f,vars, (H0 && p==0)},Delete[A0,i]];
LT=DWCLZR[precond,postcond,{f,vars, (H0 && p>0 )},Delete[A0,i]];

(* Combine reachable sets of the sub-systems *)
Throw[(GT || EQ || LT)]

]; *)
,{i,1,Length[A0]}]; (* End of main loop *)

Print["No more cuts. Trying DiscreteAbstraction`LazyReach with |A|=",Length[A0]];

Throw[DiscreteAbstraction`LazyReach[precond,postcond,{f,vars,H0},A0, 
		TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
		Parallel->OptionValue[Parallel],
		WorkingPrecision-> OptionValue[WorkingPrecision] ]]
]]


End[]
EndPackage[]
