(* ::Package:: *)

Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] 
(*Needs["DiscreteAbstraction`",FileNameJoin[{Directory[],"Primitives","DiscreteAbstraction.m"}]] *)


BeginPackage["InvariantExtractor`"];

DWC::usage="DWC[precond_, postcond_, system_List, H0_List, A0_List]
    Iteratively refine evolution constraint using differential cuts before computing the abstraction."
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

DWC[problem_List, A0_List, cuts_List, opts:OptionsPattern[]]:=
DWC[precond, postcond, system, A0, cuts]=Catch[
Module[{pre,post,GT,EQ,LT,p,f,vars,H0},

{pre,{f,vars,H0},post} = problem;
SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWC, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> DoNotSimplify};
USEDW=Not[TrueQ[OptionValue[Smallest]/.{True->True, _->False}]];

(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[OptionValue[SufficiencyTimeout] > 0,
	Print["Sufficiency check ", H0, " overlaps ", pre];
	If[TrueQ[TimeConstrained[Reduce[Not[Exists[vars,H0 && pre],vars,Reals]]], OptionValue[SufficiencyTimeout], False],
		Print["No overlap ", H0, " with ", pre]; Throw[{False, cuts}] ]
	,
	Print["Sufficiency check skipped"]
];

(* DW check *)
If[USEDW && OptionValue[DWTimeout] > 0,
	If[TrueQ[TimeConstrained[Reduce[ForAll[vars,Implies[H0, post]],vars,Reals]], DWTimeout, False],
		Print["DW"]; Throw[{H0, cuts}] ]
	,
	Print["DW check skipped"]
];

Print["Simplifying"];

(* Main loop *)
Do[p=SIMPLIFY[A0[[i]],H0]; 

Print["Trying: ",p];
(* DC check 0 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && pre, p==0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p==0, f, vars, H0]]),
Print["DC on ", p==0];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p==0), Reals]},post}, Delete[A0,i], Join[cuts,{p==0}]]]
];

(* DC strict check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && pre, p>0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p>0, f, vars, H0]]),
Print["DC on ", p>0];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p>0), Reals]},post}, Delete[A0,i], Join[cuts,{p>0}]]]
];

(* DC strict check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && pre, p<0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p<0, f, vars, H0]]),
Print["DC on ", p<0];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p<0), Reals]},post}, Delete[A0,i], Join[cuts,{p<0}]]]
];

(* DC nonstrict check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && pre, p>=0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p>=0, f, vars, H0]]),
Print["DC on ", p>=0];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p>=0), Reals]},post}, Delete[A0,i], Join[cuts,{p>=0}]]]
];

(* DC nonstrict check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && pre, p<=0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p<=0, f, vars, H0]]),
Print["DC on ", p<=0];
Throw[DWC[{pre,{f,vars, SIMPLIFY[(H0 && p<=0), Reals]},post}, Delete[A0,i], Join[cuts,{p<=0}]]]
];

 (*DDC check  *)
 (*
If[TrueQ[TrueQ[LZZ`InvS[p==0, f, vars, H0]] && TrueQ[LZZ`InvS[p==0, -f, vars, H0]]],
Print["DDC on ", p==0];
GT=DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p<0 ), Reals]},Delete[A0,i]];
EQ=DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p==0), Reals]},Delete[A0,i]];
LT=DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p>0 ), Reals]},Delete[A0,i]];

(* Combine reachable sets of the sub-systems *)
Throw[SIMPLIFY[(GT || EQ || LT),Reals]]

]; *) 

,{i,1,Length[A0]}]; (* End of main loop *)

Print["No more cuts ... "];

Throw[{H0, cuts}]
]]


Options[DWCLZR]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->FullSimplify, WorkingPrecision -> \[Infinity]};

DWCLZR[precond_, postcond_, system_List, A0_List, opts:OptionsPattern[]]:=Catch[
Module[{GT,EQ,LT,p,f=system[[1]],vars=system[[2]],H0=system[[3]]},

SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWCLZR, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];


(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[TrueQ[Reduce[ForAll[vars,Not[H0 && precond]],vars,Reals]], Throw[False] ]; 

(* DW check *)
If[TrueQ[Reduce[ForAll[vars,Implies[H0, postcond]],vars,Reals]], Throw[H0] ]; 

(* Main loop *)
Do[p=A0[[i]];

(* DC check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>=0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p>=0, f, vars, H0]]),
Print["DC on ", p>=0];
Throw[DWCLZR[precond,postcond,{f,vars,(H0 && p>=0)}, Delete[A0,i]]]
];

(* DC check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<0]],vars,Reals]]) && (TrueQ[LZZ`InvSFast[p<=0, f, vars, H0]]),
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
