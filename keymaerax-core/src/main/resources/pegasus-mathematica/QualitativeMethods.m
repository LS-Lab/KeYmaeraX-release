(* ::Package:: *)

Needs["LZZ`",FileNameJoin[{Directory[],"LZZ.m"}]] 
Needs["DiscreteAbstraction`",FileNameJoin[{Directory[],"DiscreteAbstraction.m"}]] 


BeginPackage["QualitativeMethods`"];


DCLoop::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] 
    Iteratively refine evolution constraint using differential cuts before computing the abstraction."

DWC::usage="DWC[precond_, postcond_, system_List, H0_List, A0_List] 
    Iteratively refine evolution constraint using differential cuts before computing the abstraction."

DWCLZR::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] 
    Iteratively refine evolution constraint using differential cuts before computing the abstraction."

DWCLZRC::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] 
    Iteratively refine evolution constraint using differential cuts before computing the abstraction."


Begin["`Private`"]


(* NON-LINEAR AND DISCRETE QUALITATIVE ABSTRACTION-BASED METHODS *)


DoNotSimplify[formula_, assumptions_]:=Module[{},
formula
]


Options[DWC]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->DoNotSimplify, Smallest->False, WorkingPrecision -> \[Infinity]};

DWC[precond_, postcond_, system_List, A0_List, cuts_List, opts:OptionsPattern[]]:=DWC[precond, postcond, system, A0, cuts]=Catch[
Module[{GT,EQ,LT,p,f=system[[1]],vars=system[[2]],H0=system[[3]]},

SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWC, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> DoNotSimplify};
USEDW=Not[TrueQ[OptionValue[Smallest]/.{True->True, _->False}]];

(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[TrueQ[Reduce[ForAll[vars,Not[H0 && precond]],vars,Reals]], Throw[{False, cuts}] ]; 

(* DW check *)
If[USEDW && TrueQ[Reduce[ForAll[vars,Implies[H0, postcond]],vars,Reals]], Print["DW"]; Throw[{H0, cuts}] ]; 

(* Main loop *)
Do[p=SIMPLIFY[A0[[i]],H0]; 

(* DC check 0 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p==0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p==0, f, vars, H0]]),
Print["DC on ", p==0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p==0), Reals]}, Delete[A0,i], Join[cuts,{p==0}]]]
];

(* DC strict check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p>0, f, vars, H0]]),
Print["DC on ", p>0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p>0), Reals]}, Delete[A0,i], Join[cuts,{p>0}]]]
];

(* DC strict check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p<0, f, vars, H0]]),
Print["DC on ", p<0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p<0), Reals]}, Delete[A0,i], Join[cuts,{p<0}]]]
];

(* DC nonstrict check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>=0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p>=0, f, vars, H0]]),
Print["DC on ", p>=0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p>=0), Reals]}, Delete[A0,i], Join[cuts,{p>=0}]]]
];

(* DC nonstrict check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<=0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p<=0, f, vars, H0]]),
Print["DC on ", p<=0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p<=0), Reals]}, Delete[A0,i], Join[cuts,{p<=0}]]]
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
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>=0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p>=0, f, vars, H0]]),
Print["DC on ", p>=0];
Throw[DWCLZR[precond,postcond,{f,vars,(H0 && p>=0)}, Delete[A0,i]]]
];

(* DC check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p<=0, f, vars, H0]]),
Print["DC on ", p<=0];
Throw[DWCLZR[precond,postcond,{f,vars, (H0 && p<=0)}, Delete[A0,i]]]
]; 

(* DDC check 
If[TrueQ[TrueQ[LZZ`InvS[p==0, f, vars, H0]] && TrueQ[LZZ`InvS[p==0, -f, vars, H0]]],
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


Options[DCLoop]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->FullSimplify, WorkingPrecision -> \[Infinity]};

DCLoop[{precond_, {f_List,vars_List,H0_}, postcond_}, A0_List, opts:OptionsPattern[]]:=Catch[
Module[{GT,EQ,LT,p},

SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DCLoop, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];

(* Sufficiency check 1: No evolution from the initial set, so no reachable set *)
If[TrueQ[Reduce[ForAll[vars,Not[H0 && precond]],vars,Reals]],Throw[False]]; 

(* Sufficiency check 2: Apply DW *)
If[TrueQ[Reduce[ForAll[vars,Implies[H0, postcond]],vars,Reals]],Throw[H0]]; 

Do[p=Simplify[A0[[i]], H0];

If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p>0, f, vars, H0]]),
Print["DC on ", p>0];
Throw[DCLoop[{precond,{f,vars,Simplify[(H0 && p>0), Reals]},postcond},Delete[A0,i]]];
];

If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<0]],vars,Reals]]) && (TrueQ[LZZ`InvS[p<0, f, vars, H0]]),
Print["DC on ", p<0];
Throw[DCLoop[{precond,{f,vars,Simplify[(H0 && p<0), Reals]},postcond}, Delete[A0,i]]];
];

(* DDC optional
If[TrueQ[LZZ`InvS[p==0, f, vars, H0]] && TrueQ[LZZ`InvS[p==0, -f, vars, H0]],
Print["DDC on ", p==0];
GT=DCLoop[precond,postcond,{f,vars, Simplify[(H0 && p<0), Reals]},Delete[A0,i]];
EQ=DCLoop[precond,postcond,{f,vars, Simplify[(H0 && p==0), Reals]},Delete[A0,i]];
LT=DCLoop[precond,postcond,{f,vars, Simplify[(H0 && p>0), Reals]},Delete[A0,i]];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> StandardForm};
(* Combine reachable sets of the sub-systems *)
Throw[SIMPLIFY[(GT || EQ || LT),Reals]]
]; *)
,{i,1,Length[A0]}];

Throw[DiscreteAbstraction`LazyReach[precond,postcond,{f,vars,H0},A0, 
		TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
		Parallel->OptionValue[Parallel],
		WorkingPrecision-> OptionValue[WorkingPrecision] ]]
]]


End[]
EndPackage[]
