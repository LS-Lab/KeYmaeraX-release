(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Classifier`",FileNameJoin[{Directory[],"NewClassifier.m"}]] (* Load classifier package from current directory *)
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] (* LZZ *)
Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] (* LZZ *)
Needs["DiffSaturation`",FileNameJoin[{Directory[],"Strategies","DiffSaturation.m"}]] (* Diff Sat *)
Needs["DiffDivConquer`",FileNameJoin[{Directory[],"Strategies","DiffDivConquer.m"}]] (* Diff Sat *)
Needs["Helper`",FileNameJoin[{Directory[],"Strategies","Helper.m"}]] (* Diff Sat *)
Needs["Format`",FileNameJoin[{Directory[],"Strategies","Format.m"}]] (* Formatting *)


BeginPackage["Pegasus`"];


AugmentWithParameters::usage="AugmentWithParameters[problem_List] Splits out parameter information in the problem";
InvGen::usage="InvGen[problem_List] Run Pegasus on problem";
Options[InvGen]= {SanityCheckTimeout -> 0, UseDDC -> False};


Begin["`Private`"]


AugmentWithParameters[problem_List]:=Module[{pre,post,f,vars,evoConst,symbols,parameters,newvars,newf,
paramrep,paramfixed,paramfree,prefree,evofree,asmsfree},
{ pre, { f, vars, evoConst }, post } = problem;
symbols=Complement[DeleteDuplicates@Cases[{pre, post, f, evoConst},_Symbol,Infinity], {True, False}];
parameters=Complement[symbols, vars];

(* If the parameters have fixed values in pre then substitute that *)
paramrep=Map[{#,Primitives`FindConst[pre,#,symbols]}&,parameters];
paramfixed=Map[#[[2]]&,Select[paramrep,Length[#[[2]]]!=0 &]]//Flatten;
paramfree=Map[#[[1]]&,Select[paramrep,Length[#[[2]]]==0&]];

{ pre, { f, vars, evoConst }, post } = problem /. paramfixed;

{pre,prefree} = Helper`SplitAssums[pre,paramfree];
{evoConst,evofree} = Helper`SplitAssums[evoConst,paramfree];
asmsfree = And[prefree, evofree];

(* Split out *)
Print["Parameters: ", paramfree, " Const assumptions: ", asmsfree];
{pre, {f,vars,evoConst}, post, {paramfree,asmsfree}}
]


InvGen[prob_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,f,vars,evoConst,post,
preImpliesPost,postInvariant,preInvariant,preDomFalse,domImpPost,class,constvars,constQ,eprob,
ERRSTR},

ERRSTR="Incorrect Pegasus problem format.\n
Requires either {pre,{vf,vars,Q},post} or {pre,{vf,vars,Q},post,{constvars,constQ}}.\n
pre,post are the pre/postconditions respectively,\n
vf,vars are lists of equal length representing an ODE vars'=vf\n
Q is the domain constraint\n
constvars lists parameters for the problem and constQ are
	Throw[DiffSaturation`FormatResult[False,{},False]],  assumptions about parameters\n
constvars and constQ are automatically generated if not present";

If[Length[prob]!=3 && Length[prob]!=4,
	Throw[Format`FormatErr[ERRSTR]]
	];

If[Length[prob[[2]]]!=3,
	Throw[Format`FormatErr[ERRSTR]]
	];

If[Length[prob[[2]][[1]]]!=Length[prob[[2]][[2]]]||Length[prob[[2]]]==0,
	Throw[Format`FormatErr[ERRSTR]]
	];

If[Length[prob]==3,
	Print["Extending problem. "];
	eprob=AugmentWithParameters[prob]
	];

Print["Input problem: ", eprob];
{pre,{f,vars,evoConst},post,{constvars,constQ}}=eprob;

(* Sanity check with timeout *)
If[OptionValue[InvGen,SanityCheckTimeout] > 0,
  TimeConstrained[Block[{},
  preImpliesPost=Primitives`CheckSemiAlgInclusion[And[pre,constQ,evoConst], post, Join[constvars,vars]];
  If[ Not[TrueQ[preImpliesPost]], 
    Print["Precondition does not even imply postcondition! Nothing to do."];
	Throw[Format`FormatTriv[5]], 
    Print["Precondition implies postcondition. Proceeding."]
    ];
  
  (* Dom implies Post *)
  domImpPost=Primitives`CheckSemiAlgInclusion[evoConst&&constQ,post, Join[constvars,vars]];
  If[ TrueQ[domImpPost], 
    Print["Domain constraint implies postcondition! Nothing to do."];
	Throw[Format`FormatTriv[4]]];
    
  (* TODO: LZZ should directly work with constant assumptions instead of this expansion trickery? *)
  postInvariant=LZZ`InvSFast[post, Join[f,Table[0,{i,Length[constvars]}]] , Join[vars,constvars], And[evoConst,constQ]];
  If[ TrueQ[postInvariant], 
    Print["Postcondition is an invariant! Nothing to do."];
	Throw[Format`FormatTriv[2]],
    Print["Postcondition is (probably) not an invariant. Inv check gave: ", postInvariant,". Proceeding."]
    ];

  (* Pre && Dom implies False *)
  preDomFalse=Primitives`CheckSemiAlgInclusion[pre&&evoConst&&constQ,False, Join[constvars,vars]];
  If[ TrueQ[preDomFalse], 
    Print["Precondition & domain constraint are contradictory! Nothing to do."];
	Throw[Format`FormatTriv[3]]];
  
  (* TODO: LZZ should directly work with constant assumptions instead of this expansion trickery? *)
  preInvariant=LZZ`InvSFast[pre, Join[f,Table[0,{i,Length[constvars]}]] , Join[vars,constvars], And[evoConst,constQ]];
  If[ TrueQ[preInvariant], 
    Print["Precondition is an invariant! Nothing to do."];
	Throw[Format`FormatTriv[1]],
    Print["Precondition is (probably) not an invariant. Inv check gave: ",preInvariant,". Proceeding."]];
], OptionValue[InvGen,SanityCheckTimeout]]];

(* Determine strategies depending on problem classification by pattern matching on {dimension, classes} *)
class=Classifier`ClassifyProblem[{pre,{f,vars,evoConst},post}];
Print["Classification: ", class];

If[TrueQ[OptionValue[InvGen,UseDDC]],
	DiffDivConquer`DiffSplit[eprob, class],
	DiffSaturation`DiffSat[eprob, class]]
]]


End[]
EndPackage[]
