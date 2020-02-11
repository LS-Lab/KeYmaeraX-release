(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] (* Load classifier package from current directory *)
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] (* LZZ *)
Needs["DiffSaturation`",FileNameJoin[{Directory[],"Strategies","DiffSaturation.m"}]] (* Diff Sat *)
Needs["Helper`",FileNameJoin[{Directory[],"Strategies","Helper.m"}]] (* Diff Sat *)


BeginPackage["Pegasus`"];


AugmentWithParameters::usage="AugmentWithParameters[problem_List] Splits out parameter information in the problem";
InvGen::usage="InvGen[problem_List] Run Pegasus on problem";
Options[InvGen]= {SanityTimeout -> 0};


Begin["`Private`"]


FindConst[ff_,var_,symbols_]:=Module[{ls,repr},
ls = {ff//.And -> List}//Flatten;
(* TODO: This line doesn't seem correct... *)
repr = Select[Cases[ls,Equal[var,rhs_]->rhs],Not[MemberQ[symbols,#]]&]//DeleteDuplicates;
If[Length[repr]>1,Print["Detected multiple values for ",var,repr]];
If[Length[repr]==1,{var -> First[repr]},{}]
]


AugmentWithParameters[problem_List]:=Module[{pre,post,f,vars,evoConst,symbols,parameters,newvars,newf,
paramrep,paramfixed,paramfree,prefree,evofree,asmsfree},
{ pre, { f, vars, evoConst }, post } = problem;
symbols=Complement[DeleteDuplicates@Cases[{pre, post, f, evoConst},_Symbol,Infinity], {True, False}];
parameters=Complement[symbols, vars];

(* If the parameters have fixed values in pre then substitute that *)
paramrep=Map[{#,FindConst[pre,#,symbols]}&,parameters];
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
preImpliesPost,postInvariant,preInvariant,class,constvars,constQ,eprob,
ERRSTR},

ERRSTR="Incorrect Pegasus problem format.\n
Requires either {pre,{vf,vars,Q},post} or {pre,{vf,vars,Q},post,{constvars,constQ}}.\n
pre,post are the pre/postconditions respectively,\n
vf,vars are lists of equal length representing an ODE vars'=vf\n
Q is the domain constraint\n
constvars lists parameters for the problem and constQ are assumptions about parameters\n
constvars and constQ are automatically generated if not present";

If[Length[prob]!=3 && Length[prob]!=4, Print[ERRSTR]; Throw[{}]];

If[Length[prob[[2]]]!=3, Print[ERRSTR]; Throw[{}]];

If[Length[prob[[2]][[1]]]!=Length[prob[[2]][[2]]]||Length[prob[[2]]]==0, Print[ERRSTR]; Throw[{}]];

If[Length[prob]==3, Print["Extending"];eprob=AugmentWithParameters[prob]];

Print[eprob];
{pre,{f,vars,evoConst},post,{constvars,constQ}}=eprob;

(* Sanity check with timeout *)
If[OptionValue[SanityTimeout] > 0,
  TimeConstrained[Block[{},
  preImpliesPost=Primitives`CheckSemiAlgInclusion[And[pre,constQ,evoConst], post, Join[constvars,vars]];
  If[ Not[TrueQ[preImpliesPost]], 
  Print["Precondition does not imply postcondition! Nothing to do."]; Throw[{{}, False}], 
  Print["Precondition implies postcondition. Proceeding."]];

  (* TODO: LZZ should directly work with constant assumptions instead of this expansion trickery? *)
  postInvariant=LZZ`InvSFast[post, Join[f,Table[0,{i,Length[constvars]}]] , Join[vars,constvars], And[evoConst,constasms]];
  If[ TrueQ[postInvariant], 
  Print["Postcondition is an invariant! Nothing to do."]; Throw[{{post,{{post,Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}}},True}], 
  Print["Postcondition is (probably) not an invariant. Inv check gave: ", postInvariant,". Proceeding."]];

  (* TODO: LZZ should directly work with constant assumptions instead of this expansion trickery? *)
  preInvariant=LZZ`InvSFast[pre, Join[f,Table[0,{i,Length[constvars]}]] , Join[vars,constvars], And[evoConst,constasms]];
  If[ TrueQ[preInvariant], 
  Print["Precondition is an invariant! Nothing to do."]; Throw[{{pre,{{pre,Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}}}, True}], 
  Print["Precondition is (probably) not an invariant. Inv check gave: ",preInvariant,". Proceeding."]];
],OptionValue[SanityTimeout]]];

(* Determine strategies depending on problem classification by pattern matching on {dimension, classes} *)
(* TODO: put in the classifier?? *)
class=Classifier`ClassifyProblem[prob];
Print["Classification: ", class];

DiffSaturation`DiffSat[eprob]
]]


End[]
EndPackage[]
