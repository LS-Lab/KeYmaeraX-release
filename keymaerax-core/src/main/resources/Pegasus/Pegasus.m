(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] (* Load classifier package from current directory *)
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] (* LZZ *)
Needs["DiffSaturation`",FileNameJoin[{Directory[],"Strategies","DiffSaturation.m"}]] (* Diff Sat *)


BeginPackage["Pegasus`"];


AugmentWithParameters::usage="AugmentWithParameters[problem_List] Splits out parameter information in the problem";
InvGen::usage="InvGen[problem_List] Run Pegasus on problem";
Options[InvGen]= {SanityTimeout -> 0};


Begin["`Private`"]


FindConst[ff_,var_,symbols_]:=Module[{ls,repr},
ls = {ff//.And -> List}//Flatten;
repr = Select[Cases[ls,Equal[var,rhs_]->rhs],Not[MemberQ[symbols,#]]&]//DeleteDuplicates;
If[Length[repr]>1,Print["Detected multiple values for ",var,repr]];
If[Length[repr]==1,{var -> First[repr]},{}]
]


SplitAssums[ff_,vars_]:=Module[{ls},
ls = {ff//.And -> List}//Flatten;
{Select[ls,Complement[DeleteDuplicates@Cases[#, _Symbol, Infinity],vars]!={}&]//.List->And,
Select[ls,Complement[DeleteDuplicates@Cases[#, _Symbol, Infinity],vars]=={}&]//.List->And}
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

{pre,prefree} = SplitAssums[pre,paramfree];
{evoConst,evofree} = SplitAssums[evoConst,paramfree];
asmsfree = And[prefree, evofree];

(* Split out *)
Print["Parameters: ", paramfree, " Const assumptions: ", asmsfree];
{pre, {f,vars,evoConst}, post, {paramfree,asmsfree}}
]


InvGen[prob_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,f,vars,evoConst,post,preImpliesPost,postInvariant,preInvariant,class,constvars,constasms},

{pre,{f,vars,evoConst},post,{constvars,constasms}} = AugmentWithParameters[prob];

(* Sanity check with timeout *)
If[OptionValue[SanityTimeout] > 0,
  TimeConstrained[Block[{},
  preImpliesPost=Primitives`CheckSemiAlgInclusion[And[pre,constasms,evoConst], post, Join[constvars,vars]];
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

DiffSaturation`DiffSat[prob]
]]


End[]
EndPackage[]
