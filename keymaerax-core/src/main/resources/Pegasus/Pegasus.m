(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] (* Load classifier package from current directory *)
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] (* LZZ *)
Needs["DiffSaturation`",FileNameJoin[{Directory[],"Strategies","DiffSaturation.m"}]] (* Diff Sat *)


BeginPackage["Pegasus`"];


(*RunMethod::usage="Run designated method on a problem"*)
InvGen::usage="Pegasus[problem_List] Run Pegasus on problem"
Options[InvGen]= {SanityTimeout -> 0};


Begin["`Private`"]


InvGen[prob_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,f,vars,evoConst,post,preImpliesPost,postInvariant,preInvariant,class},

{pre,{f,vars,evoConst},post} = prob;

(* Sanity check with timeout *)
If[OptionValue[SanityTimeout] > 0,
  TimeConstrained[Block[{},
  preImpliesPost=Primitives`CheckSemiAlgInclusion[pre, post, vars];
  If[ Not[TrueQ[preImpliesPost]], 
  Print["Precondition does not imply postcondition! Nothing to do."]; Throw[{{}, False}], 
  Print["Precondition implies postcondition. Proceeding."]];

  postInvariant=LZZ`InvSFast[post, f, vars, evoConst];
  If[ TrueQ[postInvariant], 
  Print["Postcondition is an invariant! Nothing to do."]; Throw[{{post,{{post,Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}}},True}], 
  Print["Postcondition is (probably) not an invariant. Inv check gave: ", postInvariant,". Proceeding."]];

  preInvariant=LZZ`InvSFast[pre, f, vars, evoConst];
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
