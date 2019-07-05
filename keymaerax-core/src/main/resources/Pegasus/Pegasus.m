(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] (* Load classifier package from current directory *)
Needs["InvariantExtractor`",FileNameJoin[{Directory[],"InvariantExtractor.m"}]] (* Load classifier package from current directory *)
(* Load specialized invariant generation strategies *)
Needs["Strategies`GenericNonLinear`",FileNameJoin[{Directory[],"Strategies","GenericNonLinear.m"}]]
Needs["Strategies`OneDimensional`",FileNameJoin[{Directory[],"Strategies","OneDimensional.m"}]]


BeginPackage["Pegasus`"];


(*RunMethod::usage="Run designated method on a problem"*)
InvGen::usage="Pegasus[problem_List] Run Pegasus on problem"
Options[InvGen]= {SanityTimeout -> 0};


Begin["`Private`"]


CheckSemiAlgInclusion[subset_,set_,vars_List]:=Module[{},
TrueQ[Reduce[ForAll[vars, Implies[subset,set]],Reals]]
]


FindConst[ff_,var_,symbols_]:=Module[{ls,repr},
ls = {ff//.And -> List}//Flatten;
repr = Select[Cases[ls,Equal[var,rhs_]->rhs],Not[MemberQ[symbols,#]]&]//DeleteDuplicates;
If[Length[repr]>1,Print["Detected multiple values for ",var,repr]];
If[Length[repr]==1,{var -> First[repr]},{}]
]


(* Add sym'=0 to the ODE if the dynamics of sym is undefined *)
AugmentWithParameters[problem_List]:=Module[{pre,post,f,vars,evoConst,symbols,parameters,newvars,newf,
paramrep,paramfixed,paramfree},
{ pre, { f, vars, evoConst }, post } = problem;
symbols=Complement[DeleteDuplicates@Cases[{pre, post, f, evoConst},_Symbol,Infinity], {True, False}];
parameters=Complement[symbols, vars];
(* If the parameters have fixed values in pre then substitute that *)
paramrep=Map[{#,FindConst[pre,#,symbols]}&,parameters];
paramfixed=Map[#[[2]]&,Select[paramrep,Length[#[[2]]]!=0 &]]//Flatten;
paramfree=Map[#[[1]]&,Select[paramrep,Length[#[[2]]]==0&]];
{ pre, { f, vars, evoConst }, post } = problem /. paramfixed;
newvars=Join[vars,paramfree];
newf=Join[f,Table[0,{i,Length[paramfree]}]];
{ pre, { newf, newvars, evoConst }, post }
]


InvGen[parametricProb_List, opts:OptionsPattern[]]:=Catch[Module[
{problem,pre1,post1,pre,f,vars,evoConst,post,preImpliesPost,postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,polyList,invlist,cuts,cutlist,strat,hint,
(*ProofHint,Unknown,FirstIntegral,Darboux,Barrier*)}, 

(* Bring symbolic parameters into the dynamics *)
problem = AugmentWithParameters[parametricProb];
{ pre1, { f, vars, evoConst }, post1 }=problem;
pre = Primitives`DNFNormalizeGtGeq[pre1];
post=Primitives`DNFNormalizeGtGeq[post1];

(* Sanity check with timeout *)
If[OptionValue[SanityTimeout] > 0,
  TimeConstrained[Block[{},
  preImpliesPost=CheckSemiAlgInclusion[pre, post, vars];
  If[ Not[TrueQ[preImpliesPost]], 
  Print["Precondition does not imply postcondition! Nothing to do."]; Throw[{{}, False}], 
  Print["Precondition implies postcondition. Proceeding."]];

  postInvariant=LZZ`InvSFast[post, f, vars, evoConst];
  If[ TrueQ[postInvariant], 
  Print["Postcondition is an invariant! Nothing to do."]; Throw[{{post,{{post,Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}}},True}], 
  Print["Postcondition is (probably) not an invariant. Proceeding."]];

  preInvariant=LZZ`InvSFast[pre, f, vars, evoConst];
  If[ TrueQ[preInvariant], 
  Print["Precondition is an invariant! Nothing to do."]; Throw[{{pre,{{pre,Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}}}, True}], 
  Print["Precondition is (probably) not an invariant. Proceeding."]];
],OptionValue[SanityTimeout]]];

(* Determine strategies depending on problem classification by pattern matching on {dimension, classes} *)
class=Classifier`ClassifyProblem[problem];
Print[class];
strategies={};
strategies = class/.{
 {1,CLASSES_List}-> {
 {Strategies`OneDimensional`OneDimPotential, Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}, 
 {Strategies`OneDimensional`OneDimReach, Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}
 }, 
(* {dim_,{"Constant"}}-> ConstantStrat, *)
(* {2,{"Linear"}}-> PlanarLinearStrat, *)
(* {dim_,{"Linear"}}-> GeneralLinearStrat, *)
(* {dim_,{"Multi-affine"}}-> MultiLinearStrat, *)
{dim_, CLASSES_List}-> {
{Strategies`GenericNonLinear`SummandFacts, Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]},
{Strategies`GenericNonLinear`FirstIntegrals, Symbol["kyx`ProofHint"]==Symbol["kyx`FirstIntegral"]},
{Strategies`GenericNonLinear`DbxPoly, Symbol["kyx`ProofHint"]==Symbol["kyx`Darboux"]},
{Strategies`GenericNonLinear`BarrierCert, Symbol["kyx`ProofHint"]==Symbol["kyx`Barrier"]},
{Strategies`GenericNonLinear`SummandFacts, Symbol["kyx`ProofHint"]==Symbol["kyx`Unknown"]}
}
};

invlist=True;
cutlist={};
(* For each strategy *)
Do[
{strat,hint}=strathint;
Print["Trying: ",ToString[strat]," ",hint];
(* Compute polynomials for the algebraic decomposition of the state space *)
polyList=strat[{pre,{f,vars,evoConst},post}]//DeleteDuplicates;
Print["Generated polynomials: ",polyList];

(* Extract an invariant from the algebraic decomposition *)
inv=InvariantExtractor`DWC[pre, post, {f,vars,evoConst}, polyList, {}];

Print["Extracted invariants: ",inv];
(* Simplify invariant w.r.t. the domain constraint *)
{inv,cuts}=Map[Assuming[evoConst, FullSimplify[#, Reals]]&, inv];

Print["Extracted (simplified) invariants: ",inv," ",cuts];

(* Needs something like this?
 ecvoConst=And[evoConst,inv[[1]]]; *)
(* Implementation sanity check *)
If[ListQ[cuts],,Print["ERROR, NOT A LIST: ",cuts];Throw[{}]];

If[TrueQ[inv], Print["Skipped"],
	invlist=And[invlist,inv];
	cutlist=Join[cutlist,Map[{#,hint}&,Select[cuts,Not[TrueQ[#]]&]]];
	evoConst=And[evoConst,inv]];

post=Assuming[evoConst, FullSimplify[post, Reals]];
Print["Inv: ",inv];
Print["Invs: ",invlist];
Print["Cuts: ",cutlist];
Print["Evo: ",evoConst," Post: ",post];
invImpliesPost=CheckSemiAlgInclusion[evoConst, post, vars];
If[TrueQ[invImpliesPost], Print["Generated invariant implies postcondition. Returning."]; Throw[{{invlist,cutlist}, True}],
Print["Generated invariant does not imply postcondition. Bad luck; returning what I could find."]]
,{strathint, strategies}(* End Do loop *)];

(* Throw whatever invariant was last computed *)
Throw[{{invlist,cutlist}, False}]

]]


End[]
EndPackage[]
