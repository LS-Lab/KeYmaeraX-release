(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] (* Load classifier package from current directory *)
Needs["InvariantExtractor`",FileNameJoin[{Directory[],"InvariantExtractor.m"}]] (* Load classifier package from current directory *)
(* Load specialized invariant generation strategies *)
Needs["Strategies`GenericNonLinear`",FileNameJoin[{Directory[],"Strategies","GenericNonLinear.m"}]]
Needs["Strategies`OneDimensional`",FileNameJoin[{Directory[],"Strategies","OneDimensional.m"}]]
Needs["BarrierCertificates`",FileNameJoin[{Directory[],"Primitives","BarrierCertificates.m"}]] 
Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"Primitives","DarbouxPolynomials.m"}]] 
Needs["QualitativeAbstraction`",FileNameJoin[{Directory[],"Primitives","QualitativeAbstractionPolynomials.m"}]] 


BeginPackage["Pegasus`"];


RunMethod::usage="Run designated method on a problem"
InvGen::usafe="Run Pegasus"


Begin["`Private`"]


CheckSemiAlgInclusion[subset_,set_,vars_List]:=Module[{},
TrueQ[Reduce[ForAll[vars, Implies[subset,set]],Reals]]
]


(* Add sym'=0 to the ODE if the dynamics of sym is undefined *)
AugmentWithParameters[problem_List]:=Module[{pre,post,f,vars,evoConst,symbols,parameters,newvars,newf},
{ pre, { f, vars, evoConst }, post } = problem;
symbols=Complement[DeleteDuplicates@Cases[{pre, post, f, evoConst},_Symbol,Infinity], {True, False}];
parameters=Complement[symbols, vars];
newvars=Join[vars,parameters];
newf=Join[f,Table[0,{i,Length[parameters]}]];
{ pre, { newf, newvars, evoConst }, post }
]


InvGen[parametricProb_List]:=Catch[Module[
{problem,pre1,post1,pre,f,vars,evoConst,post,preImpliesPost,postInvariant,preInvariant,class,strategies,inv,andinv,relaxedInv,invImpliesPost,polyList}, 

(* Bring symbolic parameters into the dynamics *)
problem = AugmentWithParameters[parametricProb];
{ pre1, { f, vars, evoConst }, post1 }=problem;

pre = Primitives`DNFNormalizeGtGeq[pre1];
post=Primitives`DNFNormalizeGtGeq[post1];
(* Sanity checks *)
preImpliesPost=CheckSemiAlgInclusion[pre, post, vars];
If[ Not[TrueQ[preImpliesPost]], 
Print["Precondition does not imply postcondition! Nothing to do."]; Throw[{{False}, False}], 
Print["Precondition implies postcondition. Proceeding."]];

postInvariant=LZZ`InvS[post, f, vars, evoConst];
If[ TrueQ[postInvariant], 
Print["Postcondition is an invariant! Nothing to do."]; Throw[{{post,{post1}},True}], 
Print["Postcondition is not an invariant. Proceeding."]];

preInvariant=LZZ`InvS[pre, f, vars, evoConst];
If[ TrueQ[preInvariant], 
Print["Precondition is an invariant! Nothing to do."]; Throw[{{pre,{pre}}, True}], 
Print["Precondition is not an invariant. Proceeding."]];

(* Determine strategies depending on problem classification by pattern matching on {dimension, classes} *)
class=Classifier`ClassifyProblem[problem];
Print[class];
strategies={};
strategies = class/.{
 {1,CLASSES_List}-> {
 Strategies`OneDimensional`OneDimPotential, 
 Strategies`OneDimensional`OneDimReach
 }, 
(* {dim_,{"Constant"}}-> ConstantStrat, *)
(* {2,{"Linear"}}-> PlanarLinearStrat, *)
(* {dim_,{"Linear"}}-> GeneralLinearStrat, *)
(* {dim_,{"Multi-affine"}}-> MultiLinearStrat, *)
{dim_, CLASSES_List}-> {
Strategies`GenericNonLinear`SummandFactors,
Strategies`GenericNonLinear`FirstIntegrals,
QualitativeAbstraction`DarbouxPolynomials,
BarrierCertificates`SOSBarrier
}
};

(* For each strategy *)
Do[
Print["Trying: ",ToString[strat]];
(* Compute polynomials for the algebraic decomposition of the state space *)
polyList=strat[problem]//DeleteDuplicates;
Print["Generated polynomials: ",polyList];

(* Extract an invariant from the algebraic decomposition *)
inv=InvariantExtractor`DWC[pre, post, {f,vars,evoConst}, polyList, {}];

(* Simplify invariant w.r.t. the domain constraint *)
inv=Map[Assuming[evoConst, FullSimplify[#, Reals]]&, inv];
Print["Extracted (simplified) invariants: ",inv];

(* Needs something like this?
 evoConst=And[evoConst,inv[[1]]]; *)
invImpliesPost=CheckSemiAlgInclusion[Apply[And,inv[[2]]], post, vars];
If[TrueQ[invImpliesPost], Print["Generated invariant implies postcondition. Returning."]; Throw[{inv, True}],
Print["Generated invariant does not imply postcondition. Bad luck; returning what I could find."]]
,{ strat, strategies}(* End Do loop *)];

(* Throw whatever invariant was last computed *)
Throw[{inv, False}]

]]


End[]
EndPackage[]
