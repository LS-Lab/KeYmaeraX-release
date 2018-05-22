(* ::Package:: *)

Needs["Methods`",NotebookDirectory[]<>"Methods.m"] (* Load invariant generation methods package from current directory *)
Needs["Classifier`",NotebookDirectory[]<>"Classifier.m"] (* Load classifier package from current directory *)
Needs["AbstractionPolynomials`",NotebookDirectory[]<>"AbstractionPolynomials.m"] (* Polynomial sources for qualitative abstraction *)
Needs["PlanarLinear`",NotebookDirectory[]<>"PlanarLinear.m"] (* Planar linear system analysis package *)


BeginPackage["Strategies`"];


RunMethod::usage="Run designated method on a problem"
RunStrategy::usage="Run designated stragegy on a problem"
Pegasus::usafe="Run Pegasus"


Begin["`Private`"]


(* ANCILLIARY MODULES *)


RunMethod[methodID_String, problem_List]:=Module[{
 precond=problem[[1]], system=problem[[2]], postcond=problem[[3]]
},
methodID/.{

(* Methods for one-dimensional systems *)
"OneDimPotential":> Methods`OneDimPotential[problem],
"OneDimReach":> Methods`OneDimReach[problem],

"PlanarLinear":> Methods`DWC[precond, postcond, system, PlanarLinear`PlanarLinearMethod[precond, postcond, system]],

(* Methods for non-linear systems based on qualitative analysis and discrete abstraction *)
"DWC-Factors-RHS":> Methods`DWC[precond, postcond, system, AbstractionPolynomials`PostRHSFactors[problem]],
"DWC-Factors-RHS-Lie":> Methods`DWC[precond, postcond, system, AbstractionPolynomials`PostRHSLieDFactors[problem]],
"DWC-Factors-RHS-Product":> Methods`DWC[precond, postcond, system, AbstractionPolynomials`PostRHSProductFactors[problem]],
"DWC-Factors-RHS-Lie-Product":> Methods`DWC[precond, postcond, system, AbstractionPolynomials`PostRHSLieDProductFactors[problem]],
"DWCL-Factors-RHS-Product":> Methods`DWCLZR[precond, postcond,system,  AbstractionPolynomials`PostRHSFactors[problem]],
"DWCL-Factors-RHS-Lie-Product":> Methods`DWCLZR[precond, postcond, system, AbstractionPolynomials`PostRHSLieDFactors[problem]]
}
]


RunStrategy[problem_List]:=Catch[Module[{},
(* Determine strategies depending on problem classification by pattern matching on {dimension, classes} *)
class=Classifier`ClassifyProblem[problem];
strat = class/.{
{1,CLASSES_List}-> OneDimStrat, 
{2,{"Linear"}}-> PlanarLinearStrat, 
{2,CLASSES_List}-> PlanarNonLinearStrat, 
{dim_,{"Linear"}}-> GeneralLinearStrat, 
{dim_, CLASSES_List}-> GenericStrat
};
(* Apply appropriate strategy to the problem and return the result *)
Throw[strat[problem]]
]]


CheckSemiAlgInclusion[subset_,set_,vars_List]:=Module[{},
TrueQ[Reduce[ForAll[vars, Implies[subset,set]],Reals]]
]


(* STRATEGIES *)


OneDimStrat[problem_List]:=Catch[Module[{},
(* Pattern match fields in the problem *)
{ pre, { f, vars, evoConst }, post } = problem;
(* Apply one-dimensional potential method *)
invPotential=RunMethod["OneDimPotential", problem];
(* If resulting invariant is sufficient, return it *)
If[CheckSemiAlgInclusion[invPotential,post,vars], Throw[invPotential],
(* Otherwise, construct the reachable set and return *)
reachSet=RunMethod["OneDimReach", problem];
Throw[reachSet]]
]]


PlanarLinearStrat[problem_List]:=Catch[Module[{inv,invs},
(* Pattern match fields in the problem *)
{ pre, { f, vars, evoConst }, post } = problem;
(* Apply methods for planar linear systems  *)
initConnectedComponents=CylindricalDecomposition[pre,vars,"Components"];
problems = Map[ {#, {f,vars,evoConst}, post}&, initConnectedComponents];
invs=Map[RunMethod["PlanarLinear", #]&, problems];
inv=If[Length[invs]>1, Throw[Apply[Or, invs]], Throw[invs[[1]]]]
]]


GeneralLinearStrat[problem_List]:=Catch[Module[{inv,invs},
(* Pattern match fields in the problem *)
{ pre, { f, vars, evoConst }, post } = problem;
(* Apply methods for planar linear systems  *)
initConnectedComponents=CylindricalDecomposition[pre,vars,"Components"];
problems = Map[ {#, {f,vars,evoConst}, post}&, initConnectedComponents];
invs=Map[RunMethod["PlanarLinear", #]&, problems];
inv=If[Length[invs]>1, Throw[Apply[Or, invs]], Throw[invs[[1]]]]
]]


QualitativeBasic[problem_List]:=Catch[Module[{},
(* Pattern match fields in the problem *)
{ pre, { f, vars, evoConst }, post } = problem;
aggregate=evoConst;
inv=True;
Do[
inv=RunMethod[method,problem];
If[ TrueQ[Reduce[Implies[inv, post], vars, Reals]], Throw[inv]];
aggregate=Simplify[inv && aggregate];
If[TrueQ[Reduce[Implies[aggregate, post], vars, Reals]], Throw[aggregate]],
{method,{"DWC-Factors-RHS", "DWC-Factors-RHS-Lie", "DWC-Factors-RHS-Product", "DWC-Factors-RHS-Lie-Product"}}
];
Throw[QualitativeExtended[{pre, {f, vars, aggregate} ,post}]]
]]


QualitativeExtended[problem_List]:=Catch[Module[{},
(* Pattern match fields in the problem *)
{ pre, { f, vars, evoConst }, post } = problem;
aggregate=evoConst;
inv=True;
Do[
inv=RunMethod[method,problem];
If[ TrueQ[Reduce[Implies[inv, post], vars, Reals]], Throw[inv]];
aggregate=Simplify[inv && aggregate];
If[TrueQ[Reduce[Implies[aggregate, post], vars, Reals]], Throw[aggregate]],
{method,{"DWCL-Factors-RHS-Product"}}
];
Throw[aggregate]
]]


Pegasus[problem_List]:=Catch[Module[{},
(* Determine strategies depending on problem classification by pattern matching on {dimension, classes} *)
class=Classifier`ClassifyProblem[problem];
strat = class/.{
{1,CLASSES_List}-> OneDimStrat, 
{2,{"Linear"}}-> PlanarLinearStrat, 
{dim_, CLASSES_List}-> QualitativeBasic
};
(* Apply strategy to the problem and return the result *)
Throw[strat[problem]]
]]


End[]
EndPackage[]
