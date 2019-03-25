(* ::Package:: *)

(* Description: Generic strategies for non-linear vector fields. *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] 
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]] 
Needs["BarrierCertificates`",FileNameJoin[{Directory[],"Primitives","BarrierCertificates.m"}]] 
Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"Primitives","DarbouxPolynomials.m"}]] 
Needs["QualitativeAbstraction`",FileNameJoin[{Directory[],"Primitives","QualitativeAbstractionPolynomials.m"}]] 


BeginPackage[ "Strategies`GenericNonLinear`"]


BarrierCertificates::usage="BarrierCertificates[problem_List]"
SummandFactors::usage="SummandFactors[problem_List]"


Begin["`Private`"]


FirstIntegrals[problem_List,deg_Integer?NonNegative]:=Module[{pre,post,vf,vars,Q},
{pre, { vf, vars, Q }, post} = problem;
(* Compute functionally independent first integrals up to given degree *)
FirstIntegrals`FuncIndep[FirstIntegrals`FindFirstIntegrals[deg, vars, vf],vars]
]


SummandFactors[problem_List]:=QualitativeAbstraction`SummandFactors[problem]


DarbouxPolynomials[problem_List]:=QualitativeAbstraction`DarbouxPolynomials[problem]


BarrierCertificates[problem_List]:=Catch[Module[{pre,post,vf,vars,Q,decompositionList},
{pre, { vf, vars, Q }, post} = problem;
(* Initialize empty list of polynomials for the algebraic decomposition *)
decompositionList={};
(* Try to compute a barrier certificate *)
decompositionList=decompositionList~Join~{BarrierCertificates`SOSBarrier[problem]};
Throw[decompositionList]
]]


End[]
EndPackage[]
