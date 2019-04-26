(* ::Package:: *)

(* Description: Generic strategies for non-linear vector fields. *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] 
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]] 
Needs["BarrierCertificates`",FileNameJoin[{Directory[],"Primitives","BarrierCertificates.m"}]] 
Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"Primitives","DarbouxPolynomials.m"}]] 
Needs["QualitativeAbstraction`",FileNameJoin[{Directory[],"Primitives","QualitativeAbstractionPolynomials.m"}]] 


BeginPackage[ "Strategies`GenericNonLinear`"]


BarrierCert::usage="BarrierCertificates[problem_List]";
SummandFacts::usage="SummandFactors[problem_List]";
FirstIntegrals::usage="FirstIntegrals[problem_List,degree]";
DbxPoly::usage="FirstIntegrals[problem_List,degree]";


Begin["`Private`"];


FirstIntegrals[problem_List]:=Module[{pre,post,vf,vars,Q,fIs,maxVs,minVs,deg,rat},
{pre, { vf, vars, Q }, post} = problem;

deg = 10;
rat = 10000;

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[Element[num,Reals]],Primitives`UpperRat[num, rat], num];
lowerRat[num_]:=If[TrueQ[Element[num,Reals]],Primitives`LowerRat[num, rat], num];

(* Compute functionally independent first integrals up to given degree *)
fIs=FirstIntegrals`FuncIndep[FirstIntegrals`FindFirstIntegrals[deg, vars, vf],vars];
(* Return polynomials encoding the max/min values that the integrals can take on the initial set *)
(* p-c \[LessEqual] invariant *)
maxVs = Map[#-(upperRat[NMaxValue[{#,pre},vars]]/.{Infinity -> 0,-Infinity -> 0})&,fIs];
(* p+c \[GreaterEqual]0 invariant *)
minVs = Map[#-(lowerRat[NMinValue[{#,pre},vars]]/.{Infinity -> 0,-Infinity -> 0})&,fIs];
Union[maxVs,minVs]
]


SummandFacts[problem_List]:=DeleteDuplicates[Join[QualitativeAbstraction`SummandFactors[problem], Flatten[QualitativeAbstraction`SFactorList[problem]]]]


DbxPoly[problem_List] := QualitativeAbstraction`DarbouxPolynomials[problem, 5, 10]


(* Round to precisions 2,4,6,8 *)
RoundPolys[p_,vars_]:=Module[{cr},
cr = CoefficientRules[p,vars];
If[Length[cr] > 0,Map[MapAt[Function[x,Rationalize[Round[x,1/10^#]]],cr,{All,2}]~FromCoefficientRules~vars&,{2,4,6,8}]//DeleteDuplicates
,{}]]


BarrierCert[problem_List]:=Catch[Module[{pre,post,vf,vars,Q,polySOS},
  {pre, { vf, vars, Q }, post} = problem;
  polySOS=BarrierCertificates`SOSBarrierMATLAB[problem];
  Flatten[Map[RoundPolys[#,vars]&,polySOS]]
]]


End[]
EndPackage[]
