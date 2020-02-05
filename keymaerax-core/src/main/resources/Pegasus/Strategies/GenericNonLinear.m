(* ::Package:: *)

(*
	Description: Generic strategies for non-linear vector fields.
	This file summarizes all the basic strategies that generate invariants from a problem.
	This will be used by DiffSat
*)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]] 
Needs["QualAbsPolynomials`",FileNameJoin[{Directory[],"Primitives","QualAbsPolynomials.m"}]] 
Needs["DarbouxDDC`",FileNameJoin[{Directory[],"Strategies","DarbouxDDC.m"}]]
Needs["InvariantExtractor`",FileNameJoin[{Directory[],"Strategies","InvariantExtractor.m"}]]
(*Needs["BarrierCertificates`",FileNameJoin[{Directory[],"Primitives","BarrierCertificates.m"}]] 
 *)


BeginPackage[ "GenericNonLinear`"];


(*BarrierCert::usage="BarrierCertificates[problem_List]";
SummandFacts::usage="SummandFactors[problem_List]";
*)

(* Returns invariants generated using first integrals *)
FirstIntegrals::usage="FirstIntegrals[problem_List,degree]";
(* Returns invariants generated using Darboux polynomials *)
DbxPoly::usage="DbxPoly[problem_List,degree]";
(* Returns invariants generated from heuristics *)
HeuInvariants::usage="Heuristics[problem_List,degree]";


Begin["`Private`"];


HeuInvariants[problem_List]:=Module[{pre,post,vf,vars,Q,polys},
{pre, { vf, vars, Q }, post} = problem;
polys = DeleteDuplicates[Join[
	QualAbsPolynomials`ProblemFactorsWithLie[problem],
	QualAbsPolynomials`PhysicalQuantities[problem],
	QualAbsPolynomials`SummandFactors[problem],
	QualAbsPolynomials`SFactorList[problem]]];
	
(*res=Map[InvariantExtractor`DWC[problem,{#},{}]&,polys];*)
InvariantExtractor`DWC[problem,polys,{}][[2]]
]


FirstIntegrals[problem_List]:=Module[{pre,post,vf,vars,Q,fIs,maxVs,minVs,deg,rat,uppers,lowers,bound},
{pre, { vf, vars, Q }, post} = problem;
(* Heuristic *)
deg = Max[10-Length[vars],1];
rat = 5;
bound=10^8;

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[Element[num,Reals] && num < bound],Primitives`UpperRat[num, rat], Infinity];
lowerRat[num_]:=If[TrueQ[Element[num,Reals] && num > -bound],Primitives`LowerRat[num, rat], -Infinity];

(* Compute functionally independent first integrals up to given degree *)
fIs=Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vf,vars,Q},deg],vars];

(* upper and lower bounds on the FIs
todo: NMaxValue instead? Needs extra LZZ check: it doesn't give the real max/mins sometimes!
*)
uppers = Map[upperRat[MaxValue[{#,pre},vars]]&,fIs];
lowers = Map[lowerRat[MinValue[{#,pre},vars]]&,fIs];
(*
Print["First integrals:",fIs];
Print[uppers,lowers]; *)

maxVs=Flatten[MapThread[If[#2==Infinity,{},{#1<=#2}] &, {fIs,uppers}]];
(* Return polynomials encoding the max/min values that the integrals can take on the initial set *)
(* p+c \[GreaterEqual]0 invariant *)
minVs=Flatten[MapThread[If[#2==-Infinity,{},{#1>=#2}] &, {fIs,lowers}]];
Union[maxVs,minVs]
]


DbxPoly[problem_List] := Module[{pre,post,vf,vars,Q,polys},
{pre, { vf, vars, Q }, post} = problem;
polys = DarbouxDDC`DarbouxPolynomialsM[{vf,vars,Q}, 10, Max[10-Length[vars],1]];
InvariantExtractor`DWC[problem,polys,{}][[2]]
]


(*(* Round to precisions 2,4,6,8 *)
RoundPolys[p_,vars_]:=Module[{cr},
cr = CoefficientRules[p,vars];
If[Length[cr] > 0,Map[MapAt[Function[x,Rationalize[Round[x,1/10^#]]],cr,{All,2}]~FromCoefficientRules~vars&,{2,4,6,8}]//DeleteDuplicates
,{}]]*)


(*BarrierCert[problem_List]:=Catch[Module[{pre,post,vf,vars,Q,polySOS},
  {pre, { vf, vars, Q }, post} = problem;
  If[pre===True,Return[{}]];
  If[post===False,Return[{}]];
  polySOS=BarrierCertificates`SOSBarrierMATLAB[problem];
  Flatten[Map[RoundPolys[#,vars]&,polySOS]]
]]*)


End[]
EndPackage[];
