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
Needs["BarrierCertificates`",FileNameJoin[{Directory[],"Primitives","BarrierCertificates.m"}]] 


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
(* Returns invariants generated from barrier certificate *)
BarrierCert::usage="BarrierCert[problem_List]";

(* Options and defaults for each of these methods
	Deg \[Rule] -1 means run with default heuristic for choosing the degree
	The default values are configured assuming a 2 minute timeout
*)
Options[HeuInvariants]= {Timeout -> 20};
Options[FirstIntegrals]= {Deg -> -1, Timeout -> 20};
Options[DbxPoly]= {Deg -> -1, Timeout -> 40};
Options[BarrierCert]= {Deg -> -1, Timeout -> Infinity};


Begin["`Private`"];


HeuInvariants[problem_List]:=Module[{pre,post,vf,vars,Q,polys},
{pre, { vf, vars, Q }, post} = problem;

If[OptionValue[HeuInvariants, Timeout] > 0,
TimeConstrained[Block[{},
polys = DeleteDuplicates[Join[
	QualAbsPolynomials`SummandFactors[problem],
	QualAbsPolynomials`SFactorList[problem]
	(*,
	QualAbsPolynomials`ProblemFactorsWithLie[problem],
	QualAbsPolynomials`PhysicalQuantities[problem],
	*)
	]];
(*res=Map[InvariantExtractor`DWC[problem,{#},{}]&,polys];*)
InvariantExtractor`DWC[problem,polys,{}][[2]]
], OptionValue[HeuInvariants,Timeout],
{}],
Print["HeuInvariants skipped."]; {}]

]


FirstIntegrals[problem_List]:=Module[{pre,post,vf,vars,Q,fIs,maxVs,minVs,deg,rat,uppers,lowers,bound},
{pre, { vf, vars, Q }, post} = problem;

(* Heuristic *)
deg = If[OptionValue[FirstIntegrals,Deg] < 0,
		Max[10-Length[vars],1],
		OptionValue[FirstIntegrals, Deg]];
rat = 5;
bound=10^8;

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[Element[num,Reals] && num < bound],Primitives`UpperRat[num, rat], Infinity];
lowerRat[num_]:=If[TrueQ[Element[num,Reals] && num > -bound],Primitives`LowerRat[num, rat], -Infinity];

If[OptionValue[FirstIntegrals, Timeout] > 0,
TimeConstrained[Block[{},
(* Compute functionally independent first integrals up to given degree *)
fIs=Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vf,vars,Q},deg],vars];
(* upper and lower bounds on the FIs
todo: NMaxValue instead? Needs extra LZZ check: it doesn't give the real max/mins sometimes! *)
uppers = Map[upperRat[MaxValue[{#,pre},vars]]&,fIs];
lowers = Map[lowerRat[MinValue[{#,pre},vars]]&,fIs];

(*Print["First integrals:",fIs];
Print[uppers,lowers]; *)

maxVs=Flatten[MapThread[If[#2==Infinity,{},{#1<=#2}] &, {fIs,uppers}]];
minVs=Flatten[MapThread[If[#2==-Infinity,{},{#1>=#2}] &, {fIs,lowers}]];

Union[maxVs,minVs]
], OptionValue[FirstIntegrals,Timeout],
{}],
Print["FirstIntegrals skipped."]; {}]

]


DbxPoly[problem_List] := Module[{pre,post,vf,vars,Q,polys,deg},
{pre, { vf, vars, Q }, post} = problem;

(* Heuristic *)
deg = If[OptionValue[DbxPoly,Deg] < 0,
		Max[6-Length[vars],1],
		OptionValue[DbxPoly, Deg]];

If[OptionValue[DbxPoly, Timeout] > 0,
TimeConstrained[Block[{},
(* Spend 3/4 time budget on polynomial finding *)
polys = DarbouxDDC`DarbouxPolynomialsM[{vf,vars,Q}, OptionValue[DbxPoly,Timeout]*3/4, deg];
InvariantExtractor`DWC[problem,polys,{}][[2]]
], OptionValue[DbxPoly,Timeout],
{}],
Print["DbxPoly skipped."]; {}]

]


(* Round to precisions 2,4,6,8 *)
RoundPolys[p_,vars_]:=Module[{cr},
cr = CoefficientRules[p,vars];
If[Length[cr] > 0,Map[MapAt[Function[x,Rationalize[Round[x,1/10^#]]],cr,{All,2}]~FromCoefficientRules~vars&,{2,4,6,8}]//DeleteDuplicates
,{}]]


BarrierCert[problem_List]:=Catch[Module[{pre,post,vf,vars,Q,polySOS,polys,deg},
{pre, { vf, vars, Q }, post} = problem;
If[pre===True,Return[{}]];
If[post===False,Return[{}]];

deg= If[OptionValue[BarrierCert,Deg] < 0,
		10,
		OptionValue[BarrierCert, Deg]];
			
If[OptionValue[BarrierCert, Timeout] > 0,
CheckAbort[
TimeConstrained[Block[{},
polySOS=BarrierCertificates`SOSBarrierMATLAB[problem,MaxDeg->deg];
polys=Flatten[Map[RoundPolys[#,vars]&,polySOS]];
InvariantExtractor`DWC[problem,polys,{}][[2]]
], OptionValue[BarrierCert,Timeout],
MATLink`CloseMATLAB[];{}] , Print["WARNING: BarrierCert aborted!"]]
,
Print["BarrierCert skipped."];{}]

]]


End[]
EndPackage[];
