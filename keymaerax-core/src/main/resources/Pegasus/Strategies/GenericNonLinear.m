(* ::Package:: *)

(*
	Description: Generic strategies for non-linear vector fields.
	This file summarizes all the basic strategies that generate invariants from a problem.
	This will be used by DiffSat
*)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]]
Needs["QualAbsPolynomials`",FileNameJoin[{Directory[],"Primitives","QualAbsPolynomials.m"}]]
Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"Primitives","DarbouxPolynomials.m"}]]
Needs["DarbouxDDC`",FileNameJoin[{Directory[],"Strategies","DarbouxDDC.m"}]]
Needs["InvariantExtractor`",FileNameJoin[{Directory[],"Strategies","InvariantExtractor.m"}]]
Needs["BarrierCertificates`",FileNameJoin[{Directory[],"Primitives","BarrierCertificates.m"}]]
Needs["PreservedState`",FileNameJoin[{Directory[],"Primitives","PreservedState.m"}]]


BeginPackage[ "GenericNonLinear`"];


(*BarrierCert::usage="BarrierCertificates[problem_List]";
SummandFacts::usage="SummandFactors[problem_List]";
*)

(* Returns invariants generated from pre *)
PreservedState::usage="PreservedState[problem_List]";
(* Returns invariants generated using first integrals *)
FirstIntegrals::usage="FirstIntegrals[problem_List,degree]";
(* Returns invariants generated using Darboux polynomials *)
DbxPoly::usage="DbxPoly[problem_List]";
(* Returns invariants and intermediate candidates generated using Darboux polynomials *)
DbxPolyIntermediate::usage="DbxPoly[problem_List]";
(* Returns invariants generated from heuristics *)
HeuInvariants::usage="Heuristics[problem_List,degree]";
(* Returns invariants generated from barrier certificate *)
BarrierCert::usage="BarrierCert[problem_List]";

(* Options and defaults for each of these methods
	Deg \[Rule] -1 means run with default heuristic for choosing the degree
	The default values are configured assuming a 2 minute timeout
*)
Options[PreservedState]= {Timeout -> 10};
Options[HeuInvariants]= {Timeout -> 20};
Options[FirstIntegrals]= {Deg -> -1, Timeout -> 20};
Options[DbxPoly]= {StartDeg -> 1, MaxDeg -> -1, Staggered -> False, CurDeg -> -1, Timeout -> 30};
Options[BarrierCert]= {Deg -> -1, Timeout -> Infinity};


Begin["`Private`"];


PreservedState[problem_List]:=Module[{pre,post,vf,vars,Q,polys},
	{pre, { vf, vars, Q }, post} = problem;
	If[OptionValue[PreservedState, Timeout] > 0,
		TimeConstrained[Block[{},
			polys = PreservedState`PreservedPre[vf,vars,pre,Q]//DeleteDuplicates;
			InvariantExtractor`DWC[problem,polys,{},False][[2]]
		], OptionValue[PreservedState,Timeout],
			{}],
		Print["PreservedState skipped."]; {}]
]

HeuInvariants[problem_List]:=Module[{pre,post,vf,vars,Q,polys},
{pre, { vf, vars, Q }, post} = problem;

If[OptionValue[HeuInvariants, Timeout] > 0,
TimeConstrained[Block[{},
polys = DeleteDuplicates[Join[
	QualAbsPolynomials`SummandFactors[problem],
	QualAbsPolynomials`SFactorList[problem],
	QualAbsPolynomials`ProblemFactors[problem]
	(*,
	QualAbsPolynomials`ProblemFactorsWithLie[problem],
	QualAbsPolynomials`PhysicalQuantities[problem],
	*)
	]];
(*res=Map[InvariantExtractor`DWC[problem,{#},{},False]&,polys];*)
InvariantExtractor`DWC[problem,polys,{},False][[2]]
], OptionValue[HeuInvariants,Timeout],
{}],
Print["HeuInvariants skipped."]; {}]

]


FirstIntegrals[problem_List, opts:OptionsPattern[]]:=Module[{
	pre,post,vf,vars,Q,
	fIs,maxminVs,deg,
	rat,uppers,lowers,bound},
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

maxminVs=Flatten[MapThread[
  (* If the upper and lower bound are the same and non-infinity, return the equality *)
  If[#2==#3&&#2!=Infinity,{#1==#2},
    (* Else return the two bounds separately*)
    {If[#2==Infinity,{},{#1<=#2}], If[#3==-Infinity,{},{#1>=#3}]}] &,
  {fIs,uppers,lowers}]];

maxminVs
], OptionValue[FirstIntegrals,Timeout],
{}],
Print["FirstIntegrals skipped."]; {}]

]


(* Darboux polynomials: exhaust until timeout, return all found ones. *)
DbxPoly[problem_List] := Module[{pre,post,vf,vars,Q,polys,deg},
{pre, { vf, vars, Q }, post} = problem;

(* Heuristic *)
deg = If[OptionValue[DbxPoly,MaxDeg] < 0,
		Max[10-Length[vars],1],
	OptionValue[DbxPoly,MaxDeg]];

If[OptionValue[DbxPoly, Timeout] > 0,
TimeConstrained[Block[{},
(* Spend 1/2 time budget on polynomial finding *)
polys = DarbouxDDC`DarbouxPolynomialsM[{vf,vars,Q}, OptionValue[DbxPoly,Timeout]*1/2, deg];
InvariantExtractor`DWC[problem,polys,{},False][[2]]
], OptionValue[DbxPoly,Timeout],
{}],
Print["DbxPoly skipped."]; {}]

]

(* Darboux polynomials: sowing intermediate results and checking whether done before increasing degree. *)
DbxPolyIntermediate[problem_List] := Module[{pre,post,vf,vars,Q,polys,allPolys,allPolysI,invs,deg,timeout,dbxResult},
	{pre, { vf, vars, Q }, post} = problem;

	(* Heuristic *)
	If[OptionValue[DbxPoly,MaxDeg] < 0,
		(* Set maximum degree, picked up by others (e.g., DiffSat) to decide whether to recurse. *)
		SetOptions[DbxPoly,MaxDeg -> Max[10-Length[vars],1]]];
	deg = If[OptionValue[DbxPoly,CurDeg] < 0,
		OptionValue[DbxPoly,MaxDeg],
		Min[OptionValue[DbxPoly,MaxDeg], OptionValue[DbxPoly,CurDeg]]];

	Print["Darboux degrees: ", OptionValue[DbxPoly,StartDeg], "-", deg];

	If[OptionValue[DbxPoly, Timeout] > 0,
		dbxResult = Reap[TimeConstrained[Block[{},
			Catch[
				invs = {};
				allPolys = {};
				(* Spend 1/2 on polynomial finding, 1/2 on invariant extraction and checking *)
				(* upgrade to Mathematica 12.1: consider TimeRemaining[] to balance degrees *)
				For[i=OptionValue[DbxPoly,StartDeg],i<=deg,i++,
					Print["Degree: ", i];
					timeout = OptionValue[DbxPoly, Timeout](*/deg*);
					polys = TimeConstrained[DarbouxPolynomials`DbxDefault[{vf, vars, Q}, i], timeout/2, {}];
					Print["Polys: ", polys];
					allPolysI = Union[allPolys, polys];
					If[allPolysI != allPolys,
						allPolys = allPolysI;
						Print["Generated Darboux polynomials: ", polys, " at degree ", i];
						TimeConstrained[
							invs = Union[invs, InvariantExtractor`DWC[problem, polys, {}, False][[2]]];
							Print["Extracted Darboux invariants: ", invs];
							If[Length[invs]>0,
								If[TrueQ[Primitives`CheckSemiAlgInclusion[And[Q, And@@invs], post, vars]],
									Throw[invs],
									Sow[invs]
								]
							],
							timeout/2
						]
						,
						Print["No new invariants"]
					]
				]
			]
		], OptionValue[DbxPoly,Timeout]]];
		If[FailureQ[dbxResult[[1]]],
			If[Length[dbxResult[[2]]]>0, dbxResult[[2]][[1]][[-1]], {}],
			dbxResult[[1]]
		]
		,
		Print["DbxPoly skipped."]; {}
	]
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
InvariantExtractor`DWC[problem,polys,{},False,False][[2]]
], OptionValue[BarrierCert,Timeout],
MATLink`CloseMATLAB[];{}] , Print["WARNING: BarrierCert aborted!"]]
,
Print["BarrierCert skipped."];{}]

]]


End[]
EndPackage[];
