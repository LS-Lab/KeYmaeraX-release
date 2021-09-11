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
(* Returns a heuristic end degree, if endDeg<0, returns endDeg otherwise. *)
DbxPolyEndDegree::usage="DbxPolyEndDegree[problem_List, endDeg_]";
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
Options[FirstIntegrals]= {Deg -> -1, Timeout -> 20, Numerical -> True};
Options[DbxPoly]= {MaxDeg -> -1, Staggered -> False, Timeout -> 30};
Options[BarrierCert]= {Deg -> -1, Timeout -> 60};


Begin["`Private`"];


PreservedState[problem_List]:=Module[{pre,post,vf,vars,Q,polys,result,constvars,constasms,prob},
	{pre, { vf, vars, Q }, post, {constvars,constasms}} = problem;
    (* temporary fix: *) 
    prob ={pre, { vf, vars, Q }, post};
	If[OptionValue[PreservedState, Timeout] > 0,
		TimeConstrained[
      PreservedState`PreservedPre[vf,vars,pre,Q]//DeleteDuplicates
      ,
      OptionValue[PreservedState,Timeout], {} (* Outside: reap and use last sown intermediate result on failureQ/empty main result *)
    ]
		,
		Print["PreservedState skipped."]; {}]
]

HeuInvariants[problem_List]:=Module[{pre,post,vf,vars,Q,polys, prob, constvars,constasms},
{pre, { vf, vars, Q }, post, {constvars,constasms}} = problem;
(* temporary fix: *) 
prob = {pre, { vf, vars, Q }, post};

If[OptionValue[HeuInvariants, Timeout] > 0,
TimeConstrained[Block[{},
  polys = DeleteDuplicates[Join[
    QualAbsPolynomials`SummandFactors[prob],
    QualAbsPolynomials`SFactorList[prob],
    QualAbsPolynomials`ProblemFactors[prob]
    (*,
    QualAbsPolynomials`ProblemFactorsWithLie[prob],
    QualAbsPolynomials`PhysicalQuantities[prob],
    *)
  ]];
  (*res=Map[InvariantExtractor`DWC[problem,{#},{},False]&,polys];*)
  InvariantExtractor`DWC[problem,polys,{},False][[2]]
  ],
  OptionValue[HeuInvariants,Timeout], {}], (* Outside: reap and use last sown intermediate result on failureQ/empty main result *)
Print["HeuInvariants skipped."]; {}]

]


FirstIntegrals[problem_List, opts:OptionsPattern[]]:=Module[{
	pre,post,vf,vars,Q,
	fIs,fIc,fIres,maxminVs,deg,
	rat,uppers,lowers,bound,constvars,constasms,constrepl,vfe,varse},
{pre, { vf, vars, Q }, post, {constvars,constasms}} = problem;

(* Heuristic *)
deg = If[OptionValue[FirstIntegrals,Deg] < 0,
		Max[10-Length[vars],1],
		OptionValue[FirstIntegrals, Deg]];
rat = 5;
bound=10^8;

vfe=Join[vf,Table[0,{i,Length[constvars]}]];
varse=Join[vars,constvars];

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[Element[num,Reals] && num < bound],Primitives`UpperRat[num, rat], Infinity];
lowerRat[num_]:=If[TrueQ[Element[num,Reals] && num > -bound],Primitives`LowerRat[num, rat], -Infinity];

If[OptionValue[FirstIntegrals, Timeout] > 0,
TimeConstrained[Block[{},
(* Compute functionally independent first integrals up to given degree *)
fIs=Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vfe,varse,Q},deg],varse];

(* upper and lower bounds on the FIs.
todo: NMaxValue instead? Needs extra LZZ check: it doesn't give the real max/mins sometimes! *)
If[TrueQ[OptionValue[FirstIntegrals, Numerical]],
Block[{},
uppers = Map[upperRat[NMaxValue[{#,pre&&constasms},varse]]&,fIs];
lowers = Map[lowerRat[NMinValue[{#,pre&&constasms},varse]]&,fIs]],
Block[{},
uppers = Map[upperRat[MaxValue[{#,pre&&constasms},varse]]&,fIs];
lowers = Map[lowerRat[MinValue[{#,pre&&constasms},varse]]&,fIs]]];

(* First integrals where initial values are fixed *)
constrepl=Join[Map[Primitives`FindConstHeu[pre,#,vars]&,vars],Map[Primitives`FindConst[pre,#,vars]&,vars]]//Flatten;
fIc = fIs/.constrepl;
fIres = MapThread[If[#1===#2,{},
	If[Intersection[Variables[#2],vars]=={},{#1-#2<=0,#1-#2>=0},{}]]&,{fIs,fIc}]//Flatten;

maxminVs=Flatten[MapThread[
  (* If the upper and lower bound are the same and non-infinity, return the equality *)
  If[#2==#3&&#2!=Infinity,{#1==#2},
    (* Else return the two bounds separately*)
    {If[#2==Infinity,{},{#1<=#2}], If[#3==-Infinity,{},{#1>=#3}]}] &,
  {fIs,uppers,lowers}]];

Join[maxminVs,fIres]
], OptionValue[FirstIntegrals,Timeout], {} (* Outside: reap and use last sown intermediate result on failureQ/empty main result *)
],
Print["FirstIntegrals skipped."]; {}]

]


(* Darboux polynomials: exhaust until timeout, return all found ones. *)
DbxPoly[problem_List, endDeg_] := Module[{pre,post,vf,vars,Q,polys,deg,constvars,constasms,prob},
{pre, { vf, vars, Q }, post, {constvars,constasms}} = problem;
(* temporary fix: *) 
prob ={pre, { vf, vars, Q }, post};

If[OptionValue[DbxPoly, Timeout] > 0,
TimeConstrained[Block[{},
(* Spend 1/2 time budget on polynomial finding *)
polys = DarbouxDDC`DarbouxPolynomialsM[{vf,vars,Q}, OptionValue[DbxPoly,Timeout]*1/2, deg];
InvariantExtractor`DWC[problem,polys,{},False][[2]]
], OptionValue[DbxPoly,Timeout],
{}],  (* Outside: reap and use last sown intermediate result on failureQ/empty main result *)
Print["DbxPoly skipped."]; {}]

]

(* Returns a heuristic end degree if endDeg<0, returns endDeg otherwise *)
DbxPolyEndDegree[problem_List, endDeg_] := Module[{pre, vf, vars, Q, post,constvars,constasms,prob},
	{pre, { vf, vars, Q }, post, {constvars,constasms}} = problem;
	prob = {pre, { vf, vars, Q }, post};
	If[endDeg < 0, Max[10-Length[vars],1], endDeg]
]

(* Darboux polynomials: sowing intermediate results and checking whether done before increasing degree. *)
DbxPolyIntermediate[problem_List, startDeg_, endDeg_] := Module[{pre,post,vf,vars,Q,polys,allPolys,allPolysI,invs,deg,timeout,dbxResult,constvars,constasms,prob},
	{pre, { vf, vars, Q }, post, {constvars,constasms}} = problem;
    (* temporary fix: *) 
    prob ={pre, { vf, vars, Q }, post};

	Print["Darboux degrees: ", startDeg, "-", endDeg];

	If[OptionValue[DbxPoly, Timeout] > 0,
		timeout = OptionValue[DbxPoly, Timeout];
		TimeConstrained[Block[{},
			Catch[
				invs = {};
				allPolys = {};
				(* Spend 1/2 on polynomial finding, 1/2 on invariant extraction and checking *)
				(* upgrade to Mathematica 12.1: consider TimeRemaining[] to balance degrees *)
				For[i=startDeg,i<=endDeg,i++,
					Print["Degree: ", i];
					polys = TimeConstrained[DarbouxPolynomials`DbxDefault[{vf, vars, Q}, i], timeout/2, {}];
					Print["Polys: ", polys];
					allPolysI = Union[allPolys, polys];
					If[allPolysI != allPolys,
						allPolys = allPolysI;
						Print["Generated Darboux polynomials: ", polys, " at degree ", i];
						TimeConstrained[
							(* Invariant extractor throws result when done; if it doesn't throw result, Sow intermediate result, then proceed.  *)
							invs = Union[invs, InvariantExtractor`DWC[problem, polys, {}, False][[2]]];
							Print["Extracted Darboux invariants (not yet sufficient): ", invs];
							Sow[invs]
							,
							timeout/2
						]
						,
						Print["No new invariants"]
					]
				];
				invs
			]
		], timeout, {}] (* Outside: reap and use last sown intermediate result on failureQ/empty main result *)
		,
		Print["DbxPoly skipped."]; {}
	]
]

(* Round to precisions 2,4,6,8 *)
RoundPolys[p_,vars_]:=Module[{cr},
cr = CoefficientRules[p,vars];
If[Length[cr] > 0,Map[MapAt[Function[x,Rationalize[Round[x,1/10^#]]],cr,{All,2}]~FromCoefficientRules~vars&,{2,4,6,8}]//DeleteDuplicates
,{}]]


BarrierCert[problem_List, maxDeg_]:=Catch[Module[
{pre,post,vf,vars,Q,polySOS,polys,deg,constvars,constasms,prob,allf,allvars},

{pre, { vf, vars, Q }, post,{constvars,constasms}} = problem;
prob = {pre, { vf, vars, Q }, post};

If[pre===True,Return[{}]];
If[post===False,Return[{}]];

deg= If[maxDeg < 0, 10, maxDeg];

If[OptionValue[BarrierCert, Timeout] > 0,
CheckAbort[
TimeConstrained[Block[{},
polySOS=BarrierCertificates`SOSBarrierMATLAB[{pre && constasms, {vf,vars,Q}, post},MaxDeg->deg];
polys=Flatten[Map[RoundPolys[#,Join[vars,constvars]]&,polySOS]];
InvariantExtractor`DWC[problem,polys,{},False,False,{"<","<="}][[2]]
], Max[0,OptionValue[BarrierCert,Timeout]-0.5], (* slightly reduce timeout to abort here and close MATLink *)
MATLink`CloseMATLAB[];{}] , Print["WARNING: BarrierCert aborted!"];{}] (* Outside: reap and use last sown intermediate result on failureQ/empty main result *)
,
Print["BarrierCert skipped."];{}]

]]


End[]
EndPackage[];
