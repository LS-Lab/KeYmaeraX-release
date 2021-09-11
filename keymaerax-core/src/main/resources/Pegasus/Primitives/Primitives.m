(* ::Package:: *)

(* Description: Basic functionality used by other packages.
   Comments: Tested in Mathematica 12.0   *)


BeginPackage["Primitives`"];


PolynomDegree::usage="PolynomDegree[P,vars] returns the total degree of a polynomial P w.r.t. the list of variables (optional)."
PolyMonomialList::usage"PolyMonomialList[P,vars] returns the list of monomials w.r.t. the list of variables(optional)"
ConstTerm::usage="ConstTerm[P,vars] returns the constant term w.r.t. the list of variables (optional)."

Lf::usage="Lf[P,vf,vars] returns the Lie derivative of P w.r.t. to ODE specified by vars'=vf"

UpperRat::usage="UpperRat[number, precision] rounds number upwards to 10^-precision"
LowerRat::usage="LowerRat[number, precision] rounds number downwards to 10^-precision"
NearestRat::usage="NearestRat[number, precision] rounds number to 10^-precision"
UpperRatCoeffs::usage="UpperRatCoeffs[number, precision]"
LowerRatCoeffs::usage="LowerRatCoeffs[number, precision]"
NearestRatCoeffs::usage="NearestRatCoeffs[number, precision]"

DNFNormalizeGtGeq::usage="DNFNormalizeGtGeq[fml] normalizes fml to a normal form only containing disjunction and conjunctions of >0 and >=0"
DNFNormalizeLtLeq::usage="DNFNormalizeLtLeq[fml] normalizes fml to a normal form only containing disjunction and conjunctions of <0 and <=0"
CNFNormalizeGtGeq::usage="DNFNormalizeGtGeq[fml] normalizes fml to a normal form only containing disjunction and conjunctions of >0 and >=0"
CNFNormalizeLtLeq::usage="DNFNormalizeLtLeq[fml] normalizes fml to a normal form only containing disjunction and conjunctions of <0 and <=0"

WeakenInequalities::usage="WeakenInequalities[fml] turns all strict inequalities to their weakened versions"
DrawPlanarProb::usage="DrawPlanarProb[prob,inv,w] draws a planar problem and invariant inv"

FuncIndep::usage="FuncIndep[polynomials_List, vars_List] Returns a list of functionally independent polynomials from a given list."

ConjugatePolynomial::usage="ConjugatePolynomial[poly] Returns the conjugate of a complex polynomial"
IsRealPolynomial::usage="IsRealPolynomial[poly] Returns true if poly is in R[x] and false if poly is not a real polynomial"
IsRatPolynomial::usage="IsRatPolynomial[poly] Returns true if poly is in R[x] with rational coefficients"
IsConcretePolynomial::usage="IsConcretePolynomial[poly, vars] returns true if the variables of poly are a subset of vars and false otherwise";

Conjuncts::usage="Conjuncts[formula] returns the conjuncts of the formula, or the formula itself if it is atomic."
Disjuncts::usage="Disjuncts[formula] returns the disjuncts of the formula, or the formula itself if it is atomic."
EqGtGeqLhs::usage="EqGtGeqLhs[formula] returns the left-hand side lhs of formulas lhs=0 or lhs>0 or lhs>=0."

CheckSemiAlgInclusion::usage="CheckSemiAlgInclusion[s_,t_,vars_List] checks if t implies s universally on vars"

InstantiateParameters::usage="InstantiateParameters[poly,vars,val] instantiates any symbolic parameter in a polynomial (not in vars) to val"

RationalQ::usage="RationalQ analogous to IntegerQ"

FindConst::usage="Find constant assumptions with respect to a variable"
FindConstHeu::usage="Find constant assumptions with respect to a variable (heuristic)"


Begin["`Private`"]


RationalQ[x_]:=(Head[x]===Rational||IntegerQ[x]);


ConjugatePolynomial[poly_]:=Module[{vars=Variables[poly]},
FromCoefficientRules[CoefficientRules[poly,vars]/.{Rule[a_,b_]:>Rule[a,Conjugate[b]]},vars]
]


IsRealPolynomial[poly_]:=Module[{vars=Variables[poly]},
AllTrue[Flatten[CoefficientList[poly,vars]], PossibleZeroQ[Im[#]]&]
]


IsRatPolynomial[poly_]:=Module[{vars=Variables[poly]},
AllTrue[Flatten[CoefficientList[poly,vars]], RationalQ[#]&]
]


IsConcretePolynomial[poly_,vars_List]:=Module[{pvars=Variables[poly]},
  SubsetQ[vars,pvars]
]

Conjuncts[formula_] := Module[{}, formula /. {
  And[a_, b_] :>
      Join[{Conjuncts[a]} // Flatten, {Conjuncts[b]} // Flatten]
}]

Disjuncts[formula_] := Module[{}, formula /. {
  Or[a_, b_] :>
      Join[{Disjuncts[a]} // Flatten, {Disjuncts[b]} // Flatten]
}]

EqGtGeqLhs[formula_] := Module[{}, (formula//ZeroRHS) /. {
  Equal[a_, 0] :> a,
  Greater[a_, 0] :> a,
  GreaterEqual[a_, 0] :> a
}]

(* Instantiating symbolic parameters in polynomials *)
InstantiateParameters[poly_,vars_List,val_]:=poly/.Map[Rule[#, val]&,Complement[Variables[poly],vars] ]


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_,vars_List]:= Max[Cases[CoefficientRules[P,vars], v_?VectorQ :> Total[v], 2]]
PolynomDegree[P_] := PolynomDegree[P,Variables[P]]

(* Return all monomials of a given polynomial wrt the variables -- less annoying than the builtin MonomialList *)
PolyMonomialList[P_, vars_list] := Times @@ (vars^#) & /@ CoefficientRules[P, vars][[All, 1]]
PolyMonomialList[P_] := PolyMonomialList[P,Variables[P]]

(* Return the constant term in a polynomial *)
ConstTerm[P_,vars_List]:=(Table[0,Length[vars]]/.CoefficientRules[P,vars])/.{a_List:>0}
ConstTerm[P_]:=ConstTerm[P,Variables[P]]


(* Lie derivative of P w.r.t. ODEs *)
Lf[P_,vf_List,vars_List,domain_] := FullSimplify[Grad[P,vars].vf, And[domain, Map[#\[Element]Reals&,vars]/.{List->And}]];
Lf[P_,vf_List,vars_List] := Lf[P,vf,vars,True];


(* Upper, lower and nearest rational bounds of a number, nearest 10^-precision *)
UpperRat[x_?NumericQ, precision_?Positive]:=Module[{uncertainty},
  uncertainty=Abs[x]*10^-precision;
  Rationalize[N[x,precision]+uncertainty, uncertainty]
]
LowerRat[x_?NumericQ, precision_?Positive]:=Module[{uncertainty},
  uncertainty=Abs[x]*10^-precision;
  Rationalize[N[x,precision]-uncertainty, uncertainty]
]
NearestRat[x_?NumericQ, precision_?Positive]:=Module[{uncertainty},
  uncertainty=Abs[x]*10^-precision;
  Rationalize[N[x,precision], uncertainty]
]

(* Rounding on polynomials *)
RatCoeffs[p_?PolynomialQ, vars_List, precision_?NonNegative,dir_]:=Module[{coeffRules},
  coeffRules=CoefficientRules[p, vars];
  coeffRules=Switch[dir,
  "Upper",   coeffRules/.{Rule[$MON_,$COEFF_]-> Rule[$MON,UpperRat[$COEFF,precision]]},
  "Lower",   coeffRules/.{Rule[$MON_,$COEFF_]-> Rule[$MON,LowerRat[$COEFF,precision]]},
  "Nearest", coeffRules/.{Rule[$MON_,$COEFF_]-> Rule[$MON,NearestRat[$COEFF,precision]]},
  _, Throw[dir]
  ];
  FromCoefficientRules[coeffRules,vars]
];

UpperRatCoeffs[p_?PolynomialQ, vars_List, precision_?NonNegative] := RatCoeffs[p,vars,precision,"Upper"]
LowerRatCoeffs[p_?PolynomialQ, vars_List, precision_?NonNegative] := RatCoeffs[p,vars,precision,"Lower"]
NearestRatCoeffs[p_?PolynomialQ, vars_List, precision_?NonNegative] := RatCoeffs[p,vars,precision,"Nearest"]


(* Standard normalization conventions used throughout Pegasus *)

(* Set right-hand side of terms to zero *)
ZeroRHS[formula_]   :=  Module[{},formula/.{
	Equal[a_,b_]        :>  Equal[a-b,0],
	Unequal[a_,b_]      :>  Unequal[a-b,0],
	Greater[a_,b_]      :>  Greater[a-b,0],
	GreaterEqual[a_,b_] :>  GreaterEqual[a-b,0],
	Less[a_,b_]         :>  Less[a-b,0], 
	LessEqual[a_,b_]    :>  LessEqual[a-b,0]
}]

(* Standardize (in)equalities *)
GeqToLeq[formula_]:=Module[{}, formula/.{         GreaterEqual[lhs_,rhs_] :>  LessEqual[rhs,lhs]} ] 
GtToLt[formula_]:=Module[{}, formula/.{           Greater[lhs_,rhs_]      :>  Less[rhs,lhs]} ] 
LeqToGeq[formula_]:=Module[{}, formula/.{         LessEqual[lhs_,rhs_] :>  GreaterEqual[rhs,lhs]} ] 
LtToGt[formula_]:=Module[{}, formula/.{           Less[lhs_,rhs_]      :>  Greater[rhs,lhs]} ] 
UnequalToLtOrGt[formula_]:=Module[{}, formula/.{  Unequal[lhs_,rhs_]      :>  Or[Less[lhs,rhs] ,Less[rhs,lhs]]} ] 
EqualToLeqAndGeq[formula_]:=Module[{}, formula/.{ Equal[lhs_,rhs_]        :>  And[LessEqual[lhs,rhs] ,LessEqual[rhs,lhs]]} ] 
LeqToLtOrEqual[formula_]:=Module[{}, formula/.{   LessEqual[lhs_,rhs_]    :>  Or[Less[lhs,rhs] ,Equal[rhs,lhs]]} ] 

(* Normalize expression to DNF form (Or of Ands) with >, \[GreaterEqual] only *)
DNFNormalizeGtGeq[expression_]:=Module[{},
  BooleanMinimize[expression//LogicalExpand//UnequalToLtOrGt//EqualToLeqAndGeq//LtToGt//LeqToGeq//ZeroRHS, "DNF"]] 
DNFNormalizeLtLeq[expression_]:=Module[{},
  BooleanMinimize[expression//LogicalExpand//UnequalToLtOrGt//EqualToLeqAndGeq//GtToLt//GeqToLeq//ZeroRHS, "DNF"]] 

(* Normalize expression to CNF form (And of Ors) with >, \[GreaterEqual] only *)
CNFNormalizeGtGeq[expression_]:=Module[{},
  BooleanMinimize[expression//LogicalExpand//UnequalToLtOrGt//EqualToLeqAndGeq//LtToGt//LeqToGeq//ZeroRHS, "CNF"]] 
CNFNormalizeLtLeq[expression_]:=Module[{},
  BooleanMinimize[expression//LogicalExpand//UnequalToLtOrGt//EqualToLeqAndGeq//GtToLt//GeqToLeq//ZeroRHS, "CNF"]] 



(* Weaken inequalities *)
WeakenInequalities[formula_]  :=  Module[{},formula/.{
	Unequal[a_,b_]      :>  True,
	Greater[a_,b_]      :>  GreaterEqual[a,b],
	Less[a_,b_]         :>  LessEqual[a,b]
	}]


(* Drawing primitive *)
ExpandEq[formula_]   :=  Module[{},formula/.{
	Equal[a_,b_]        :>  LessEqual[(a-b)^2,0.01]
}]

DrawPlanarProb[prob_List, invariant_:False, w_:6 ] := Module[{init,f,x,y,H,safe,x1min,x1max,x2min,x2max,rules,inv},
  If[Length[prob[[2]][[2]]]!=2, Print["Non-planar problem"]; Return[]];
  rules = Rule @@@ Transpose[{prob[[2]][[2]],{x,y}}];
  {init, { f, {x, y}, H }, safe } = prob/.rules//ExpandEq;
  inv = invariant/.rules//ExpandEq;
  {x1min, x1max} = {-w, w};
  {x2min, x2max} = {-w, w};
    
  Show[
	(* Plot unsafe states in red *)
    RegionPlot[Not[safe], {x, x1min, x1max}, {y, x2min, x2max}, PlotStyle -> Opacity[0.2,Red],
      FrameLabel -> {prob[[2]][[2]][[1]], prob[[2]][[2]][[2]]}, FrameTicks -> None, LabelStyle -> Directive[Large],PlotPoints -> 100],
    (* Plot initial states in green *)
    RegionPlot[init, {x, x1min, x1max}, {y, x2min, x2max}, PlotStyle -> Opacity[0.2,Green],PlotPoints -> 100],
    (* Plot invariant in magenta *)
    RegionPlot[inv, {x, x1min, x1max}, {y, x2min, x2max}, PlotStyle -> Opacity[0.2,Magenta],PlotPoints -> 100],
    (* Plot vector field *)
    StreamPlot[f, {x, x1min, x1max}, {y, x2min, x2max}, StreamStyle -> Darker[Gray]],
    (* Plot domain in blue *)
    RegionPlot[H, {x, x1min, x1max}, {y, x2min, x2max}, PlotStyle -> Opacity[0.05,Blue]]
    ]
]


FuncIndep[polys_List, vars_List]:=Module[{sortedlist,span,pool,gradList,Gramian},
If[Length[polys]>0,
sortedlist=Sort[polys,And[Primitives`PolynomDegree[#1]<=Primitives`PolynomDegree[#2], Length[#1]<=Length[#2]]&];
span={First[sortedlist]};
pool=Rest[sortedlist];
While[Length[pool]>0 && Length[span]<Length[vars],
gradList = Map[Grad[#,vars]&, Append[span,First[pool]]];
Gramian=gradList.Transpose[gradList];
(* Debugging 
Print[Gramian//MatrixForm];
Print[Det[Gramian]];
*)
If[TrueQ[Reduce[Exists[vars,Det[Gramian]>0],Reals]],
 span=Append[span,First[pool]]; 
pool=Rest[pool],
pool=Rest[pool]
]];
span, polys]
]


CheckSemiAlgInclusion[subset_,set_,vars_List]:=Module[{},
TrueQ[Reduce[ForAll[vars, Implies[subset,set]],Reals]]
]


FindConst[ff_,var_,symbols_]:=Module[{ls,repr},
ls = {ff//.And -> List}//Flatten;
(* TODO: This line doesn't seem correct... *)
repr = Select[Cases[ls,Equal[var,rhs_]->rhs],Not[MemberQ[symbols,#]]&]//DeleteDuplicates;
If[Length[repr]>1,Print["Detected multiple values for ",var,repr]];
If[Length[repr]==1,{var -> First[repr]},{}]
]

FindConstHeu[ff_,var_,symbols_]:=Module[{ls,repr,reprL,reprR},
ls = {ff//.And -> List}//Flatten;
(* TODO: This line doesn't seem correct... *)
reprL = Select[Cases[ls,GreaterEqual[var-rhs_,0]->rhs],Not[MemberQ[symbols,#]]&];
reprR = Select[Cases[ls,GreaterEqual[var-rhs_,0]->rhs],Not[MemberQ[symbols,#]]&];
repr=Join[reprL,reprR]//DeleteDuplicates;
If[Length[repr]>1,Print["Detected multiple values for ",var,repr]];
If[Length[repr]==1,{var -> First[repr]},{}]
]


End[]
EndPackage[]
