(* ::Package:: *)

(* Description: Basic functionality used by other packages.
   Comments: Tested in Mathematica 10.0   *)


BeginPackage[ "Primitives`"]


PolynomDegree::usage="PolynomDegree[P,vars] returns the total degree of a polynomial P w.r.t. the list of variables (optional)."
ConstTerm::usage="ConstTerm[P,vars] returns the constant term w.r.t. the list of variables (optional)."
Lf::usage="Lf[P,vf,vars] returns the Lie derivative of P w.r.t. to ODE specified by vars'=vf"
UpperRat::usage="UpperRat[number, precision] rounds number upwards to 10^-precision"
LowerRat::usage="LowerRat[number, precision] rounds number downwards to 10^-precision"
NearestRat::usage="NearestRat[number, precision] rounds number to 10^-precision"
UpperRatCoeffs::usage="UpperRatCoeffs[number, precision]"
LowerRatCoeffs::usage="LowerRatCoeffs[number, precision]"
NearestRatCoeffs::usage="NearestRatCoeffs[number, precision]"
DNFNormalize::usage="DNFNormalize[fml]"


Begin["`Private`"]


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_,vars_List]:= Max[Cases[CoefficientRules[P,vars], v_?VectorQ :> Total[v], 2]]
PolynomDegree[P_] := PolynomDegree[P,Variables[P]]


(* Return the constant term in a polynomial *)
ConstTerm[P_,vars_List]:=(Table[0,Length[vars]]/.CoefficientRules[P,vars])/.{a_List:>0}
ConstTerm[P_]:=ConstTerm[P,Variables[P]]


(* Lie derivative of P w.r.t. ODEs *)
Lf[P_,vars_List,vf_List] := Grad[P,vars].vf;


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
LeqToGeq[formula_]:=Module[{}, formula/.{         LessEqual[lhs_,rhs_] :>  GreaterEqual[rhs,lhs]} ] 
LtToGt[formula_]:=Module[{}, formula/.{           Less[lhs_,rhs_]      :>  Greater[rhs,lhs]} ] 
UnequalToLtOrGt[formula_]:=Module[{}, formula/.{  Unequal[lhs_,rhs_]      :>  Or[Less[lhs,rhs] ,Less[rhs,lhs]]} ] 
EqualToLeqAndGeq[formula_]:=Module[{}, formula/.{ Equal[lhs_,rhs_]        :>  And[LessEqual[lhs,rhs] ,LessEqual[rhs,lhs]]} ] 
LeqToLtOrEqual[formula_]:=Module[{}, formula/.{   LessEqual[lhs_,rhs_]    :>  Or[Less[lhs,rhs] ,Equal[rhs,lhs]]} ] 

(* Normalize expression to DNF form (Or of Ands) with >, \[GreaterEqual] only *)
DNFNormalize[expression_]:=Module[{},
  BooleanMinimize[expression//LogicalExpand//UnequalToLtOrGt//EqualToLeqAndGeq//LtToGt//LeqToGeq//ZeroRHS, "DNF"]] 


End[]
EndPackage[]
