(* ::Package:: *)

(* Description: Basic functionality used by other packages.
   Comments: Tested in Mathematica 10.0   *)


BeginPackage[ "Primitives`"]


PolynomDegree::usage="PolynomDegree[P] returns the total degree of a polynomial P."
UpperRat::usage="UpperRat[number, precision]"
LowerRat::usage="LowerRat[number, precision]"
UpperRatCoeffs::usage="UpperRatCoeffs[number, precision]"


Begin["`Private`"]


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_]:=Module[{},
Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]]
]


(* Upper rational bound of a number *)
UpperRat[x_?NumericQ, precision_?Positive]:=Module[{},
uncertainty=Abs[x]*10^-precision;
Rationalize[N[x,precision]+uncertainty, uncertainty]
]
(* Lower rational bound of a number *)
LowerRat[x_?NumericQ, precision_?Positive]:=Module[{},
uncertainty=Abs[x]*10^-precision;
Rationalize[N[x,precision]-uncertainty, uncertainty]
]


UpperRatCoeffs[p_?PolynomialQ, vars_List, precision_?NonNegative]:=Module[{},
coeffRules=CoefficientRules[p, vars];
coeffRules=coeffRules/.{Rule[$MON_,$COEFF_]->Rule[$MON,UpperRat[$COEFF,precision]]};
FromCoefficientRules[coeffRules,vars]
]


End[]
EndPackage[]
