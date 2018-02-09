(* ::Package:: *)

(*
   Description:
	Implementation of a procedure for generating polynomial first integrals for
	autonomous (i.e. time-independent) systems of polynomial ODEs.

   Comments: Tested in Mathematica 10.0   *)


BeginPackage[ "FirstIntegralGen`"]


FindFirstIntegrals::usage="
FindFirstIntegrals[deg_Integer?NonNegative, vars_List, vectorField_List] 
computes a list of polynomial first integrals (up to some given maximum
polynomial total degree in the variables 'vars') for the system of ODEs
described by vectorField. The variable order MATTERS, e.g. if vars={x,y} and
vectorField={x^2+1, x+y-2}, this is interpreted as the system of ODEs x'=x^2+1,
y'=x+y-2. Changing the order of variables or entries in vectorField will
generally result in different systems of ODEs."


FindFirstIntegralsPDE::usage="
FindFirstIntegralsPDE[vars_List, vectorField_List] 
computes a list of POTENTIALLY NON-POLYNOMIAL first integrals in the variables 'vars'
for the system of ODEs described by vectorField. The variable order MATTERS, e.g. if vars={x,y} and
vectorField={x^2+1, x+y-2}, this is interpreted as the system of ODEs x'=x^2+1,
y'=x+y-2. Changing the order of variables or entries in vectorField will
generally result in different systems of ODEs."


Begin[ "Private`" ]


(* Computing the Lie derivative of some given function P w.r.t. the given vector field *)
LieDerivative[P_,vars_List,VectorField_List]:=Module[{},
Expand[Grad[P,vars].VectorField]
]


(* Computing the monomial basis for polynomials of maximal total degree maxdeg *)
GenMonomialBasis[vars_List,maxdeg_Integer?NonNegative]:=Module[{},
Select[Permutations[Flatten[Table[Table[j,{i,1,Length[vars]}],{j,0,maxdeg}]],{Length[vars]}], Apply[Plus, #] <= maxdeg &]
]


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_]:=Module[{},
Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]]
]


(* Implementation of the Matringe-Moura-Rebiha polynomial first integral generation method *)
FindFirstIntegrals[deg_Integer?NonNegative,vars_List,vectorField_List]:=Module[{
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vectorField]]},
(* Compute the monomial basis *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasis[vars,r]],vars]];
(* Compute the Lie derivatives of the monomial basis *)
LieDMonBas=Map[LieDerivative[#,vars,vectorField]&, MonBas];
(* Compute the coefficient rules for each of the Lie derivatives of the monomial basis *)
LieDMonBasCoeffs=Map[CoefficientRules[#,vars]&, LieDMonBas];
(* Create a matrix of monomial basis elements for polynomials of degree r+d-1 as its row entries, with |MonBas| rows in total *)
NewBasisMat=Table[GenMonomialBasis[vars,r+d-1], {i,1,Length[MonBas]}];
(* For each row j, substitute the monomial coefficients of the Lie derivative of the j-th monomial element in MonBas; then transpose *)
MD=Transpose[Table[Map[If[ListQ[#],0,#]&,NewBasisMat[[j]]/.LieDMonBasCoeffs[[j]]], {j,1,Length[MonBas]}]];
(* Turn the null space vectors into polynomials in the monomial basis and return the result *)
Map[Apply[Plus,Times[MonBas,#]]&,NullSpace[MD]]
]


(* Implementation of a first integral generation method based on solving PDEs *)
FindFirstIntegralsPDE[vars_List,vectorField_List]:=Module[{},
(* Set FIC to be the First Integral Candidate in the state variables *)
FIC=FICandidate[Apply[Sequence,vars]];
(* Formulate PDE problem: seeking function in the state variables, i.e. (\[PartialD]FIC/\[PartialD]x)*x' + (\[PartialD]FIC/\[PartialD]y)*y' + etc. = 0 *)
PDE=(LieDerivative[FIC,vars,vectorField]==0);
(* Reals assumption*)
OverReals=Apply[And, Map[#\[Element]Reals &, vars]];
(* Solve the PDE using methods available in Mathematica *)
solution=PowerExpand[Assuming[OverReals,DSolve[PDE,FIC,vars]]];
(* Extract first integrals from solutions, replacing functions C[1], C[2], etc. with Simplify *) 
integrals=(FIC/.solution)/.{C[_]->Simplify} 
]


End[]


EndPackage[]
