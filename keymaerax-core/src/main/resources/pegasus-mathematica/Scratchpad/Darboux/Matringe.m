(* ::Package:: *)

BeginPackage["Matringe`"];


MatringeDbx::usage=""


Begin["`Private`"];


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_]:=Module[{},
Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]]
]


MatringeDbx[deg_Integer,vf_List,vars_List]:=Catch[Module[
{monbas, newMonbas, coeffs, template, Dtemplate, basisVect, 
newBasisVect, PolyBasis, LieD, MD,LT, MonBas,cofactCoeffs,
cofactBasis,cofactTemplate, choices, evaluations, rk, minrk, 
cofactor,nullspace,minInstance, r=deg, (* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vf]]},

If[deg<=0, Throw[0]];
(* Compute monomial basis in lexicographic order *)
MonBas[maxdeg_]:=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^maxdeg , vars, "Lexicographic"]];
monbas= MonBas[deg];
(* Compute the symbolic coefficients of the polynomial template *)
coeffs=Table[Symbol["COEFF"<>ToString[i]],{i,1,Length[monbas]}];
cofactBasis=MonBas[d-1];
cofactCoeffs=Table[Symbol["COFACTCOEFF"<>ToString[i]],{i,1,Length[cofactBasis]}];

template=coeffs.monbas;
cofactTemplate=cofactCoeffs.cofactBasis;
LieD[p_]:=Grad[p,vars].vf;

(* Building a basis vector from given polynomial *)
newMonbas= MonBas[(r+d-1)];
newBasisVect=Map[CoefficientRules[#, vars, "Lexicographic"][[1]][[1]]&, newMonbas];
PolyBasis[p_]:=Replace[(newBasisVect/.CoefficientRules[p, vars, "Lexicographic"]),{__Integer}:> 0, {1}];
(* Build formal Lie derivative computation matrix *)
MD=(Map[PolyBasis,Map[LieD, monbas]])//Transpose;
(* Building the multiplication by cofactor matrix *)
LT=(Map[PolyBasis,cofactTemplate*monbas])//Transpose;
choices=Flatten[MD]//DeleteDuplicates;
evaluations=Map[Thread[cofactCoeffs ->#]&,Tuples[choices,Length[cofactCoeffs]]];
minrk=Infinity;
minInstance={};
Do[
rk=MatrixRank[(MD-LT)/.eval];
If[rk<minrk, minrk=rk; minInstance=eval],
{eval,evaluations}];
cofactor=cofactTemplate/.minInstance;
nullspace=NullSpace[(MD-LT)/.minInstance];
Throw[{cofactor, cofactor*(nullspace.monbas)}];

]]


End[]
EndPackage[]
