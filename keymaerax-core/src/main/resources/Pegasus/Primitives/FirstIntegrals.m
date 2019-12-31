(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
(*
   Description:
	Implementation of a procedure for generating polynomial first integrals for
	autonomous (i.e. time-independent) systems of polynomial ODEs.

   Comments: Tested in Mathematica 10.0   *)


BeginPackage[ "FirstIntegrals`"];

FindFirstIntegrals::usage="
FindFirstIntegrals[{vectorField_List,vars_List,domain},deg_Integer?NonNegative] 
Uses the method of undetermined coefficients relying on Solve";

FindFirstIntegralsMatringe::usage="
FindFirstIntegrals[{vectorField_List,vars_List,domain},deg_Integer?NonNegative] 
computes a list of polynomial first integrals (up to some given maximum
polynomial total degree in the variables 'vars') for the system of ODEs
described by vectorField. The variable order MATTERS, e.g. if vars={x,y} and
vectorField={x^2+1, x+y-2}, this is interpreted as the system of ODEs x'=x^2+1,
y'=x+y-2. Changing the order of variables or entries in vectorField will
generally result in different systems of ODEs.";

FindFirstIntegralsPDE::usage="
FindFirstIntegralsPDE[{vectorField_List,vars_List,domain}] 
computes a list of POTENTIALLY NON-POLYNOMIAL first integrals in the variables 'vars'
for the system of ODEs described by vectorField. The variable order MATTERS, e.g. if vars={x,y} and
vectorField={x^2+1, x+y-2}, this is interpreted as the system of ODEs x'=x^2+1,
y'=x+y-2. Changing the order of variables or entries in vectorField will
generally result in different systems of ODEs.";

FuncIndep::usage="
FuncIndep[polynomials_List, vars_List] 
Returns a list of functionally independent polynomials from a given list.";

GenMonomialBasis::usage="Generate a monomial basis";

Begin[ "Private`" ];


(* Computing the monomial basis for polynomials of maximal total degree maxdeg *)
GenMonomialBasis[vars_List,maxdeg_Integer?NonNegative]:=Module[{},
Select[Permutations[Flatten[Table[Table[j,{i,1,Length[vars]}],{j,0,maxdeg}]],{Length[vars]}], Apply[Plus, #] <= maxdeg &]
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


(* Implementation of the Matringe-Moura-Rebiha polynomial first integral generation method *)
FindFirstIntegralsMatringe[{vectorField_List,vars_List,domain_},deg_Integer?NonNegative]:=Module[{MonBas,LieDMonBas,LieDMonBasCoeffs,NewBasisMat,MD,FIs,
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[Primitives`PolynomDegree,vectorField]]},
(* Compute the monomial basis *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasis[vars,r]],vars]];
(* Compute the Lie derivatives of the monomial basis *)
LieDMonBas=Map[Primitives`Lf[#,vectorField,vars]&, MonBas];
(* Compute the coefficient rules for each of the Lie derivatives of the monomial basis *)
LieDMonBasCoeffs=Map[CoefficientRules[#,vars]&, LieDMonBas];
(* Create a matrix of monomial basis elements for polynomials of degree r+d-1 as its row entries, with |MonBas| rows in total *)
NewBasisMat=Table[GenMonomialBasis[vars,r+d-1], {i,1,Length[MonBas]}];
(* For each row j, substitute the monomial coefficients of the Lie derivative of the j-th monomial element in MonBas; then transpose *)
MD=Transpose[Table[Map[If[ListQ[#],0,#]&,NewBasisMat[[j]]/.LieDMonBasCoeffs[[j]]], {j,1,Length[MonBas]}]];
(* Turn the null space vectors into polynomials in the monomial basis and return the result *)
FIs=Map[Apply[Plus,Times[MonBas,#]]&,NullSpace[MD]];
(* Return non-constant first integrals *)
Rest[FIs]
]


FindFirstIntegrals[{vectorField_List,vars_List,domain_},deg_Integer?NonNegative]:=Module[
{MonBas,TemplateCoeffs,FITemplate,LieDTemplate,problem,probsimp,sol,FIs,
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[Primitives`PolynomDegree,vectorField]]},
(* Compute the monomial basis *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasis[vars,r]],vars]];
(* Create a template polynomial with symbolic coefficients *)
TemplateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[MonBas]}];
FITemplate=Evaluate[TemplateCoeffs.MonBas];
(* Compute the Lie derivatives of the monomial basis *)
LieDTemplate=Assuming[domain,Simplify[Expand[Grad[FITemplate,vars].vectorField]]];
(* Equate the template derivative coefficients to zero and solve a system of linear equations *)
problem=Map[#==0&,DeleteDuplicates[Flatten[CoefficientList[LieDTemplate,vars]]]];
(* Simplify the problem using Mathematica's simplifier *)
probsimp=Assuming[domain,Simplify[problem]];
sol=Solve[probsimp, TemplateCoeffs,Reals];
(* Use the solutions to create instances of the original template *)
FIs=(FITemplate/.sol);
(* Filter out the first integrals *)
Select[DeleteDuplicates[Grad[FIs, TemplateCoeffs]//Flatten], Not[NumericQ[#]]&] 
(*DeleteDuplicates[Map[CoefficientRules[#,TemplateCoeffs][[All,2]]&,FIs]]*)
]


(* Implementation of a first integral generation method based on solving PDEs *)
FindFirstIntegralsPDE[{vectorField_List,vars_List,domain_}]:=Module[{FIC,PDE,OverReals,solution,integrals},
(* Set FIC to be the First Integral Candidate in the state variables *)
FIC=FICandidate[Apply[Sequence,vars]];
(* Formulate PDE problem: seeking function in the state variables, i.e. (\[PartialD]FIC/\[PartialD]x)*x' + (\[PartialD]FIC/\[PartialD]y)*y' + etc. = 0 *)
PDE=(Primitives`Lf[FIC,vectorField,vars]==0);
(* Reals assumption*)
OverReals=Apply[And, Map[#\[Element]Reals &, vars]];
(* Solve the PDE using methods available in Mathematica *)
solution=PowerExpand[Assuming[OverReals,DSolve[PDE,FIC,vars]]];
(* Extract first integrals from solutions, replacing functions C[1], C[2], etc. with Simplify *) 
integrals=(FIC/.solution)/.{C[_]->Simplify} 
]


End[]


EndPackage[]
