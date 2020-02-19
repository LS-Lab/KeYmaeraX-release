(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"Primitives","DarbouxPolynomials.m"}]]
(*
   Description:
	Implementation of a procedure for generating polynomial and rational 
	first integrals for autonomous (i.e. time-independent) systems of polynomial ODEs.

   Comments: Tested in Mathematica 12.0   
   
   *)


BeginPackage[ "FirstIntegrals`"];

FindFirstIntegrals::usage="
FindFirstIntegral[deg_Integer?NonNegative, vars_List, vectorField_List] 
computes a list of POLYNOMIAL first integrals (up to some given maximum
polynomial total degree in the variables 'vars') for the system of ODEs
described by vectorField using the basic method of undetermined coefficients. 
The variable order MATTERS, e.g. if vars={x,y} and vectorField={x^2+1, x+y-2}, 
this is interpreted as the system of ODEs x'=x^2+1, y'=x+y-2. 
Changing the order of variables or entries in vectorField will
generally result in different systems of ODEs.";

FindRationalFirstIntegrals::usage="
FindRationalFirstIntegrals[deg_Integer?NonNegative, vars_List, vectorField_List] 
computes a list of RATIONAL first integrals (up to some given maximum
polynomial total degree in the variables 'vars') for the system of ODEs
described by vectorField. This implementation relies on computing Darboux polynomials.";

FindLinSysIntegrals::usage="
FindLinSysIntegrals[vars_List, vectorField_List] 
computes a list of first integrals (which may be rational functions) for the system of LINEAR ODEs
described by vectorField.";

GenMonomialBasis::usage="Generate a monomial basis";

Begin[ "Private`" ];


(* Computing the monomial basis for polynomials of maximal total degree maxdeg *)
GenMonomialBasis[vars_List,maxdeg_Integer?NonNegative]:=Module[{monomialOrder="DegreeReverseLexicographic"},
Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^maxdeg , vars, monomialOrder]]
]


(*internally used*)
GenMonomialBasisCoeffs[vars_List,maxdeg_Integer?NonNegative]:=Module[{},
Select[Permutations[Flatten[Table[Table[j,{i,1,Length[vars]}],{j,0,maxdeg}]],{Length[vars]}], Apply[Plus, #] <= maxdeg &]
]


FindFirstIntegrals[{vectorField_List,vars_List,domain_},deg_Integer?NonNegative]:=Module[
{MonBas,TemplateCoeffs,FITemplate,LieDTemplate,problem,sol,FIs,
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[Primitives`PolynomDegree,vectorField]]},
(* Compute the monomial basis *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasisCoeffs[vars,r]],vars]];
(* Create a template polynomial with symbolic coefficients *)
TemplateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[MonBas]}];
FITemplate=Evaluate[TemplateCoeffs.MonBas];
(* Compute the Lie derivatives of the monomial basis *)
LieDTemplate=Expand[Grad[FITemplate,vars].vectorField];
(* Equate the template derivative coefficients to zero and solve a system of linear equations *)
problem=Map[#==0&,DeleteDuplicates[Flatten[CoefficientList[LieDTemplate,vars]]]];
sol=Solve[problem, TemplateCoeffs];
(* Use the solutions to create instances of the original template *)
FIs=(FITemplate/.sol);
(* Filter out the first integrals *)
Select[DeleteDuplicates[Grad[FIs, TemplateCoeffs]//Flatten], Not[NumericQ[#]]&] 
(*DeleteDuplicates[Map[CoefficientRules[#,TemplateCoeffs][[All,2]]&,FIs]]*)
]


(* Compute cofactors of Darboux polynomials *)
(* Requires: dbxList is a list of genuine Darboux polynomials *)
DbxCofactors[dbxList_List,vf_List,vars_List]:=Catch[Module[{},
Map[First@@PolynomialReduce[(Grad[#,vars].vf),{#},vars]&, dbxList]
]
]


(* Generate rational first integrals from a list of independent Darboux polynomials *)
RatFIGen[dbxList_List, cofactors_List,vars_List]:=Catch[
If[TrueQ[Length[cofactors]!=Length[dbxList]], 
Print["Number of cofactors does not match the number of Darboux polynomials."];
Throw[{}]];
Module[{
lambdas=Table[Symbol["lambda"<>ToString[i]],{i, Length[dbxList]}],
notAllLambdaZero,coeffConstraints,sol, exponents
},
(* Constraints: 
i) not all lambdas are 0, and 
 ii) Subscript[cofact, 1]*Subscript[lambda, 1] + ... + Subscript[cofact, k]*Subscript[lambda, k] = 0 
*)
notAllLambdaZero=Or@@Map[#!=0&,lambdas];
coeffConstraints=And@@CoefficientRules[lambdas.cofactors,vars]/.{Rule[mon_List,coeff_]:> coeff==0};
(* Solve for lambdas over the integers; seek at most n-1 solutions *)
sol=FindInstance[coeffConstraints&& notAllLambdaZero, lambdas, Integers,Length[vars]-1];
(* Bring the solution to normal form and remove redundancies *)
exponents=DeleteDuplicatesBy[Map[(lambdas/.sol[[#]])/GCD[Sequence@@(lambdas/.sol[[#]])]&, Range[Length[sol]]],
(* This deletes vectors that differ by sign *) 
Function[vec,If[First[vec]<0, -vec, vec]]];
(* Construct first integrals by raising the Darboux polynomials to the resulting exponents and taking their product*)
Map[Apply[Times, #]&,Map[Thread[dbxList ^ #]&,exponents]]
]
]


FindRationalFirstIntegrals[{vectorField_List,vars_List,domain_},deg_Integer?NonNegative]:=Catch[
Module[{dbx,cofactors},
(* TODO: currently we discard Darboux polynomials with complex coefficients.
This is a limitation because they always come in conjugate pairs and can be used to construct a real first integral. *)
dbx=Select[DarbouxPolynomials`ManPS2[{vectorField,vars,domain},deg], FreeQ[#,_Complex]&];
dbx=Map[Primitives`InstantiateParameters[#,vars,1]&,dbx];
(* Forget about first integrals *)
dbx=Select[dbx, Not[TrueQ[Simplify[Grad[#,vars].vectorField]==0]] &];
(* If there are no real Darboux polynomials, return the empty list *)
If[TrueQ[Length[dbx]<1], Throw[{}]];
cofactors=DbxCofactors[dbx,vectorField,vars];
Throw[RatFIGen[dbx,cofactors,vars]];
]]


(* Implementation of a first integral generation method based on solving PDEs - these may not be defined everywhere
and can feature transcendental functions *)
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


(* LINEAR SYSTEMS SECTION *)


LinearlyIndependentQ[vectors_List]:=Module[{},
TrueQ[MatrixRank[vectors]==Length[vectors]]
]


(* Given a list of numbers, return a set of all distinct pairs of non-zero numbers *)
DistinctNonZeroPairs[numbers_List]:=Module[{nz},
Select[(Sort/@Tuples[Select[numbers, TrueQ[#!=0]&],2]//DeleteDuplicates),
Length[DeleteDuplicates[#]]!=1&]
]


(* Return a list of rules of the form eigenvalue \[Rule] {eigenvectors associated with eigenvalue} *)
EigenRules[A_]:=Module[{lambdas,vectors},
{lambdas, vectors}=Eigensystem[A]; 
Map[Rule @@#&,Map[Function[lambda, {lambdas[[lambda]]//First, vectors[[lambda]]} ],
(* N.B. the use of //N below is important! Extracting positions of non-numeric entries is quirky in Mathematica *)
Map[(Position[lambdas//N,#//N]//Flatten)&,lambdas]//DeleteDuplicates]]
]


(* Easy case: eigenvectors of A^T with eigenvalue 0 determine linear first integrals *)
ZeroEigenvalueFIs[vf_List,vars_List]:=Module[{A},
A=Grad[vf,vars];
Map[#[[2]].vars &
,Select[Transpose[Eigensystem[Transpose[A]]], First[#]==0&]]
]


(* Less trivial case: linearly independent eigenvectors corresponding to the same non-zero real eigenvalue *)
NonZeroEigenvalueFIs[vf_List,vars_List]:=Catch[Module[{A,eigensystem, nonZeroDistinctEigenvals, EigenvecPairs,FIs},
A=Grad[vf,vars];
eigensystem=Eigensystem[Transpose[A]];
(* N.B. we need real eigenvalues *)
nonZeroDistinctEigenvals=Select[DeleteDuplicates[eigensystem[[1]]],TrueQ[ #!=0 && Im[#]==0]&];
EigenvecPairs[eig_]:=Select[Tuples[(#[[2]]&/@Select[Transpose[eigensystem], #[[1]]==eig&]),2], LinearlyIndependentQ[#]&];
FIs=Map[Function[vecpair,If[UnsameQ[vecpair,{}],vecpair[[1]].vars/vecpair[[2]].vars ]],
Sort/@(Replace[
Map[EigenvecPairs, nonZeroDistinctEigenvals] 
,x_List:>DeleteCases[x,{}],{0,Infinity}]//.{x_List}:>x)//DeleteDuplicates
];
Select[FIs//Flatten, UnsameQ[#, Null]&]
]]


(* FIs constructed from eigenvectors corresponding to distinct non-zero real eigenvalues *)
DistinctEigenvalueFIs[vf_List,vars_List]:=Catch[Module[{A,eigenSystem,nzDistinctEigenvals,FIs,eigenvalPairs,eigenRules},
A=Grad[vf,vars];
eigenRules=EigenRules[A//Transpose];
eigenSystem=Eigensystem[A//Transpose];
(* N.B. we need real eigenvalues *)
nzDistinctEigenvals=Select[DeleteDuplicates[eigenSystem[[1]]],TrueQ[#!=0 && Im[#]==0]&];
eigenvalPairs=Select[Sort/@Tuples[nzDistinctEigenvals,2]//DeleteDuplicates, Length[DeleteDuplicates[#]]!=1&];
FIs[nzpair_List]:=nzpair/.{
{l1_/;NumericQ[l1],l2_/;NumericQ[l2]}:>
Map[Apply[Times, #]&,Tuples[{(#.vars)^(-l2)&/@(l1/.eigenRules), (#.vars)^(l1)&/@(l2/.eigenRules)}]]
};
Throw[Map[FIs,eigenvalPairs]];
]]


FindLinSysIntegrals[{vectorField_List,vars_List,domain_}]:=Module[{},
(* Compute some first integrals, combine them and return the result,
 following the method described by Gorbuzov & Pranevich in FIRST INTEGRALS OF ORDINARY LINEAR DIFFERENTIAL SYSTEMS *)
{ZeroEigenvalueFIs[vectorField, vars],
NonZeroEigenvalueFIs[vectorField,vars],
DistinctEigenvalueFIs[vectorField, vars]}//Flatten//DeleteDuplicates
]


End[]


EndPackage[]
