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


FindFirstIntegralsAlt::usage="
FindFirstIntegralsAlt[deg_Integer?NonNegative, vars_List, vectorField_List] 
Alternative implementation relying on Solve"


FindDbx::usage="
FindDbx[deg_Integer?NonNegative, vars_List, vectorField_List] 
Darboux polynomial search based on Solve"
FindDbxBoreale::usage="
FindDbx[deg_Integer?NonNegative, vars_List, vectorField_List] 
Darboux polynomial search based on Solve"


FindFirstIntegralsPDE::usage="
FindFirstIntegralsPDE[vars_List, vectorField_List] 
computes a list of POTENTIALLY NON-POLYNOMIAL first integrals in the variables 'vars'
for the system of ODEs described by vectorField. The variable order MATTERS, e.g. if vars={x,y} and
vectorField={x^2+1, x+y-2}, this is interpreted as the system of ODEs x'=x^2+1,
y'=x+y-2. Changing the order of variables or entries in vectorField will
generally result in different systems of ODEs."


FuncIndep::usage="
FuncIndep[polynomials_List, vars_List] 
Returns a list of functionally independent polynomials from a given list."
GenMonomialBasis::usage="Generate a monomial basis"


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


FuncIndep[polys_List, vars_List]:=Module[{},
If[Length[polys]>0,
sortedlist=Sort[polys,And[MaxPolyDegree[#1,vars]<=MaxPolyDegree[#2,vars], Length[#1]<=Length[#2]]&];
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
FIs=Map[Apply[Plus,Times[MonBas,#]]&,NullSpace[MD]];
(* Return  non-constant first integrals *)
Rest[FIs]
]


(* Alternative polynomial first integral generation method using the solver - inspired by Kong & Boreale *)
FindFirstIntegralsAlt[deg_Integer?NonNegative,vars_List,vectorField_List]:=Module[{
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vectorField]]},
(* Compute the monomial basis *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasis[vars,r]],vars]];
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
]


(* Alternative polynomial first integral generation method using the solver - inspired by Kong & Boreale *)
FindDbxBoreale[deg_Integer?NonNegative,vars_List,vectorField_List]:=Module[{
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vectorField]]},
(* Compute the monomial basis *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasis[vars,r]],vars]];
(* Create a template polynomial with symbolic coefficients *)
TemplateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[MonBas]}];
DbxTemplate=Evaluate[TemplateCoeffs.MonBas];
(* Compute the Lie derivatives of the monomial basis *)
LieDTemplate=Expand[Grad[DbxTemplate,vars].vectorField];
(* Equate the template derivative coefficients to zero and solve a system of linear equations *)
rem=PolynomialReduce[LieDTemplate,{DbxTemplate},Union[TemplateCoeffs, vars]]//Last;
(* Solve for zero remainder *)
problem=Map[#==0&,DeleteDuplicates[Flatten[CoefficientList[rem,vars]]]];
sol=Solve[problem, TemplateCoeffs];
(* Use the solutions to create instances of the original template *)
Dbxs=(DbxTemplate/.sol);
(* Filter out the first integrals *)
Select[DeleteDuplicates[Grad[Dbxs, TemplateCoeffs]//Flatten], Not[NumericQ[#]]&] 
]


(* Implementation of an (incomplete) Darboux polynomial generation method due to Kong et al., HSCC 2017*)
FindDbx[deg_Integer?NonNegative,vars_List,vectorField_List]:=Module[{
(* Maximum total polynomial degree of the first integral being sought *)
r=deg, 
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vectorField]]},
(* Compute the monomial basis in Degree Reverse Lexicographic Order *)
MonBas=MonomialList[FromCoefficientRules[Map[Rule[#,1]&,GenMonomialBasis[vars,r]],vars], "DegreeReverseLexicographic"];
(* Create symbolic coefficients for the monomial basis *)
Coeffs=Table[Symbol["coeff"<>ToString[i]], {i, 1, Length[MonBas]}];
(* Create a symbolic polynomial template *)
PTemp = Coeffs.MonBas;
(* Compute the Lie derivative of the polynomial template along the trajectories *)
LfPTemp = Grad[PTemp, vars].vectorField;
(* Compute the Leading Terms of the template and the Lie derivative wrt the same monomial ordering *)
LTPTemp = Coeffs[[1]]*MonBas[[1]];
LTLfPTemp = FromCoefficientRules[{CoefficientRules[LfPTemp,vars, "DegreeReverseLexicographic"][[1]]}, vars];
(* Compute the remainder coefficients wrt to the monomial ordering *)
remcoeffs = CoefficientRules[LfPTemp-(LTLfPTemp/LTPTemp)*PTemp, vars,  "DegreeReverseLexicographic"];
(* Create a system of equalities *)
syst = Map[#/.Rule[_,coeff_]:>coeff==0&, remcoeffs];
(* Compute a parametric solution *)
parametricSol=Solve[syst, Coeffs];
(* Eliminate symbolic coefficients *)
Dbxs=(PTemp/.parametricSol);
(* Filter out the first integrals *)
Select[DeleteDuplicates[Grad[Dbxs, Coeffs]//Flatten], Not[NumericQ[#]]&]
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
