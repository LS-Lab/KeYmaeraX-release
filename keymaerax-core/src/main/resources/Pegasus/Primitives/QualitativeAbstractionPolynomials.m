(* ::Package:: *)

Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"DarbouxPolynomials.m"}]] (* Load algorithms for Darboux polynomial generation from current directory *)
Needs["Primitives`",FileNameJoin[{ParentDirectory[],"Primitives.m"}]] (* Load primitives package *)


(* ::Input:: *)
(*(* Polynomial generation for qualitative analysis *)*)


BeginPackage["QualitativeAbstraction`"];


PolyProductFactors::usage="PolyProductFactors[list]"
QualitativePolys::usage="QualitativePolys[problem]"
PostRHSFactors::usage="PostRHSFactors[problem] Generate irreducible factors of the right-hand side and the post-condition."
PostRHSLieDFactors::usage="PostRHSLieDFactors[problem] Generate irreducible factors of the right-hand side and the post-condition, and their Lie derivatives."
PostRHSLieDProductFactors::usage="PostRHSFactors[problem] Generate irreducible factors of the right-hand side and the post-condition."
PostRHSLieNFactors::usage="PostRHSFactors[problem] Generate irreducible factors of the right-hand side and the post-condition."
PostRHSProductFactors::usage="PostRHSLieDFactors[problem] Generate irreducible factors of the right-hand side and the post-condition, and their Lie derivatives."
DarbouxPolynomials::usage="DarbouxPolynomials[problem]"
SummandFactors::usage="SummandFactors[problem]"


Begin["`Private`"]


SF[p_]:=Module[{},
Apply[Times,Map[Function[x,First[x]],FactorSquareFreeList[p]]]
]


ExtractFactors[polynomials_List]:=Module[{},
Cases[DeleteDuplicates[Flatten[Map[FactorList[#, Extension->Automatic]&, polynomials]]], Except[_?NumericQ]]
]


ExtractPolynomials[semialg_]:=Module[{predicates=Flatten[{DNFNormalizeLtLeq[semialg]}/.{And->List,Or->List}]},
DeleteDuplicates[predicates/.{Less[p_,0]:> p, LessEqual[p_,0]:> p, Equal[p_,0]:> p}]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
PostRHSFactors[problem_List]:=Module[{precond, f,vars,Q, postcond},
(* Pattern match problem input *)
{precond,{f,vars,Q},postcond} = problem;
DeleteDuplicates[
	Union[
		ExtractFactors[{f}],  (* Use FACTORS of polynomials from the RHS of ODE *)
		ExtractFactors[ExtractPolynomials[postcond]]
	]
]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
QualitativePolys[problem_List]:=Module[{precond, f,vars,Q, postcond},
(* Pattern match problem input *)
{precond,{f,vars,Q},postcond} = problem;
ExtractFactors[{Div[f,vars]}]
]


(* Generate a list of Lie Derivatives of all the polynomials in the list *)
LieDFactors[polynomials_List, f_List, vars_List]:=Module[{result},
result=Union[Map[Primitives`Lf[#,f,vars]&,polynomials],polynomials]//DeleteDuplicates;
Select[Expand[result],Not[IntegerQ[#]]&]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
PostRHSLieNFactors[problem_List, n_Integer]:=Module[{precond, f,vars,Q, postcond},
(* Pattern match problem input *)
{precond,{f,vars,Q},postcond} = problem;
LieDFactors[PostRHSProductFactors[problem], f, vars]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
PostRHSLieDFactors[problem_List]:=Module[{},
PostRHSLieNFactors[problem, 1]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
PostRHSLieDProductFactors[problem_List]:=Module[{precond, f,vars,Q, postcond},
(* Pattern match problem input *)
{precond,{f,vars,Q},postcond} = problem;
PolyProductFactors[LieDFactors[PostRHSFactors[problem], f, vars]]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
PolyProductFactors[polynomials_List]:=Module[{},
ExtractFactors[{Apply[Times, polynomials]}]
]


(* Generate a list of polynomials A with linear factors of the RHS of the ODE and the polynomials describing the postcondition *)
PostRHSProductFactors[problem_List]:=Module[{precond, f,vars,Q, postcond},
(* Pattern match problem input *)
{precond,{f,vars,Q},postcond} = problem;
PolyProductFactors[PostRHSFactors[problem]]
]


ConjugatePolynomial[poly_]:=Module[{vars=Variables[poly]},
FromCoefficientRules[CoefficientRules[poly,vars]/.{Rule[a_,b_]:>Rule[a,Conjugate[b]]},vars]
]


IsRealPolynomial[poly_]:=Module[{vars=Variables[poly]},
AllTrue[Flatten[CoefficientList[poly,vars]], PossibleZeroQ[Im[#]]&]
]


IsConcretePolynomial[poly_,vars_]:=Module[{pvars=Variables[poly]},
  SubsetQ[vars,pvars]
]


DarbouxPolynomials[problem_List,time_Integer,maxdeg_Integer]:=Catch[Module[{pre,f,vars,Q,post,deg,dbx,realdbx,i},
{pre,{f,vars,Q},post}=problem;

dbx={};
TimeConstrained[For[i=1,i<=maxdeg,i++,
  dbx=Union[dbx,DarbouxPolynomials`ManPS2[i,f,vars]]],time];
(* Currently unable to take advantage of parametric Darboux polynomials *)
dbx=Select[dbx,IsConcretePolynomial[#,vars]&];
Print["Generated Darboux polynomials: ",dbx];
(* Darboux polynomials come in complex conjugate pairs - we multiply with the conjugates to eliminate complex coefficients *)
realdbx=Map[If[IsRealPolynomial[#], #, #*ConjugatePolynomial[#]//Expand]&, dbx]//DeleteDuplicates;
Throw[realdbx]
]]


(* Extracting square-free factors of summands in the rhs *)
SummandFactors[problem_List]:=Module[{pre,f,vars,Q,post},
{pre,{f,vars,Q},post}=problem;
Select[Map[FactorSquareFreeList,
If[Head[#]===Plus, Apply[List,#],#]&/@f//Flatten//Expand]//Flatten, 
Not[NumericQ[#]]&]
]


End[]
EndPackage[]
