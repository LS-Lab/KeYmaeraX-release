(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]


BeginPackage["DarbouxPolynomials`"];


(*
	Version 1.1, with minor optimisations
	TODO: Add support for using the domains to all the methods
*)
DbxNaive::usage=
"DbxNaive[{vectorField_List,vars_List,domain}, degree_Integer?NonNegative] 
A naive implementation for generating Darboux polynomials for the polynomial vector field, up to a given finite poylnomial degree.";

ManPS1::usage=
"ManPS1[{vectorField_List,vars_List,domain}, degree_Integer?NonNegative]
An implementation of Y.K. Man's algorithm for Darboux polynomial generation (up to given degree) for a polynomial vector field.
See algorithm ps_1 in Y.K. Man 'Computing Closed Form Solutions of First Order ODEs Using the Prelle-Singer Procedure', J. Symb. Comput., 1993.";

ManPS2::usage=
"ManPS2[{vectorField_List,vars_List,domain}, degree_Integer?NonNegative] 
An implementation of Y.K. Man's algorithm for Darboux polynomial generation (up to given degree) for a polynomial vector field.
See alorithm new_ps_1 in Y.K. Man 'Computing Closed Form Solutions of First Order ODEs Using the Prelle-Singer Procedure', J. Symb. Comput., 1993.";

DbxDefault::usage="DbxDefault[{vf,vars,domain},degree] Adds some bells and whistles to cleanup ManPS2,
e.g. turns complex (or irrational) results into real ones";


Begin["`Private`"];


DbxDefault[{vf_List,vars_List,domain_}, deg_Integer]:=Module[{dbx,realdbx,ratdbx,irratdbx,irratsq},
dbx=DarbouxPolynomials`ManPS2[{vf,vars,domain}, deg];
(* Hack: Set all remaining parameters to 1 *)
dbx=Map[Primitives`InstantiateParameters[#,vars,1]&,dbx];
(* deduplicated and noncomplexified polynomials*)
realdbx=Map[If[Primitives`IsRealPolynomial[#], #, #*Primitives`ConjugatePolynomial[#]//Expand]&, dbx]//DeleteDuplicates;
ratdbx=Select[realdbx,Primitives`IsRatPolynomial];
irratdbx=Select[realdbx,Not[Primitives`IsRatPolynomial[#]]&];
irratsq=Select[Map[Expand[#[[1]]*#[[2]]]&,Tuples[{irratdbx,irratdbx}]]//DeleteDuplicates,Primitives`IsRatPolynomial];
Join[ratdbx,irratsq]//DeleteDuplicates
]


DbxNaive[{vf_List,vars_List,domain_}, degree_Integer?NonNegative]:=Catch[Module[
{monbas, coeffs, template, MonBas, cofactCoeffs, 
cofactBasis, cofactTemplate, Lftemplate, Lfdeg, lhs ,sol,
 problem, monomialOrder,
(* Maximum total polynomial degree of the vector field *)
m=Max[Map[Primitives`PolynomDegree[#,vars]&,vf]]},

If[degree<=0, Throw[{}]];

(* Compute monomial basis with given monomial order *)
monomialOrder="DegreeReverseLexicographic";
MonBas[maxdeg_]:=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^maxdeg , vars, monomialOrder]];
monbas=MonBas[degree];

(* Compute the symbolic coefficients of the polynomial template *)
coeffs=Table[Symbol["COEFF"<>ToString[i]],{i,1,Length[monbas]}];
template=coeffs.monbas;

(* Lie derivative of template *)
Lftemplate=Primitives`Lf[template,vf,vars];
Lfdeg = Primitives`PolynomDegree[Lftemplate,vars];

(* Set maximum degree of the cofactor template to be at most m-1 *)
cofactBasis=MonBas[m-1];
cofactCoeffs=Table[Symbol["COFACTCOEFF"<>ToString[i]],{i,1,Length[cofactBasis]}];
cofactTemplate=cofactCoeffs.cofactBasis;

(* Equate coefficients of Lf(p)-q*p to zero and solve the nonlinear system over Complexes *)
problem=Map[#==0&,DeleteDuplicates@(#[[2]]&/@CoefficientRules[Lftemplate - cofactTemplate*template,vars])];
sol=Solve[problem, Join[cofactCoeffs,coeffs], Complexes];
Throw[Select[ (* Cleanup: return only non-numeric factors, without any duplicates *)
   Map[FactorList, 
    ((Map[Grad[#,coeffs]&,(template/.sol)])//Flatten//DeleteDuplicates)
    ]//Flatten//DeleteDuplicates,
 Not[NumericQ[#]]&]];
]]


(* Man PS implementation *)


MonicTemplatesAlt[deg_,vars_List]:=Catch[Module[
{MonBas,monbas,moncoeffs,monictemplate,monomialOrder},
(* Fix monomial order *)
monomialOrder="DegreeReverseLexicographic";
MonBas[maxdeg_]:=MonBas[maxdeg]=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^maxdeg , vars, monomialOrder]];
monbas=MonBas[deg];
Throw[Most[UpperTriangularize[Table[If[i==j,1,Symbol["\[Alpha]"<>ToString[j]]],{i,Length[monbas]},{j,Length[monbas]}]]].monbas];
]]


ManPS1[{vf_List,vars_List,domain_}, deg_Integer?NonNegative]:=Catch[Module[
{monicTemplates,Sfg,k, Dfi, monomialOrder,
LT,LC, MonBas, ltfi,ltDfi,n, cofactBasis, 
cofactCoeffs,gi,eqns,geqns,feqns,geqnsol,feqnsol},
k=1;
(* Final solution set is initially empty *)
Sfg={};
While[k<=deg,
(* Step 1 - construct all monic templates up to given degree *)
monicTemplates=MonicTemplatesAlt[k,vars];
monomialOrder="DegreeReverseLexicographic";
MonBas[maxdeg_]:=MonBas[maxdeg]=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^maxdeg , vars, monomialOrder]];

(* Leading Term computation *)
LT[p_]:=LT[p]=FromCoefficientRules[{CoefficientRules[p,vars, monomialOrder][[1]]}, vars];
(* Leading Coefficient computation *)
LC[p_]:=LC[p]=(CoefficientRules[p,vars, monomialOrder][[1]])/.Rule[exp_,coeff_]:>coeff;(* Lie derivative of template *)

(* Step 2 - main procedure foreach loop *)
Do[
Dfi=Primitives`Lf[fi,vf,vars]; (* Compute the derivative of the template *)
ltfi=LT[fi];
ltDfi=LT[Dfi];
(* If LT(fi) divides LT(D(fi)) *)
If[TrueQ[PolynomialReduce[ltDfi,ltfi,vars][[2]]==0], 
n= Primitives`PolynomDegree[Dfi,vars]-Primitives`PolynomDegree[fi,vars];
If[n<0, n=0];

(* Create a parametric cofactor of degree n *)
cofactBasis=MonBas[n];
cofactCoeffs=Table[Symbol["\[Beta]"<>ToString[i]],{i,1,Length[cofactBasis]}];
gi=cofactCoeffs.cofactBasis;
(* Bring everything in Lfp = q*p to the right hand side and collect the coefficients *)eqns=DeleteDuplicates@(#[[2]]&/@CoefficientRules[gi*fi -Dfi,vars]);(* Collect coefficients of those monomial terms that are generated by LT(p)*q *)geqns= (CoefficientRules[(ltfi*gi),vars]/.{Rule[exp_,coeff_]:>exp})/.CoefficientRules[Expand[gi*fi -Dfi],vars];(* Separate the above coefficients from the rest *)
feqns=Complement[eqns,geqns];
(* Solve in terms of parametric coefficients of p *)
geqnsol=Solve[Map[#==0&,geqns],cofactCoeffs, Complexes];
(* Update the other coeffients with this solution *)
feqns=(feqns/.geqnsol)//Flatten;
feqnsol=Solve[Map[#==0&,feqns],Complement[Variables[feqns],vars], Complexes];
If[Length[feqnsol]>0,Sfg=Join[Sfg, Select[fi/.feqnsol, IrreduciblePolynomialQ[#,Extension->All]&]]];
],{fi, monicTemplates}];
k=k+1;
];
Throw[Sfg//DeleteDuplicates];
]]


(* Implementation of new_ps_1 algorithm from Y.K. Man's 1993 JSC paper *)
ManPS2[{vf_List,vars_List,domain_}, deg_Integer]:=Catch[Module[
{monbas, moncoeffs, monictemplate, LieD, MonBas, cofactCoeffs, cofactBasis, 
cofactTemplate, Lftemplate, Lfdeg, lhs ,sol, problem, LT, LC, n, gi, indivisible, 
eqns,feqns,geqns, elimvar, s, geqnsol,feqnsol,Sfg,irreducibles,monomialOrder,k,monicTemplates},
If[deg<=0, Throw[{}]];
(* Fix monomial order *)
monomialOrder="DegreeReverseLexicographic";
(* Final solution set is initially empty *)
Sfg={};
(* Leading Term computation *)
LT[p_]:=LT[p]=FromCoefficientRules[{CoefficientRules[p,vars, "DegreeReverseLexicographic"][[1]]}, vars];
(* Leading Coefficient computation *)
LC[p_]:=LC[p]=(CoefficientRules[p,vars, monomialOrder][[1]])/.Rule[exp_,coeff_]:>coeff;

(* Compute monomial basis in lexicographic order *)
MonBas[maxdeg_]:=MonBas[maxdeg]=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^maxdeg , vars, monomialOrder]];
monbas=MonBas[1];
k=1;

While[k<=deg,
(* Step 1 - construct all monic templates up to given degree *)
monicTemplates=MonicTemplatesAlt[k,vars];
Do[
(* Compute Lie deriovative of the monic template *)
Lftemplate=Primitives`Lf[monictemplate,vf,vars];

gi=0;
indivisible=False;
feqns={};
While[ TrueQ[Not[indivisible] && Not[TrueQ[Expand[Lftemplate]==0]]],
Which[
(* If LT(p) divides LT(D(p)) *)
TrueQ[PolynomialReduce[LT[Lftemplate],LT[monictemplate],vars][[2]]==0], 
(* Then *)
gi = gi + (LT[Lftemplate]/LT[monictemplate]);
Lftemplate = Expand[Lftemplate - monictemplate*(LT[Lftemplate]/LT[monictemplate])],
(* Else, if LC(D(p)) - the leading COEFFICIENT of D(p) - is a constant *)
NumericQ[LC[Lftemplate]],
(* Then *)
indivisible=True,
(* Else if LC(D(p)) contains ONLY ONE parameter of p, which is a VARIABLE of the monic template *)
TrueQ[Length[Variables[LC[Lftemplate]]==1] && SubsetQ[Variables[LC[Lftemplate]],vars]],
(* Then *)
elimvar=Variables[LC[Lftemplate]];
s=Solve[LC[Lftemplate]==0,elimvar,Complexes];
monictemplate=monictemplate/.s;
gi=gi/.s;
feqns=feqns/.s, 
(* Anything else *)
True, 
(* Then *)
feqns=Join[feqns,{LC[Lftemplate]}];
Lftemplate = Lftemplate-LT[Lftemplate]
] (* End Which *) 
]; (* End While *)

If[TrueQ[Not[indivisible] && Length[feqns]>0], 
feqnsol=Solve[Map[#==0&,feqns], Complement[Variables[feqns],vars], Complexes];
];

If[Length[feqnsol]>0, 
If[TrueQ[Not[indivisible] ],
irreducibles=Select[monictemplate/.feqnsol, IrreduciblePolynomialQ[#,Extension->All]&];
Sfg=Join[Sfg,irreducibles];
 ]
]
, {monictemplate, monicTemplates}];
k=k+1;
];

Throw[Sfg//DeleteDuplicates];
]]


End[]
EndPackage[]
