(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
(*
   Description:
	Implements the Rodriguez-Carbonell/Tiwari procedure for generating algebraic
	invariants for linear systems.
 *)


BeginPackage[ "LinearAlgebraicInvariants`"];

RatBasis::usage="RatBasis[v_List] returns a rational basis for v along with the transformation matrix so that\[IndentingNewLine]transmat . basisEigs = v\[IndentingNewLine]transmat is guaranteed to be an integer matrix \[IndentingNewLine]basisEigs is not guaranteed to be a true basis though (because of numerics)";

EigSolve::usage="EigSolve[A] Given a system matrix A, computes the expected algebraic relationships
returns a 3 tuple {rep, invs, vars} where rep maps the trigonometric functions into vars and inv defines
algebraic invariants over vars";

LinAlgInv::usage="LinAlgInv[prob] Generates a list of algebraic invariants for the given problem";

LinAlgInvNumeric::usage="LinAlgInv[prob] Generates algebraic invariants for the given problem using 
	numerical steps";

Begin[ "Private`" ];


RatBasis[v_List]:=Block[{vv,a,lra,lrared,rref,trref,delPos,basisPos,delEigs,preEigs,scale,
basisEigs,transmat, power, errbound,sortpos,sortedmat},
(* some potentially tunable params controlling the LatticeReduce computation *)
power=10^20;
errbound=10;
If[Length[v]==0,Return[{{},{}}]];
(* Find integral relationships *)
vv=Round[power v];
a=Join[IdentityMatrix[Length[v]],Transpose[{-vv}],2];
lra=LatticeReduce[a];
lrared=Map[Drop[#,-1]&,Select[lra,Abs[Last[#]]<=errbound&]];
(* RREF form: each row eliminates an eigenvalue in terms of the rest *)
If[Length[lrared]==0,Return[{IdentityMatrix[Length[v]],v}]];
(*Print["Lattice reduction:",lrared//MatrixForm];*)
rref=RowReduce[lrared];
trref=Transpose[rref];
(* Find the basis eigenvalues *)
delPos=Map[FirstPosition[#,_?(#==1&)]&,rref]//Flatten;
(* Strange degenerate case if errbound is too high *)
If[Length[delPos]==Length[v],delPos=Drop[delPos,-1]];
basisPos=Delete[Range[Length[v]],Partition[delPos,1]];
delEigs = v[[delPos]];
preEigs = v[[basisPos]];
(* Rescale the basis eigenvalues *)
scale=Map[Apply[LCM],Map[Denominator,trref[[basisPos]]]];
basisEigs=MapThread[#1/#2&,{preEigs,scale}];
(* Represent every initial eigenvalue in terms of the (rescaled) basis *)
transmat=Join[DiagonalMatrix[scale],Map[#*scale&,-rref[[All,basisPos]]]];
sortpos=Ordering[Join[basisPos,delPos]];
sortedmat=transmat[[sortpos]];
{sortedmat,basisEigs}];


FilterZero[eigs_List] :=Block[{},
Select[eigs,Not[Round[#,0.0000000001]===0]&]
]
MkExpRule[row_,eig_,uvars_,vvars_,tvar_] := Block[{rhs},
rhs=MapThread[If[#1>0,Power[#2,#1],Power[#3,-#1]]&,{row,uvars,vvars}];
DeleteDuplicates[{(Power[E,Times[eig,tvar]])->Apply[Times,rhs],
(Power[E,Times[eig,tvar]//Expand])->Apply[Times,rhs],
(Power[E,Times[eig,tvar]]//ComplexExpand)->Apply[Times,rhs]}]
];
MkTrigRule[row_,eig_,uvars_,vvars_,tvar_] := Block[{rhsPre},
rhsPre=Apply[Times,MapThread[If[#1>0,ComplexExpand[Power[#2+I #3,#1]],ComplexExpand[Power[#2-I #3,-#1]]]&,{row,uvars,vvars}]];
DeleteDuplicates[{(Cos[Times[eig,tvar]])-> ComplexExpand[Re[rhsPre]],
(Sin[Times[eig,tvar]])->ComplexExpand[Im[rhsPre]],(Cos[Times[eig,tvar]]//ComplexExpand)-> ComplexExpand[Re[rhsPre]],
(Sin[Times[eig,tvar]]//ComplexExpand)->ComplexExpand[Im[rhsPre]],(Cos[Times[eig,tvar]//Expand])-> ComplexExpand[Re[rhsPre]],
(Sin[Times[eig,tvar]//Expand])->ComplexExpand[Im[rhsPre]]}]
];

EigSolve[A_]:=Block[{eigs,realEigs,imEigs,tvar,ratConst,
realTrans,realBasis,us,vs,repReal,relReal,
imTrans,imBasis,ws,zs,repIm,relIm},
(* TODO: Pass as params *)
tvar=t;
ratConst=0.000000001;

eigs=Eigenvalues[A];
realEigs=Re[eigs] //FilterZero;
imEigs=Im[eigs] //FilterZero;
(*Print["Real part eigenvalues: ",realEigs];
Print["Imaginary part eigenvalues: ",imEigs];*)
(* Handle real part *)
{realTrans,realBasis} = RatBasis[realEigs];
us = Table[Unique["u"],{i,Length[realBasis]}];
vs = Table[Unique["v"],{i,Length[realBasis]}];
(*Print["Real basis:",realBasis];
Print["Real trans:",realTrans];*)
(* Real replacement rules*)
repReal=MapThread[MkExpRule[#1,#2,us,vs,tvar]&,{realTrans,realEigs}]//Flatten;
relReal = MapThread[#1*#2-1&,{us,vs}];
(* Handle imaginary part *)
{imTrans,imBasis} = RatBasis[imEigs];
ws = Table[Unique["w"],{i,Length[imBasis]}];
zs = Table[Unique["z"],{i,Length[imBasis]}];
(*Print["Imaginary basis:",imBasis];
Print["Imaginary trans:",imTrans];*)
(* Imaginary replacement rules*)
repIm=MapThread[MkTrigRule[#1,#2,ws,zs,tvar]&,{imTrans,imEigs}]//Flatten;
relIm=MapThread[#1^2+#2^2-1&,{ws,zs}];
{Join[repReal,repIm],Join[relReal,relIm],Join[us,vs,ws,zs]}
];


(*
  The following should work correctly when the eigenvalues are rational
 but is a naive approximation when they aren't
 
EigSolve[A_]:=Block[{eigs,realRatEigs,imRatEigs,realEigs,imEigs,p,q,rep1,rep2,
uvar,vvar,wvar,zvar,ratrel,us,vs,ws,zs,irratrel,repu,repv,repw,repz,
replacements,repvars},
eigs = Eigenvalues[A]//Expand;
Print["Eigenvalues: ",eigs];

(* Handle rational eigenvalues *)
realRatEigs =Select[DeleteDuplicates[Re[eigs]],#\[NotEqual]0&] //Select[RationalQ]//Expand;
imRatEigs = Select[DeleteDuplicates[Im[eigs]],#\[NotEqual]0&] //Select[RationalQ]//Expand;
(*Print["Real rational eigenvalue parts: ",realRatEigs];
Print["Imaginary rational eigenvalue parts: ",imRatEigs];*)
p=1/Times@@Denominator[realRatEigs//Abs//DeleteDuplicates];
q=1/Times@@Denominator[imRatEigs//Abs//DeleteDuplicates];
Print["p: ",p," q: ",q];
(* Replacement rule for exponentials
	u = e^{pt}, v = e^{-pt} *)
uvar = Unique["u"];
vvar = Unique["v"];
rep1=Map[If[#>0,Power[E,Times[#,t]]\[Rule]Power[uvar,#/p],Power[E,Times[#,t]]\[Rule]Power[vvar,-#/p]]&,realRatEigs];
wvar = Unique["w"];
zvar = Unique["z"];
(* Replacement rule for imaginary part (trig)
	w = cos{qt}, z = sin{qt}
This trick is used to calculate the product rules for trig functions:
Cos[#,t] = ComplexExpand[Re[Power[Cos[q*t]+I*Sin[q*t],#/q]]]/.Cos[q*t]\[Rule]w
*)
 rep2=Map[If[#>0,
Cos[Times[#,t]]\[Rule](ComplexExpand[Re[Power[Cos[q*t]+I*Sin[q*t],#/q]]]/.{Cos[q*t]\[Rule] wvar,Sin[q*t]\[Rule] zvar})
,
Sin[Times[-#,t]]\[Rule](ComplexExpand[Im[Power[Cos[q*t]+I*Sin[q*t],-#/q]]]/.{Cos[q*t]\[Rule] wvar,Sin[q*t]\[Rule] zvar})]&,imRatEigs];
(* The added relationships *)
ratrel={uvar*vvar-1,wvar^2+zvar^2-1};

(* Partially handle non rational eigenvalues *)
realEigs =Select[DeleteDuplicates[Abs[Re[eigs]]],#\[NotEqual]0&] //Select[Not[RationalQ[#]]&]//Expand;
imEigs = Select[DeleteDuplicates[Abs[Im[eigs]]],#\[NotEqual]0&] //Select[Not[RationalQ[#]]&]//Expand;
Print["Real eigenvalue parts: ",realEigs];
Print["Imaginary eigenvalue parts: ",imEigs];
us = Table[Unique["u"],{i,Length[realEigs]}];
vs = Table[Unique["v"],{i,Length[realEigs]}];
ws = Table[Unique["w"],{i,Length[imEigs]}];
zs = Table[Unique["z"],{i,Length[imEigs]}];

irratrel = Join[MapThread[#1*#2-1&,{us,vs}],MapThread[#1^2+#2^2-1&,{ws,zs}]];
repu = MapThread[Power[E,Times[#1,t]]\[Rule]#2&,{realEigs,us}];
repv = MapThread[Power[E,Times[-#1,t]]\[Rule]#2&,{realEigs,vs}];
repw = MapThread[Cos[#1*t] \[Rule]#2&,{imEigs,ws}];
repz = MapThread[Sin[#1*t]\[Rule]#2&,{imEigs,zs}];
replacements=Join[rep1,rep2,repu,repv,repw,repz];
repvars =Join[{uvar,vvar,wvar,zvar},us,vs,ws,zs];
{replacements,Join[ratrel,irratrel],repvars}
]*)


(* ::Input::Initialization:: *)
(* Find alg invariants
  TODO: need to properly check that vf is linear (or affine)
TODO: properly extract algebraic initial conditions
*)
LinAlgInv[{ pre_, { vf_List, vars_List, evoConst_ }, post_}] := Block[{A,replacements,equations,repvars,nexp,mexp,inits,algpre,px,py,sol,repsol,polys,alginvs,DUMMYCONSTANT},
A=Grad[vf,vars];
{replacements,equations,repvars}=EigSolve[A];
inits=Map[Unique,vars];
Print[replacements,equations,repvars,inits];
algpre=(Select[pre/.And->List,Head[#]===Equal&]/.{Equal[px_,py_]->px-py})/.Thread[vars->inits];
mexp=MatrixExp[A t] //Normal //ComplexExpand;
sol=(mexp.inits)//.replacements;
Print["Solution: ",sol];
polys = Join[equations,sol-vars,algpre];
Print["Polynomials: ",polys];
alginvs=GroebnerBasis[polys,vars,Join[repvars,inits]]
];

LinAlgInvNumeric[{ pre_, { vf_List, vars_List, evoConst_ }, post_}] := Block[{A,replacements,equations,repvars,nexp,mexp,inits,algpre,px,py,sol,repsol,polys,alginvs,DUMMYCONSTANT,rrep,rat},
rat=10^-5;
A=Grad[vf,vars];
{replacements,equations,repvars}=EigSolve[A];
inits=Map[Unique,vars];
(*Print[replacements,equations,repvars,inits];*)
algpre=(Select[pre/.And->List,Head[#]===Equal&]/.{Equal[px_,py_]->px-py})/.Thread[vars->inits];
mexp = Rationalize[N[MatrixExp[A t]/.E->DUMMYCONSTANT]/.DUMMYCONSTANT->E //ComplexExpand,rat^2];
rrep=Rationalize[N[replacements/.E->DUMMYCONSTANT]/.DUMMYCONSTANT->E ,rat^2];
sol=(mexp.inits)//.rrep;
(*Print["Solution: ",sol];*)
polys = Join[equations,sol-vars,algpre];
(*Print["Polynomials: ",polys];*)
alginvs=Map[RoundPoly[#,rat]&,GroebnerBasis[polys,vars,Join[repvars,inits]]]
];
RoundPoly[p_,rat_]:=Block[{},
Rationalize[p/(Flatten[CoefficientList[p,Variables[p]]]//Abs//Max)//N//FullSimplify,rat]
]


End[]


EndPackage[]
