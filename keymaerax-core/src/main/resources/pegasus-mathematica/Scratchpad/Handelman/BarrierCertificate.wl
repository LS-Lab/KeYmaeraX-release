(* ::Package:: *)

Needs["MATLink`"]


BeginPackage[ "BarrierCertificate`"]


BTemplate::usage="BTemplate[deg_, vars_List] Polynomial template with symbolic coefficients (of degree at most 'deg')"


LPBarrier::usage="LPBarrier[deg_, problem_List] Linear relaxation for barrier certificate search up to degree 'deg'"


LPBarrierMATLAB::usage="LPBarrierMATLAB[deg_, problem_List] Linear relaxation for barrier certificate search up to degree 'deg'"


HandelmanRepEps::usage="HandelmanRepEps[BTemp_, vars_List, deg_Integer, constraints_List, eps_] Handelman representation of a template polynomial BTemp on a hyperbox given by constraints."


BoundingBox::usage="BoundingBox[set_,vars_List] Computes a hyperbox in R^|vars| which bounds a given set."


Begin[ "Private`" ]


BoundingBox[set_,vars_List]:=Catch[Module[{BoundingInterval},
BoundingInterval[var_]:={MinValue[{var, set},vars,Reals], MaxValue[{var, set},vars,Reals]};
Throw[Map[BoundingInterval, vars]]
]]


BTemplate[deg_Integer?NonNegative,vars_List]:=Catch[Module[{monBas,templateCoeffs,template},
(* Compute the monomial basis up to given degree *)
monBas=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^deg , vars, "DegreeLexicographic"]];
(* Create a template polynomial with symbolic coefficients *)
templateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[monBas]}];
template=Evaluate[templateCoeffs.monBas];
Throw[template]
]]


HandelmanRepEps[BTemp_, vars_List, deg_Integer, constraints_List, eps_] := Catch[Module[{m = Length[vars], 
monExponents, lowerEval, upperEval, Bhandel, fjs, fjalphaprod, lambdas, lambdaB, lambdaPos, prob, B}, 
(* Compute all the monomial multidegrees up to deg in vars *)
monExponents = First /@ CoefficientRules[(Plus @@ vars + 1)^deg, vars]; 
(* Compute upper and lower bounds on the state variables within the constraints *)
lowerEval = Thread[vars -> Min /@ constraints]; 
upperEval = Thread[vars -> Max /@ constraints]; 

fjs = Tuples[Thread[{vars - (vars /. lowerEval), (vars /. upperEval) - vars}]]; 
fjalphaprod = Function[fjproduct, (Times @@ Thread[fjproduct^#1] & ) /@ monExponents]; 
Bhandel = DeleteDuplicates[Flatten[fjalphaprod /@ fjs]]; 
B=Bhandel//DeleteDuplicates;
lambdas = Table[Unique["\[Lambda]"], {i, Length[B]}]; 
lambdaB = (#1 == 0 & ) /@ Last /@ CoefficientRules[BTemp - lambdas . B -eps, vars]; 
lambdaPos = (#1 >= 0 & ) /@ lambdas; 
prob = Join[lambdaB, lambdaPos]; 
Throw[prob]
]]


LPBarrier[deg_Integer?NonNegative, LAMBDA_/;NumericQ[LAMBDA], problem_List]:=Catch[Module[
(* Declare local variables *)
{init,safe,Q,vars,vf,ibox,ubox,qbox,vfdeg,lfdeg,PolyDegree,B,Lf,LfB,BC1,BC2,BC3,prob,LPvars,LPsol,Binst,
equations, inequalities, Aeq, Aineq, beq, bineq, const, objFn, LPres, ConstTerm},
(* Pattern match on safety problem 'Hoare triple' *)
{init, {vf,vars,Q}, safe}=problem;
(* Computing the maximal total polynomial degree of a given polynomial P *)
PolyDegree[P_]:=Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]];
(* Maximum degree of the vector field *)
vfdeg=Max[PolyDegree/@vf];
(* Maximum degree of the first Lie derivative *)
lfdeg=deg+vfdeg-1;

(* Compute bounding boxes for the initial and unsafe sets and the evolution constraint *)
ibox=BoundingBox[init,vars];
ubox=BoundingBox[Not[safe],vars];
qbox=BoundingBox[Q,vars];
(* qbox=BoundingBox[init||Not[safe],vars]; *)

(* Compute a symbolic template *)
B=BTemplate[deg,vars];
(* Compute the Lie derivative along the vector field *)
Lf[P_]:=Grad[P,vars].vf;
LfB=Lf[B];

(* Compute Handelman representations for each of the barrier certificate conditions *)
BC1=HandelmanRepEps[B,vars,deg,ubox, 1/100]; (* Ubox \[Rule] B>0 *)
BC2=HandelmanRepEps[-B,vars,deg,ibox, 0]; (* Ibox \[Rule] B<=0 *)
BC3=HandelmanRepEps[-LfB+LAMBDA*B,vars,lfdeg,qbox, 0]; (* qbox \[Rule] B'<=-B *)

(* Collect the systems of linear equations and inequalities into one *)
prob=Union[BC1,BC2,BC3];

(* Uncomment to return the linear program *)
(* Throw[prob]; *)

(* Explicit LinearProgramming implementation *)
equations=First/@Select[prob, Head[#]==Equal&];
inequalities=First/@Select[prob, Head[#]==GreaterEqual&];

(* Extract the symbolic variables for the linear program *)
LPvars=(Variables/@(First/@prob))//Flatten//DeleteDuplicates//Sort;

(* Return the constant term in a polynomial *)
ConstTerm[P_,vrs_List]:=(Table[0,Length[vrs]]/.CoefficientRules[P,vrs])/.{a_List:>0};

Aeq=Map[Grad[#,LPvars]&,equations];
Aineq=Map[Grad[#,LPvars]&,inequalities];

beq=Map[{-ConstTerm[#,LPvars],0}&, equations];
bineq=Table[{0,1}, Length[inequalities]];

const=Map[If[StringContainsQ[ToString[#], "\[Lambda]"], 0,-Infinity]&,LPvars];
objFn=#*0&/@LPvars;
 LPres=LinearProgramming[
objFn,
Join[Aeq,Aineq],
Join[beq,bineq],
const, Method->"InteriorPoint"
];
LPsol=Thread[LPvars -> LPres]; 

(* Solve the linear program conveniently using Minimize- optimising 0 to obtain a feasible point in the constraint *)
(* LPsol=Minimize[{0,And@@prob},LPvars][[2]]; *)

(* Instantiate solution and return *)
Binst=B/.LPsol;
Throw[Binst]
]]


LPBarrierMATLAB[deg_Integer?NonNegative, LAMBDA_/;NumericQ[LAMBDA], problem_List]:=Catch[Module[
(* Declare local variables *)
{init,safe,Q,vars,vf,ibox,ubox,qbox,vfdeg,lfdeg,PolyDegree,B,Lf,LfB,BC1,BC2,BC3,prob,LPvars,LPsol,Binst,
equations, inequalities, Aeq, Aineq, beq, bineq, const, objFn, LPres, ConstTerm,mSol},
(* Pattern match on safety problem 'Hoare triple' *)
{init, {vf,vars,Q}, safe}=problem;
(* Computing the maximal total polynomial degree of a given polynomial P *)
PolyDegree[P_]:=Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]];
(* Maximum degree of the vector field *)
vfdeg=Max[PolyDegree/@vf];
(* Maximum degree of the first Lie derivative *)
lfdeg=deg+vfdeg-1;

(* Compute bounding boxes for the initial and unsafe sets and the evolution constraint *)
ibox=BoundingBox[init,vars];
ubox=BoundingBox[Not[safe],vars];
qbox=BoundingBox[Q,vars];
(* qbox=BoundingBox[init||Not[safe],vars]; *)

(* Compute a symbolic template *)
B=BTemplate[deg,vars];
(* Compute the Lie derivative along the vector field *)
Lf[P_]:=Grad[P,vars].vf;
LfB=Lf[B];

(* Compute Handelman representations for each of the barrier certificate conditions *)
BC1=HandelmanRepEps[B,vars,deg,ubox, 1/100]; (* Ubox \[Rule] B>0 *)
BC2=HandelmanRepEps[-B,vars,deg,ibox, 0]; (* Ibox \[Rule] B<=0 *)
BC3=HandelmanRepEps[-LfB+LAMBDA*B,vars,lfdeg,qbox, 0]; (* qbox \[Rule] B'<=-B *)

(* Collect the systems of linear equations and inequalities into one *)
prob=Union[BC1,BC2,BC3];

(* Explicit LinearProgramming implementation *)
equations=First/@Select[prob, Head[#]==Equal&];
inequalities=First/@Select[prob, Head[#]==GreaterEqual&];

(* Extract the symbolic variables for the linear program *)
LPvars=(Variables/@(First/@prob))//Flatten//DeleteDuplicates//Sort;

(* Return the constant term in a polynomial *)
ConstTerm[P_,vrs_List]:=(Table[0,Length[vrs]]/.CoefficientRules[P,vrs])/.{a_List:>0};

MATLink`OpenMATLAB[];
Aeq=Map[Grad[#,LPvars]&,equations];
beq=Map[-ConstTerm[#,LPvars]&, equations];
Aineq=Map[-Grad[#,LPvars]&,inequalities];
bineq=Table[0, Length[inequalities]];
objFn=#*0&/@LPvars;
MATLink`MEvaluate["clear"];
MATLink`MSet["aeq", Aeq];
MATLink`MSet["beq", beq];
MATLink`MSet["aineq", Aineq];
MATLink`MSet["bineq",bineq];
MATLink`MSet["f", objFn];
MATLink`MEvaluate["lpsl = linprog(f,aineq,bineq,aeq,beq)"];
mSol=MATLink`MGet["lpsl"];
(* If nothing was found, return 0 *)
If[Length[mSol]==0, Throw[0]];
LPsol=Thread[LPvars -> mSol];

(* Instantiate solution and return *)
Binst=B/.LPsol;
Throw[Binst]
]]


End[]


EndPackage[]
