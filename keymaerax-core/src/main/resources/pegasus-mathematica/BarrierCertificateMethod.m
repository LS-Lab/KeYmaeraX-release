(* ::Package:: *)

Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] 
Needs["MATLink`"]


BeginPackage["BarrierCertificateMethod`"];


SOSBarrier::usage="SOSBarrierCertificate[problem_List] uses an interface to Matlab (MatLink plugin required!) to compute barrier certificates."
Options[SOSBarrier]= {NPrecision->6};


ConjunctiveIneqSetQ::usage="foo"


PreProcess::usage="fooo"


BTemplate::usage="BTemplate[deg_, vars_List] Polynomial template with symbolic coefficients (of degree at most 'deg')"


LPBarrier::usage="LPBarrier[deg_, problem_List] Linear relaxation for barrier certificate search up to degree 'deg'"


LPBarrierMATLAB::usage="LPBarrierMATLAB[deg_, problem_List] Linear relaxation for barrier certificate search up to degree 'deg'"


HandelmanRepEps::usage="HandelmanRepEps[BTemp_, vars_List, deg_Integer, constraints_List, eps_] Handelman representation of a template polynomial BTemp on a hyperbox given by constraints."


BoundingBox::usage="BoundingBox[set_,vars_List] Computes a hyperbox in R^|vars| which bounds a given set."


Begin["`Private`"]


Pegasus`NPRECISION=6; (* Default precision for numericising rationals *)


(* COMMON FUNCTIONS
TODO: move to a common Pegasus library file?
*)
(* Lie derivative of P wrt ODEs *)
Lf[P_,vars_,vf_]:=Grad[P,vars].vf;

(* Normalize formulas *)
LeqToGeq[formula_]:=Module[{}, formula/.{         LessEqual[lhs_,rhs_] :>  GreaterEqual[rhs,lhs]} ] 
LtToGt[formula_]:=Module[{}, formula/.{           Less[lhs_,rhs_]      :>  Greater[rhs,lhs]} ] 
UnequalToLtOrGt[formula_]:=Module[{}, formula/.{  Unequal[lhs_,rhs_]      :>  Or[Less[lhs,rhs] ,Less[rhs,lhs]]} ] 
EqualToLeqAndGeq[formula_]:=Module[{}, formula/.{ Equal[lhs_,rhs_]        :>  And[LessEqual[lhs,rhs] ,LessEqual[rhs,lhs]]} ] 
LeqToLtOrEqual[formula_]:=Module[{}, formula/.{   LessEqual[lhs_,rhs_]    :>  Or[Less[lhs,rhs] ,Equal[rhs,lhs]]} ] 

(* Set right-hand side of terms to zero *)
ZeroRHS[formula_]   :=  Module[{},formula/.{
Equal[a_,b_]        :>  Equal[a-b,0],
Unequal[a_,b_]      :>  Unequal[a-b,0],
Greater[a_,b_]      :>  Greater[a-b,0],
GreaterEqual[a_,b_] :>  GreaterEqual[a-b,0],
Less[a_,b_]         :>  Less[a-b,0], 
LessEqual[a_,b_]    :>  LessEqual[a-b,0]
}]

(* Return all monomials of a given polynomial wrt the variables *)
monomialList[poly_, vars_] := Times @@ (vars^#) & /@ CoefficientRules[poly, vars][[All, 1]]

(* Return the constant term in a polynomial *)
ConstTerm[P_,vrs_List]:=(Table[0,Length[vrs]]/.CoefficientRules[P,vrs])/.{a_List:>0};


(* A very basic Mathematica to Matlab expression converter *)
MmaToMatlab[list_List]:="["<>StringRiffle[Map[MmaToMatlab, list],"; "]<>"]"
MmaToMatlab[Power[trm_,exp_]]:=MmaToMatlab[trm]<>"^("<>MmaToMatlab[exp]<>")"
MmaToMatlab[Times[product_]]:= "("<>StringRiffle[MmaToMatlab /@ (List @@ product), "*"]<>")"
MmaToMatlab[product_Plus]:= "("<>StringRiffle[MmaToMatlab /@ (List @@ product), "+"]<>")"
MmaToMatlab[rat_Rational]:=InputForm[N[rat, Pegasus`NPRECISION], NumberMarks->False]//ToString
MmaToMatlab[atom_?AtomQ]:=ToString[atom//InputForm]

(* Relational symbols *)
MmaToMatlab[Greater[lhs_,rhs_]]:=MmaToMatlab[lhs]<>">"<>MmaToMatlab[rhs] 
MmaToMatlab[GreaterEqual[lhs_,rhs_]]:=MmaToMatlab[lhs]<>">="<>MmaToMatlab[rhs] 
MmaToMatlab[Equal[lhs_,rhs_]]:=MmaToMatlab[lhs]<>"=="<>MmaToMatlab[rhs] 
MmaToMatlab[LessEqual[lhs_,rhs_]]:=MmaToMatlab[lhs]<>"<="<>MmaToMatlab[rhs] 
MmaToMatlab[Less[lhs_,rhs_]]:=MmaToMatlab[lhs]<>"<"<>MmaToMatlab[rhs] 

(* Logical connectives *)
MmaToMatlab[implication_Implies]:="("<>MmaToMatlab[implication//LogicalExpand]<>")"
MmaToMatlab[conjunction_And]:="("<>StringRiffle[MmaToMatlab /@ List @@ conjunction, " & "]<>")"
MmaToMatlab[disjunction_Or]:="("<>StringRiffle[MmaToMatlab /@ List @@ disjunction, " | "]<>")"
MmaToMatlab[Not[negation_]]:="~("<>MmaToMatlab[negation]<>")"

MmaToMatlab[True]:="true"
MmaToMatlab[False]:="false"


PreProcess[expression_]:=PreProcess[expression]=Module[{},
BooleanMinimize[UnequalToLtOrGt[expression], "DNF"]//LogicalExpand//EqualToLeqAndGeq//LtToGt//LeqToGeq//ZeroRHS ] 


ConjunctiveIneqSetQ[set_]:=Module[{S=PreProcess[set]},
TrueQ[S==True] || 
(TrueQ[Head[S]===GreaterEqual || Head[S]===LessEqual] || Head[S]===Greater || Head[S]===Less || Head[S]===Equal) ||
(TrueQ[Head[S]===And] && AllTrue[Map[
ConjunctiveIneqSetQ[#] &, Level[S,{1}]], TrueQ])
]


ExtractPolys[form_]:=Module[{expr,lst},
expr=form//LogicalExpand//PreProcess;
lst= expr/.{And->List, GreaterEqual[lhs_,0]:> lhs, Greater[lhs_,0]:> lhs};
If[TrueQ[Head[expr]==And],
lst,
{lst}
]
]


HeuristicMonomials[vars_,vf_,degree_]:=Module[ {},
DeleteDuplicates[Flatten[Function[x,monomialList[x,vars]]/@vf]]]


SOSBarrier[{ pre_, { vf_List, vars_List, evoConst_ }, post_}, opts:OptionsPattern[]]:=Catch[Module[{init,unsafe,Q,f, precision,sosprog,res,lines,B, link, barrierscript,heumons},
If[Not[TrueQ[ 
ConjunctiveIneqSetQ[pre//LogicalExpand] && 
ConjunctiveIneqSetQ[Not[post]//LogicalExpand] && 
ConjunctiveIneqSetQ[evoConst//LogicalExpand] ]], 
Throw[{
(* Throws empty list if no result found
ConjunctiveIneqSetQ[pre//LogicalExpand],
ConjunctiveIneqSetQ[Not[post]//LogicalExpand],
ConjunctiveIneqSetQ[evoConst//LogicalExpand] *)
}]]; 
(* Open a link to Matlab *)
link=MATLink`OpenMATLAB[];

precision=OptionValue[NPrecision];

init=ExtractPolys[pre];
unsafe=ExtractPolys[Not[post]];
Q=If[TrueQ[evoConst],{}, ExtractPolys[evoConst]];

f=MmaToMatlab[vf];

heumons = HeuristicMonomials[vars,vf,2];
sosprog="
% Exponential barrier certificates

clear;
% Inputs from Mathematica
% Variables
pvar "<>StringRiffle[Map[MmaToMatlab, vars], " "]<>";
vars = "<>MmaToMatlab[vars]<>";

% Problem specification
% The vector field for each coordinate
field = "<>MmaToMatlab[vf]<>";
% Conj. Polynomials characterizing the initial set
inits = "<>MmaToMatlab[init]<>";
% Conj. Polynomials characterizing the unsafe set
unsafes = "<>MmaToMatlab[unsafe]<>" ;
% Conj. Polynomials characterizing the ev. domain
dom = "<>MmaToMatlab[Q]<>" ;

% Configurable options from Mathematica
% Configurable lambda in B' >= lambda B
lambdas = [-1,0,1];
% min and max degree bounds (incremented by 1 each time)
mindeg = 0;
maxdeg = 10;
% Additional monomials to use for the barrier certificate
monheu =  "<>MmaToMatlab[heumons]<>";
% Additional SOS basis monomials for SOS-variables
monheu2 = [];
% Encode strict inequalities p>0 as p-eps >=0
eps = 0.001;
% Minimum feasibility to accept a solution
minfeas = 0.9;

% MATLAB setup
init_dim = length(inits);
unsafe_dim = length(unsafes);
dom_dim = length(dom);

for deg = mindeg : maxdeg
    sosdeg = ceil(sqrt(deg));
    fprintf('monomial degree: %i sos degree: %i\\n', deg, sosdeg);
    monvec = vertcat(monomials(vars,0:1:deg),monheu);
    monvec2 = vertcat(monomials(vars,0:1:sosdeg),monheu2); 
    for i = 1 : length(lambdas)
        lambda = lambdas(i);
        fprintf('Trying lambda: %i\\n', lambda);
        % The SOS program
        prog = sosprogram(vars);

        % Template for the barrier certificate B
        [prog,B] = sospolyvar(prog,monvec);

        % SOS coefficients for each barrier in init
        for i=1:init_dim
          [prog,IP(i)] = sossosvar(prog,monvec2);
        end

        % Constrain barrier to be <= 0 on all inits
        % Note: could assume domain constraint here too
        prog = sosineq(prog, -IP*inits - B);

        % SOSes for the unsafe states
        for i=1:unsafe_dim
          [prog,FP(i)] = sossosvar(prog,monvec2);
        end

        % Constrain barrier to be > 0 on all unsafe
        % Note: could assume domain constraint here too
        prog = sosineq(prog, B - FP*unsafes - eps);

        % Lie derivatives for each component
        dB = 0*vars(1);
        for i = 1:length(vars)
          dB = dB+diff(B,vars(i))*field(i);
        end

        % Constrain the Lie derivative
        expr = lambda * B - dB;

        if dom_dim > 0
            % SOSes for each barrier in domain
            for i=1:dom_dim
              [prog,DP(i)] = sossosvar(prog,monvec2);
            end
            prog = sosineq(prog, expr -DP*dom);
        else
            prog = sosineq(prog, expr);
        end

        opt.params.fid = 0;
        prog = sossolve(prog,opt);

        feasibility = prog.solinfo.info.feasratio;
        if feasibility >= minfeas
            B2 = sosgetsol(prog,B)
            return;
        end
    end
end
B2 = 0
";
barrierscript=MATLink`MScript["expbarrier",sosprog, "Overwrite" -> True];
(* Print[sosprog]; *)
res=MATLink`MEvaluate@barrierscript;
lines=StringSplit[res,{"B2 =", "break"}];
B=CoefficientRules[N[StringReplace[StringDelete[lines[[-1]], "\n" | "\r" |" "], {"e-"->"*10^-"}]//ToExpression//Expand, 10]];
If[B=={},Throw[{}],Throw[MapAt[Function[x,Rationalize[Round[x,1/10^precision]]],B,{All,2}]~FromCoefficientRules~vars]];
]]


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
(* Multi-index exponents up to degree bound *)
monExponents =Flatten[Table[Flatten[Permutations/@IntegerPartitions[iter+Length[constraints],{Length[constraints]}]-1,1],{iter,0,deg,1}],1];
B= Map[Times @@ Thread[constraints^#]&,monExponents] //DeleteDuplicates;
lambdas = Table[Unique["\[Lambda]"], {i, Length[B]}]; 
(* Set all polynomial coefficients to 0 *)
lambdaB = (#1 == 0 & ) /@ Last /@ CoefficientRules[BTemp - lambdas . B -eps, vars]; 
(* Non-negative lambdas *)
lambdaPos = (#1 >= 0 & ) /@ lambdas; 
prob = Join[lambdaB, lambdaPos]; 
Throw[prob]
]]


LPBarrier[{ pre_, { vf_List, vars_List, evoConst_ }, post_}]:=Catch[Module[
(* Declare local variables *)
{init,unsafe,Q,B,LfB,BC1,BC2,BC3,deg,eps,lambda,prob,equations,inequalities,LPvars,
Aeq,Aineq,beq,bineq,const,obbjFn,LPres,objFn,LPsol,Binst},

(* TODO: pass these as params after unifying interfaces *)
deg = 5;
eps = 0.0001;
lambda = -0.5;

If[Not[TrueQ[ 
ConjunctiveIneqSetQ[pre//LogicalExpand] && 
ConjunctiveIneqSetQ[Not[post]//LogicalExpand] && 
ConjunctiveIneqSetQ[evoConst//LogicalExpand] ]], 
Throw[[
ConjunctiveIneqSetQ[pre//LogicalExpand],
ConjunctiveIneqSetQ[Not[post]//LogicalExpand],
ConjunctiveIneqSetQ[evoConst//LogicalExpand]]]]; 

init=ExtractPolys[pre];
unsafe=ExtractPolys[Not[post]];
Q=If[TrueQ[evoConst],{}, ExtractPolys[evoConst]];

(* TODO: adjoint additional constraints for axis-aligned bounding boxes
ibox=BoundingBox[init,vars];
ubox=BoundingBox[Not[safe],vars];
qbox=BoundingBox[Q,vars]; *)

(* Compute a symbolic template *)
B=BTemplate[deg,vars];
(* Compute the Lie derivative along the vector field *)
LfB=Lf[B,vars,vf];
(* Compute Handelman representations for each of the barrier certificate conditions *)
BC1=HandelmanRepEps[B,vars,deg, unsafe, eps]; (* Ubox \[Rule] B\[GreaterEqual]eps>0 *)
BC2=HandelmanRepEps[-B,vars,deg,init, 0]; (* Ibox \[Rule] B<=0 *)
BC3=HandelmanRepEps[-LfB+lambda*B,vars,deg,Q, 0]; (* qbox \[Rule] B'<=-B *)

(* Collect the systems of linear equations and inequalities into one *)
prob=Union[BC1,BC2,BC3];

(* Uncomment to return the linear program *)
(* Throw[prob]; *)

(* Explicit LinearProgramming implementation *)
equations=First/@Select[prob, Head[#]==Equal&];
inequalities=First/@Select[prob, Head[#]==GreaterEqual&];

(* Extract the symbolic variables for the linear program *)
LPvars=(Variables/@(First/@prob))//Flatten//DeleteDuplicates//Sort;
Aeq=Map[Grad[#,LPvars]&,equations];
Aineq=Map[Grad[#,LPvars]&,inequalities];

beq=Map[{-ConstTerm[#,LPvars],0}&, equations];
bineq=Table[{0,1}, Length[inequalities]];

const=Map[If[StringContainsQ[ToString[#], "\[Lambda]"], 0,-Infinity]&,LPvars];
objFn=Table[0,Length[LPvars]];

LPres=LinearProgramming[
  objFn,
  Join[Aeq,Aineq],
  Join[beq,bineq],
  const, Method->"InteriorPoint"
];
If[Head[LPres]===LinearProgramming, Throw[0]];
LPsol=Thread[LPvars -> LPres]; 

(* Solve the linear program conveniently using Minimize- optimising 0 to obtain a feasible point in the constraint *)
(* LPsol=Minimize[{0,And@@prob},LPvars][[2]]; *)

(* Instantiate solution and return *)
Binst=B/.LPsol;
Throw[Binst]
]]


End[]
EndPackage[]
