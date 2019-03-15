(* ::Package:: *)

Needs["Classifier`",FileNameJoin[{Directory[],"Classifier.m"}]] 
Needs["MATLink`"]


BeginPackage["BarrierCertificateMethod`"];


BarrierCertificate::usage="BarrierCertificateMethod[problem_List] uses an interface to Matlab (MatLink plugin required!) to compute barrier certificates."
Options[BarrierCertificate]= {NPrecision->6};


Begin["`Private`"]


Pegasus`NPRECISION=6; (* Default precision for numericising rationals *)


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


(* Set right-hand side of terms to zero *)
ZeroRHS[formula_]   :=  Module[{},formula/.{
Equal[a_,b_]        :>  Equal[a-b,0],
Unequal[a_,b_]      :>  Unequal[a-b,0],
Greater[a_,b_]      :>  Greater[a-b,0],
GreaterEqual[a_,b_] :>  GreaterEqual[a-b,0],
Less[a_,b_]         :>  Less[a-b,0], 
LessEqual[a_,b_]    :>  LessEqual[a-b,0]
}]


LeqToGeq[formula_]:=Module[{}, formula/.{         LessEqual[lhs_,rhs_] :>  GreaterEqual[rhs,lhs]} ] 
LtToGt[formula_]:=Module[{}, formula/.{           Less[lhs_,rhs_]      :>  Greater[rhs,lhs]} ] 
UnequalToLtOrGt[formula_]:=Module[{}, formula/.{  Unequal[lhs_,rhs_]      :>  Or[Less[lhs,rhs] ,Less[rhs,lhs]]} ] 
EqualToLeqAndGeq[formula_]:=Module[{}, formula/.{ Equal[lhs_,rhs_]        :>  And[LessEqual[lhs,rhs] ,LessEqual[rhs,lhs]]} ] 
LeqToLtOrEqual[formula_]:=Module[{}, formula/.{   LessEqual[lhs_,rhs_]    :>  Or[Less[lhs,rhs] ,Equal[rhs,lhs]]} ] 


PreProcess[expression_]:=PreProcess[expression]=Module[{},
BooleanMinimize[UnequalToLtOrGt[expression], "DNF"]//LogicalExpand//EqualToLeqAndGeq//LtToGt//LeqToGeq//ZeroRHS ] 


ConjunctiveIneqSetQ[set_]:=Module[{S=PreProcess[set]},
TrueQ[S==True] || 
(TrueQ[Head[S]==GreaterEqual || Head[S]==LessEqual] || Head[S]==Greater || Head[S]==Less) ||
(TrueQ[Head[S]==And] && AllTrue[Map[
Head[#]==LessEqual || Head[#]==GreaterEqual || Head[#]==Greater || Head[#]==Less &, Level[set,{1}]], TrueQ])
]


ExtractPolys[form_]:=Module[{expr,lst},
expr=form//LogicalExpand//PreProcess;
If[TrueQ[Head[expr]==And],
lst= expr/.{And->List, GreaterEqual[lhs_,0]:> lhs, Greater[lhs_,0]:> lhs};
MmaToMatlab[lst],
"["<>MmaToMatlab[(expr//LogicalExpand//PreProcess)/.{GreaterEqual[lhs_,0]:> lhs, Greater[lhs_,0]:> lhs}]<>"]"
]
]


monomialList[poly_, vars_] := Times @@ (vars^#) & /@ CoefficientRules[poly, vars][[All, 1]]


HeuristicMonomials[vars_,vf_,degree_]:=Module[ {},
DeleteDuplicates[Flatten[Function[x,monomialList[x,vars]]/@vf]]]


BarrierCertificate[{ pre_, { vf_List, vars_List, evoConst_ }, post_}, opts:OptionsPattern[]]:=Catch[Module[{init,unsafe,Q,f, precision,sosprog,res,lines,B, link, barrierscript,heumons},
If[Not[TrueQ[ 
ConjunctiveIneqSetQ[pre//LogicalExpand] && 
ConjunctiveIneqSetQ[Not[post]//LogicalExpand] && 
ConjunctiveIneqSetQ[evoConst//LogicalExpand] ]], 
Throw[[
ConjunctiveIneqSetQ[pre//LogicalExpand],
ConjunctiveIneqSetQ[Not[post]//LogicalExpand],
ConjunctiveIneqSetQ[evoConst//LogicalExpand]]]]; 

(* Open a link to Matlab *)
link=MATLink`OpenMATLAB[];

precision=OptionValue[NPrecision];

init=ExtractPolys[pre];
unsafe=ExtractPolys[Not[post]];
Q=If[TrueQ[evoConst],MmaToMatlab[{}], ExtractPolys[evoConst]];

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
inits = "<>init<>";
% Conj. Polynomials characterizing the unsafe set
unsafes = "<>unsafe<>" ;
% Conj. Polynomials characterizing the ev. domain
dom = "<>Q<>" ;

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
B=N[StringReplace[StringDelete[lines[[-1]], "\n" | "\r" |" "], {"e-"->"*10^-"}]//ToExpression//Expand, 10];
Throw[MapAt[Function[x,Rationalize[Round[x,1/10^precision]]],CoefficientRules[B],{All,2}]~FromCoefficientRules~vars];
]]


End[]
EndPackage[]
