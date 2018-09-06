(* ::Package:: *)

Needs["Classifier`",NotebookDirectory[]<>"Classifier.m"] 
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


(* Set righ-hand side of terms to zero *)
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
BooleanMinimize[UnequalToLtOrGt[expression], "DNF"]//LogicalExpand//LtToGt//LeqToGeq//ZeroRHS ] 


ConjunctiveIneqSetQ[set_]:=Module[{S=PreProcess[set]},
TrueQ[S==True] || 
(TrueQ[Head[S]==GreaterEqual || Head[S]==LessEqual] || Head[S]==Greater || Head[S]==Less) ||
(TrueQ[Head[S]==And] && AllTrue[Map[
Head[#]==LessEqual || Head[#]==GreaterEqual || Head[#]==Greater || Head[#]==Less &, Level[set,{1}]], TrueQ])
]


ExtractPolys[form_]:=Module[{expr,lst},
expr=form//LogicalExpand//PreProcess;
If[TrueQ[Head[expr]==And],
lst= expr/.{And->List, GreaterEqual[lhs_,0]:> lhs};
MmaToMatlab[lst],
"["<>MmaToMatlab[(expr//LogicalExpand//PreProcess)/.{GreaterEqual[lhs_,0]:> lhs}]<>"]"
]
]


BarrierCertificate[{ pre_, { vf_List, vars_List, evoConst_ }, post_}, opts:OptionsPattern[]]:=Catch[Module[{init,unsafe,Q,f, precision,sosprog,res,lines,B, link, barrierscript},
If[Not[TrueQ[ 
ConjunctiveIneqSetQ[pre//LogicalExpand] && 
ConjunctiveIneqSetQ[Not[post]//LogicalExpand] && 
ConjunctiveIneqSetQ[evoConst//LogicalExpand] ]], 
Throw[evoConst]]; 

(* Open a link to Matlab *)
link=MATLink`OpenMATLAB[];

Pegasus`NPRECISION=OptionValue[NPrecision];

init=ExtractPolys[pre];
unsafe=ExtractPolys[Not[post]];
Q=If[TrueQ[evoConst],0, ExtractPolys[evoConst]];

f=MmaToMatlab[vf];

sosprog="
% SOS vector barrier certificates
% These are the two examples constructed by Khalil
% for the original submission
% ex 1 is the linear barriers example currently in the paper

clear; echo on;
pvar "<>StringRiffle[Map[MmaToMatlab, vars], " "]<>";
vars = "<>MmaToMatlab[vars]<>";

%Working example (using 2D vector barrier + deg 2 polynomials):
field = "<>MmaToMatlab[vf]<>";
inits = "<>init<>";
unsafes = "<>unsafe<>" ;

 A = [[-1]];

%The problem (ex 2):
%field = [ x1*x2; -x2^2; 1+x3-x2*x3];
%x1<=-1,x2>=0,x3>=0 -- Bounding x1,x2,x3 away from zero helps a lot
%inits = [-1-x1, x2, x3];
%x1*x2>=1
%unsafes = [x1*x2-1];
%A = [[0 1 0];[0 0 0];[1 0 1]];

init_dim = length(inits)
unsafe_dim = length(unsafes)

barrier_dim = 1;
maxdeg = 2;
maxsosdeg = 2;
monvec = monomials("<>MmaToMatlab[vars]<>",0:1:maxdeg);
monvec2 = monomials("<>MmaToMatlab[vars]<>",0:1:maxsosdeg);

%strict inequality tolerance
eps = 0.001;
%polynomial coefficient tolerance
poly_tol = 1e-4;

prog = sosprogram(vars);
% The m-D vector barrier certificate (B1,...,Bm)
for i=1:barrier_dim
    [prog,B(i)] = sospolyvar(prog,monvec);
end

% SOSes for each barrier in init
for i = 1:barrier_dim
    for j=1:init_dim
        [prog,IP(i,j)] = sossosvar(prog,monvec2);
    end
end

%Constrain barriers to be <= 0 on all inits
for i=1:barrier_dim
  sum = 0;
  for j=1:init_dim
      sum = sum + IP(i,j)*inits(j);
  end
  prog = sosineq(prog, -sum - B(i));
end

% SOSes for the unsafe states
for i=1:unsafe_dim
    [prog,FP(i)] = sossosvar(prog,monvec2);
end

%Constrain only the first barrier to be > 0
sum = 0;
for i=1:unsafe_dim
  sum = sum + FP(i) * unsafes(i);
end
prog = sosineq(prog, (B(1) - sum) - eps);

%Lie derivatives for each component
for i=1:barrier_dim
    dB(i) = 0*vars(1);
    for j = 1:length(vars)
        dB(i) = dB(i)+diff(B(i),vars(j))*field(j);
    end
end

expr = A * transpose(B) - transpose(dB);
for i = 1:barrier_dim
    prog = sosineq(prog,expr(i));
end

opt.params.fid = 0;
prog = sossolve(prog,opt);

feasibility = prog.solinfo.info.feasratio;
B2 = sosgetsol(prog,B);
%for i = 1:barrier_dim
%    [t,B2(i)] = truncate_coeffs(B2(i),poly_tol);
%end
B2";

barrierscript=MATLink`MScript["expbarrier",sosprog];
res=MATLink`MEvaluate@barrierscript;
lines=StringSplit[res,{"B2 = ", "break"}];
B=N[StringReplace[lines[[-1]], {"\n"->"", "e-"->"*10^-"}]//ToExpression//Expand, 10]//Rationalize;
Throw[B];
]]


End[]
EndPackage[]
