(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] (* LZZ *)


BeginPackage["Lyapunov`"];


CLFGen::usage="CLFGen[systems_List] Generate a common Lyapunov function";
MLFGen::usage="MLFGen[systems_List,transitions_List] Generate multiple Lyapunov functions";


Begin["`Private`"]


allMonomials[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,1,m}]]


RoundPolys[p_,vars_]:=Module[{cr},
cr = CoefficientRules[p,vars];
If[Length[cr] > 0,Map[MapAt[Function[x,Rationalize[Round[x,1/10^#]]],cr,{All,2}]~FromCoefficientRules~vars&,{2,4,6,8}]//DeleteDuplicates
,{}]]


CLFGen[systems_List, opts:OptionsPattern[]]:=Catch[Module[
{PRECISION,odes,domains,normdom,normlhs,allvars,ERRSTR,monomials,X,dim,linconds,linodes,conds,origsubs,dommat,Si,res,lyap},

(*ERRSTR="Incorrect CLF problem format.\n
Requires a list of ODEs represented as triplets {vf,vars,Q}.";*)
allvars = Map[#[[2]]&,systems] // Flatten // DeleteDuplicates;
odes=Map[#[[1]]&,systems];
domains=Map[CNFNormalizeGtGeq[#[[3]]]&,systems];
normdom=Map[({#/.{And->List,Greater->GreaterEqual}}//Flatten)&,domains];
dim=Length[allvars];
origsubs = Map[#->0&,allvars];

normlhs=Map[PadRight[Cases[#,GreaterEqual[x_,y_]->x],1]&,normdom];
Print[normlhs];
dommat=Map[Grad[#,allvars]/.origsubs&,normlhs,1];
Si=Map[Transpose[#].#&,dommat];
Print["Matrices ",Si];

Print["Solving ",systems, " over ",allvars];
X = Unique["X"];
linodes = Map[Grad[#,allvars]/.origsubs&,odes];

(*linconds=Map[
	Block[{},
		VectorLess[{(Transpose[#1].X +X. #1),0},{"SemidefiniteCone", dim}]
	]&,linodes];*)

linconds=MapThread[
	Block[{},
		Print[#1, #2];
		VectorLess[{ Inactivate[(Transpose[#1].X +X. #1)+#2,Plus],0},{"SemidefiniteCone", dim}]
	]&,{linodes,Si}];
conds=Join[linconds,{VectorGreater[{X, 0}, {"SemidefiniteCone", dim}]}];
res=SemidefiniteOptimization[0,conds,X];
If[MemberQ[X/.res//Flatten,Indeterminate], Return[{}]];
lyap = allvars.(X/.res).allvars // Rationalize//FullSimplify;
Return[RoundPolys[lyap,allvars]]
]];


MLFGen[systems_List, transitions_List,opts:OptionsPattern[]]:=Catch[Module[
{odes,domains,normdom,normlhs,allvars,ERRSTR,monomials,X,dim,linconds,linodes,semiconds,conds,origsubs,dommat,Si,res,lyap},

allvars = Map[#[[2]]&,systems] // Flatten // DeleteDuplicates;
odes=Map[#[[1]]&,systems];
domains=Map[CNFNormalizeGtGeq[#[[3]]]&,systems];
normdom=Map[({#/.{And->List,Greater->GreaterEqual}}//Flatten)&,domains];
dim=Length[allvars];
origsubs = Map[#->0&,allvars];

normlhs=Map[PadRight[Cases[#,GreaterEqual[x_,y_]->x],1]&,normdom];
Print[normlhs];
dommat=Map[Grad[#,allvars]/.origsubs&,normlhs,1];
Si=Map[Transpose[#].#&,dommat];
Print["Matrices ",Si];

Print["Solving ",systems, " over ",allvars];
X = Table[Unique["X"],{i,Length[systems]}];
linodes = Map[Grad[#,allvars]/.origsubs&,odes];

(*linconds=Map[
	Block[{},
		VectorLess[{(Transpose[#1].X +X. #1),0},{"SemidefiniteCone", dim}]
	]&,linodes];*)

linconds=MapThread[
	Block[{},
		Print[#1, #2,#3];
		VectorLess[{ Inactivate[(Transpose[#1].#3 + #3. #1)+#2,Plus],0},{"SemidefiniteCone", dim}]
	]&,{linodes,Si,X}];
semiconds=Map[VectorGreater[{#, 0}, {"SemidefiniteCone", dim}]&,X];
conds=Join[linconds,semiconds];
(*conds=Join[linconds,{VectorGreater[{X, 0}, {"SemidefiniteCone", dim}]}];*)
res=SemidefiniteOptimization[0,conds,X];
lyap = allvars.(X/.res).allvars // Rationalize//FullSimplify;

Return[lyap]
]];


End[]
EndPackage[]
