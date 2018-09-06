(* ::Package:: *)

Needs["Classifier`",NotebookDirectory[]<>"Classifier.m"] 


BeginPackage["NilpotentMethod`"];


NilpotentReachSet::usage="NilpotentReachSet[problem_List] Finds the reachable set of a nilpotent linear system of ODEs for the initial set."


Begin["`Private`"]


NilpotentReachSet[{ pre_, { f_List, vars_List, evoConst_ }, post_}]:=Catch[Module[
{X,ODEsystem,A,sol,varsT, subst,const, Pegasus`TIMEVARIABLE,reachT,reachSet},
(* If not nilpotent, nothing to do, return evolution constraint as the potentially reachable states *)
If[TrueQ[Classifier`NilpotentSystemQ[f,vars]], Print["System is nilpotent."]];
(* Else, extract system matrix *)
A=Grad[f,vars];
(* Turn variables into functions of time (TIMEVARIABLE) *)
varsT=Map[#[Pegasus`TIMEVARIABLE]&, vars];
Print[varsT];
(* Form a system of ODEs *)
ODEsystem=Map[Derivative[1][#][Pegasus`TIMEVARIABLE]&,vars]==A.varsT;
Print[ODEsystem];
(* Solve the system *)
sol=DSolve[ODEsystem,vars,Pegasus`TIMEVARIABLE];
subst=Thread[vars -> varsT];
const=Thread[Map[C[#]&, Range[Length[vars]]] -> vars];
Print[subst];
Print[const];
reachT=(((pre/.subst)/.sol)/.const)[[1]];
reachSet=Resolve[Exists[{Pegasus`TIMEVARIABLE},reachT && Pegasus`TIMEVARIABLE<=0],Reals] && evoConst;
Throw[reachSet]
]]


End[]
EndPackage[]
