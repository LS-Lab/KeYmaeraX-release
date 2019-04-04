(* ::Package:: *)

Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] 


BeginPackage["Strategies`OneDimensional`"];


OneDimPotential::usage="OneDimPotential[problem_List] Attempts to find an invariant using the potential function of the one-dimensional system."
OneDimReach::usage="OneDimReach[problem_List] Uses roots of the right-hand side and extreme points to build the reachable set of a one-dimensional ODE."


Begin["`Private`"]


OneDimPotential[problem_List]:=Module[{pre,post,statevar,Q,f,k,potentialFn},
(* Pattern match problem input *)
{pre,{{f},{statevar},Q},post} = problem;
(* Compute the potential function *)
potentialFn=-Integrate[f, statevar];
(* Compute the maximum value on the initial set *)
k=MaxValue[{potentialFn,pre},statevar];
(* Return potential-based invariant *)
{-potentialFn-k}
]


OneDimReach[problem_List]:=Module[{pre,post,statevar,Q,f},
(* Pattern match problem input *)
{pre,{{f},{statevar},Q},post} = problem;
(STATEVAR-statevar/.Solve[f==0,{statevar}, Reals])/.{STATEVAR->statevar}
]


End[]
EndPackage[]
