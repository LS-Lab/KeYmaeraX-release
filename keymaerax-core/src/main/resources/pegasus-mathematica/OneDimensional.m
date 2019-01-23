(* ::Package:: *)

Needs["LZZ`",FileNameJoin[{Directory[],"LZZ.m"}]] 


BeginPackage["OneDimensional`"];


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
-potentialFn<=k
]


OneDimReach[problem_List]:=Module[{ToCells=Function[Form,If[TrueQ[Head[Form]==Or],Apply[List, Form],{Form}]],
EndpointInCell=Function[{var, endpoint, cell},Reduce[ForAll[var,Implies[var==endpoint,cell]], var, Reals]]},
(* Pattern match problem input *)
{Init,{{f},{var},Q},Postcond} = problem;
(* Start with the initial set *)
ReachSet=Init;
(* Compute 1-d CAD decompositions of regions where the derivative is positive, negative, and of the initial states *)
PosQCells= CylindricalDecomposition[Q&&f>0,{var}]//ToCells;
NegQCells= CylindricalDecomposition[Q&&f<0,{var}]//ToCells;
InitCells= CylindricalDecomposition[Init,{var}]//ToCells;
(* Compute the left and right end-points of the initial cells *)
InitRightEndpoints=Select[Map[ArgMax[{var,#},var, Reals]&,InitCells],Element[#,Reals]&]//Quiet;
InitLeftEndpoints=Select[Map[ArgMin[{var,#},var, Reals]&,InitCells],Element[#,Reals]&] //Quiet;
(* Iteratively check if the initial right end-points belong to positive derivative cells *)
Do[
Do[
ReachSet=If[TrueQ[EndpointInCell[var,endpoint, posQCell]],
(* if so, add all that's to the right in the cell *)
ReachSet || ((var>=endpoint) && posQCell), 
ReachSet
],{endpoint,InitRightEndpoints}],
{posQCell,PosQCells}];
(* Iteratively check if the initial left end-points belong to negative derivative cells *)
Do[
Do[
ReachSet=If[TrueQ[EndpointInCell[var,endpoint, negQCell]],
(* if so, add all that's to the left in the cell *)
ReachSet || ((var<=endpoint)&&negQCell), 
ReachSet
],{endpoint,InitLeftEndpoints}],
{negQCell,NegQCells}];
(* Return reachable set *)
Simplify[ReachSet]
]


End[]
EndPackage[]
