(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]] 


BeginPackage["Refute`"];


RefuteS::usage="Attempts to refute a conjectured safety problem using LZZ"


Begin["`Private`"]


RefuteS[A_, B_, f_List, vars_List, Q_, avars_List]:=Module[{
Cond1 = Q && A && Not[B],
Cond2 = Q && A && LZZ`InfS[Q,f,vars]&& Not[LZZ`InfS[B,f,vars]],
Cond3 = Q && Not[B] && LZZ`IvInfS[Q,f,vars] && LZZ`IvInfS[A,f,vars]
},
N[FindInstance[Cond1 || Cond2 || Cond3, avars, Reals] ]
]


End[]
EndPackage[]
