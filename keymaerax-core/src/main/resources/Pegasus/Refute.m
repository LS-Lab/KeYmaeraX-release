(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]]


BeginPackage["Refute`"];


RefuteS::usage="Attempts to refute a conjectured safety problem using LZZ"
SeqFml::usage="Returns necessary & sufficient conditions for Post to be an ODE invariant and necessary conditions for Pre -> [x'=f(x)&Q]Post"


Begin["`Private`"]


RefuteS[A_, B_, f_List, vars_List, Q_, avars_List]:=Module[{
Cond1 = Q && A && Not[B],
Cond2 = Q && A && LZZ`InfS[Q,f,vars]&& Not[LZZ`InfS[B,f,vars]],
Cond3 = Q && Not[B] && LZZ`IvInfS[Q,f,vars] && LZZ`IvInfS[A,f,vars]
},
N[FindInstance[Cond1 || Cond2 || Cond3, avars, Reals] ]
]


SeqFml[A_, B_, f_List, vars_List, Q_]:=Module[{
(* B \[Rule] [x'=f(x)&Q] B *)
(* B,Q,Q* \[Rule] B* *)
Condi1 = Implies[B && Q && LZZ`InfS[Q,f,vars] , LZZ`InfS[B,f,vars]],
(* ~B,Q,Q-* \[Rule] ~B-* *)
Condi2 = Implies[Not[B] && Q && LZZ`IvInfS[Q,f,vars] , Not[LZZ`IvInfS[B,f,vars]]],
(* A \[Rule] [x'=f(x)&Q] B *)
(* Q, A \[Rule] B *)
Condn1 = Implies[Q && A , B],
(* Q,A,Q* \[Rule] B* *)
Condn2 = Implies[A && Q && LZZ`InfS[Q,f,vars], LZZ`InfS[B,f,vars]],
(* Q,~B,Q-* \[Rule] ~A* *)
Condn3 = Implies[Not[B] && Q && LZZ`IvInfS[Q,f,vars], Not[LZZ`IvInfS[A,f,vars]]]
},
{Condi1,Condi2,Condn1,Condn2,Condn3}
]


End[]
EndPackage[]
