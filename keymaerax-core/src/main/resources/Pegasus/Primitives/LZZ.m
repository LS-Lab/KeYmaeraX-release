(* ::Package:: *)

BeginPackage["LZZ`"];


InvS::usage="InvS[S,f,H] LZZ decision procedure determining continuous invariance of semi-algebaic set S 
under the flow of a polynomial vector field f with evolution constraint H."


Begin["`Private`"]


(* Set righ-hand side of terms to zero *)
ZeroRHS[formula_]   :=  Module[{},formula/.{
Equal[a_,b_]        :>  Equal[a-b,0],
Unequal[a_,b_]      :>  Unequal[a-b,0],
Greater[a_,b_]      :>  Greater[a-b,0],
GreaterEqual[a_,b_] :>  GreaterEqual[a-b,0],
Less[a_,b_]         :>  Less[a-b,0], 
LessEqual[a_,b_]    :>  LessEqual[a-b,0]
}]


GeqToLeq[formula_]:=Module[{}, formula/.{         GreaterEqual[lhs_,rhs_] :>  LessEqual[rhs,lhs]} ] 
GtToLt[formula_]:=Module[{}, formula/.{           Greater[lhs_,rhs_]      :>  Less[rhs,lhs]} ] 
UnequalToLtOrGt[formula_]:=Module[{}, formula/.{  Unequal[lhs_,rhs_]      :>  Or[Less[lhs,rhs] ,Less[rhs,lhs]]} ] 
EqualToLeqAndGeq[formula_]:=Module[{}, formula/.{ Equal[lhs_,rhs_]        :>  And[LessEqual[lhs,rhs] ,LessEqual[rhs,lhs]]} ] 
LeqToLtOrEqual[formula_]:=Module[{}, formula/.{   LessEqual[lhs_,rhs_]    :>  Or[Less[lhs,rhs] ,Equal[rhs,lhs]]} ] 


PreProcess[expression_]:=PreProcess[expression]=Module[{},
ZeroRHS[ GeqToLeq[ GtToLt[
LogicalExpand[BooleanMinimize[UnequalToLtOrGt[expression], "DNF"]]
] ] ] ] 


(* Lie derivative *)
LD[p_, f_List, vars_List]:=Grad[p,vars].f


(* Given a polynomial, compute a list of its Lie derivatives up to order n *)
NLieDerivatives[p_, n_, f_List, vars_List]:=NLieDerivatives[p,n,f,vars]=Module[{},
NestList[LD[#,f,vars]&,p,n]
]


(* Given a polynomial, compute the condition requiring that its first n-1 Lie derivatives are 0 and its nth Lie derivative is < 0 *)
NthLieLtZero[p_,n_,f_List,vars_List]:=NthLieLtZero[p,n,f,vars]=Module[{NLie,NthLieCondition},
If[n==0, p<0,
If[n==1, p==0 && LD[p,f,vars]<0,
NLie = NLieDerivatives[p,n-1,f,vars];
NthLieCondition = LD[Last[NLie],f,vars]<0;
Apply[And,Map[Function[x,x==0],NLie]] && NthLieCondition
]]
]


(* Given a polynomial, compute the condition requiring that its first n-1 Lie derivatives are 0 and its nth Lie derivative is <= 0 *)
NthLieLeqZero[p_,n_,f_List,vars_List]:=NthLieLeqZero[p,n,f,vars]=Module[{NLie,NthLieCondition},
If[n==0, p<0,
If[n==1, p==0 && LD[p,f,vars]<=0,
NLie = NLieDerivatives[p,n-1,f,vars];
NthLieCondition = LD[Last[NLie],f,vars]<=0;
Apply[And,Map[Function[x,x==0],NLie]] && NthLieCondition
]]
]


(* Given a polynomial, compute the condition requiring that its first n Lie derivatives are all 0 *)
NthLieEqZero[p_,n_,f_List,vars_List]:=NthLieEqZero[p,n,f,vars]=Module[{NLie},
NLie = NLieDerivatives[p,n,f,vars];
Apply[And,Map[Function[x,x==0],NLie]] 
]


(* Given a polynomial p and an integer n, check that the ideal <p, Lfp, Lf^2p, ..., Lf^np > is saturated under adding Lie derivatives of higher order  *)
Rank[p_,n_,f_List,vars_List]:=Rank[p,n,f,vars]=Module[{NLie,NPlusOneLie,GB,Remainder},
NLie=NLieDerivatives[p,n,f,vars];
NPlusOneLie = LD[Last[NLie],f,vars];
GB = GroebnerBasis[NLie, vars, MonomialOrder -> DegreeReverseLexicographic];
Remainder = PolynomialReduce[NPlusOneLie, GB, vars, MonomialOrder -> DegreeReverseLexicographic][[2]]
]


(* Given a polynomial p, compute its rank Rk(p), i.e. the smallest order n of the Lie derivative that saturates the ideal <p, Lfp, Lf^2p, ... > *)
Rank[p_,f_List,vars_List]:=Rank[p,f,vars]=Module[{rem,n},
rem=1;
n=0;
While[Not[PossibleZeroQ[rem]],
n++;
rem=Rank[p,n,f,vars];
];
n
]


InfpStrict[p_, f_List, vars_List]:=InfpStrict[p, f, vars]=Module[{countToRank,rank},
rank = Rank[p,f,vars];
countToRank =Table[i,{i,0,rank}];
Apply[Or, Map[Function[x,NthLieLtZero[p,x,f,vars]], countToRank] ]
]


InfpNonStrict[p_, f_List, vars_List]:=InfpNonStrict[p, f, vars]=Module[{countToRank,rank},
rank = Rank[p,f,vars];
countToRank =Table[i,{i,0,rank-1}];
Apply[Or, Map[Function[x,NthLieLtZero[p, x,f,vars]], countToRank] ] || NthLieLeqZero[p, rank,f,vars]
]


InfpEqual[p_, f_List, vars_List]:=InfpEqual[p, f, vars]=Module[{rank = Rank[p,f,vars]}, NthLieEqZero[p, rank,f,vars] ]


InfS[S_, f_List, vars_List]:=InfS[S, f, vars]=Module[{processedS=PreProcess[S]},
processedS/.{
LessEqual[p_,0]:> InfpNonStrict[p, f,vars], 
Equal[p_,0]:> InfpEqual[p, f,vars], 
Less[p_,0]:>InfpStrict[p, f,vars]}
]


IvInfS[S_, f_List, vars_List]:=IvInfS[S, f, vars]=Module[{processedS=PreProcess[S]},
processedS/.{
LessEqual[p_,0] :> InfpNonStrict[p, -f,vars],
Equal[p_,0] :> InfpEqual[p, -f,vars], 
Less[p_,0] :>InfpStrict[p, -f,vars]}
]


ComplementS[S_]:=ComplementS[S]=Module[{},PreProcess[Not[S]] ]


InvS[S_, f_List, vars_List, H_]:=InvS[S, f, vars, H]=Module[{
Cond2 = Implies[S && H && InfS[H,f,vars], InfS[S,f,vars]],
Cond3 = Implies[ComplementS[S] && H && IvInfS[H,f,vars], ComplementS[IvInfS[S,f,vars]]]
},
Resolve[ForAll[vars, Cond2 && Cond3], Reals] 
]


End[]
EndPackage[]
