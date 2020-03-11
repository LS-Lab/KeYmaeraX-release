(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]


BeginPackage["LZZ`"];


NLieDerivatives::usage="NLieDerivatives[p,n,f,vars,domain] returns the first n higher Lie derivatives of p (including p itself)";
Rank::usage="Rank[p,f,vars,domain] Computes the value n such that the ideal (p,...p'^(n)) is saturated";
InfS::usage="InfS[S,f,vars,domain] Computes the local progress formula for S wrt f, vars";
IvInfS::usage="IvInfS[S,f,vars,domain] Same as InfS except for -f instead of f";
InvS::usage="InvS[S,f,vars,H] LZZ decision procedure determining continuous invariance of semi-algebaic set S 
under the flow of a polynomial vector field f with evolution constraint H.";
InvSFast::usage="InvSFast[S,f,vars,H] Same as InvS but does not run the full check. Sound but incomplete.";


Begin["`Private`"];


(* Given a polynomial, compute a list of its Lie derivatives up to order n *)
NLieDerivatives[p_, n_, f_List, vars_List,domain_]:=NLieDerivatives[p,n,f,vars,domain]=Module[{},
NestList[FullSimplify[Primitives`Lf[#,f,vars,domain]]&,p,n]
]


(* Given a polynomial, compute the condition requiring that its first n-1 Lie derivatives are 0 and its nth Lie derivative is < 0 *)
NthLieLtZero[p_,n_,f_List,vars_List,domain_]:=NthLieLtZero[p,n,f,vars,domain]=Module[{NLie,NthLieCondition},
If[n==0, p<0,
If[n==1, p==0 && Primitives`Lf[p,f,vars,domain]<0,
NLie = NLieDerivatives[p,n-1,f,vars,domain];
NthLieCondition = Primitives`Lf[Last[NLie],f,vars,domain]<0;
Apply[And,Map[Function[x,x==0],NLie]] && NthLieCondition
]]
]


(* Given a polynomial, compute the condition requiring that its first n-1 Lie derivatives are 0 and its nth Lie derivative is <= 0 *)
NthLieLeqZero[p_,n_,f_List,vars_List,domain_]:=NthLieLeqZero[p,n,f,vars,domain]=Module[{NLie,NthLieCondition},
If[n==0, p<0,
If[n==1, p==0 && Primitives`Lf[p,f,vars,domain]<=0,
NLie = NLieDerivatives[p,n-1,f,vars,domain];
NthLieCondition = Primitives`Lf[Last[NLie],f,vars,domain]<=0;
Apply[And,Map[Function[x,x==0],NLie]] && NthLieCondition
]]
]


(* Given a polynomial, compute the condition requiring that its first n Lie derivatives are all 0 *)
NthLieEqZero[p_,n_,f_List,vars_List,domain_]:=NthLieEqZero[p,n,f,vars,domain]=Module[{NLie},
NLie = NLieDerivatives[p,n,f,vars,domain];
Apply[And,Map[Function[x,x==0],NLie]] 
]


(* Given a polynomial p and an integer n, check that the ideal <p, Lfp, Lf^2p, ..., Lf^np > is saturated under adding Lie derivatives of higher order *)
Rank[p_,n_Integer,f_List,vars_List,domain_]:=Rank[p,n,f,vars,domain]=Module[{NLie,NPlusOneLie,GB,Remainder},
NLie=NLieDerivatives[p,n,f,vars,domain];
NPlusOneLie = Primitives`Lf[Last[NLie],f,vars,domain];
GB = GroebnerBasis[NLie, vars, MonomialOrder -> DegreeReverseLexicographic];
Remainder = PolynomialReduce[NPlusOneLie, GB, vars, MonomialOrder -> DegreeReverseLexicographic][[2]]
]


(* Given a polynomial p, compute its rank Rk(p), i.e. the smallest order n of the Lie derivative that saturates the ideal <p, Lfp, Lf^2p, ... > *)
Rank[p_,f_List,vars_List,domain_]:=Rank[p,f,vars,domain]=Module[{rem,n},
rem=1;
n=0;
While[Not[PossibleZeroQ[rem]],
n++;
rem=Rank[p,n,f,vars,domain];
];
n
]


InfpStrict[p_, f_List, vars_List,domain_]:=InfpStrict[p, f, vars,domain]=Module[{countToRank,rank},
rank = Rank[p,f,vars,domain];
countToRank =Table[i,{i,0,rank}];
Apply[Or, Map[Function[x,NthLieLtZero[p,x,f,vars,domain]], countToRank] ]
]


InfpNonStrict[p_, f_List, vars_List,domain_]:=InfpNonStrict[p, f, vars,domain]=Module[{countToRank,rank},
rank = Rank[p,f,vars,domain];
countToRank =Table[i,{i,0,rank-1}];
Apply[Or, Map[Function[x,NthLieLtZero[p, x,f,vars,domain]], countToRank] ] || NthLieLeqZero[p, rank,f,vars,domain]
]


InfpEqual[p_, f_List, vars_List,domain_]:=InfpEqual[p, f, vars,domain]=Module[{rank = Rank[p,f,vars]}, NthLieEqZero[p, rank,f,vars,domain] ]


InfS[S_, f_List, vars_List,domain_]:=InfS[S, f, vars,domain]=Module[{processedS=Primitives`DNFNormalizeLtLeq[S]},
processedS/.{
LessEqual[p_,0]:> InfpNonStrict[p, f,vars,domain], 
Equal[p_,0]:> InfpEqual[p, f,vars,domain], 
Less[p_,0]:>InfpStrict[p, f,vars,domain]}
]


IvInfS[S_, f_List, vars_List,domain_]:=InfS[S,-f,vars,domain]


InvS[S_, f_List, vars_List, H_]:=InvS[S, f, vars, H]=Module[{
Cond2 = Implies[S && H && InfS[H,f,vars,H], InfS[S,f,vars,H]],
Cond3 = Implies[Not[S] && H && IvInfS[H,f,vars,H], Not[IvInfS[S,f,vars,H]]]
},
Resolve[ForAll[vars, Cond2 && Cond3], Reals] 
]


InvSFast[S_, f_List, vars_List, H_]:=InvS[S, f, vars, H]=Module[{
(* TODO: this could also use 'fast' InfS/IvInfS e.g. that truncates at given rank *)
Cond2 = Implies[S && H , InfS[S,f,vars,H]],
Cond3 = Implies[Not[S] && H, Not[IvInfS[S,f,vars,H]]]
},
Resolve[ForAll[vars,Cond2 && Cond3], Reals]
]


End[];
EndPackage[];
