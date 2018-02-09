(* ::Package:: *)

BeginPackage["Methods`"];


InvS::usage="InvS[S,f,H] LZZ decision procedure]"
Abstraction::usage="GenerateDiscreteAbstraction[f_List,vars_List,H_,p_List] Generate a discrete abstraction of a continuous system."
LazyReach::usage="LazyReach[precond_, postcond_, system_List, A_List] Lazily compute the continuous invariant by computing the reachable set in the abstraction from the initial set of states"
LazyChain::usage="LazyReach[precond_, postcond_, system_List, A_List] Lazily compute the continuous invariant by computing the reachable set in the abstraction from the initial set of states"
EagerReach::usage="EagerReach[precond_, postcond_, system_List, A_List] Eagerly compute the continuous invariant by computing the full abstraction first and then generating the reachable set from the initial set of states"
DCLoop::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] Iteratively refine evolution constraint using differential cuts before computing the abstraction."
DWC::usage="DWC[precond_, postcond_, system_List, H0_List, A0_List] Iteratively refine evolution constraint using differential cuts before computing the abstraction."
DWCLZR::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] Iteratively refine evolution constraint using differential cuts before computing the abstraction."
DWCLZRC::usage="DCLoop[precond_, postcond_, system_List, H0_List, A0_List] Iteratively refine evolution constraint using differential cuts before computing the abstraction."
OneDimReach::usage="OneDimReach"
OneDimPotential::usage="OneDimReach"


Begin["`Private`"]


(* INVARIANT CHECKING SECTION *)


(* Set righ-hand side of terms to zero *)
ZeroRHS[formula_] := Module[{},formula/.{
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


PreProcess[expression_]:=Module[{},
ZeroRHS[
GeqToLeq[
GtToLt[
LogicalExpand[BooleanMinimize[UnequalToLtOrGt[expression], "DNF"]]
]
]
]
] 


(* Lie derivative *)
LD[p_, f_List, vars_List]:=Grad[p,vars].f


(* Smoothness condition: non-vanishing gradient *)
NonZeroGrad[p_, f_List, vars_List]:=LogicalExpand[Grad[p,vars]!= Map[Function[x,0],vars]]


(* Given a polynomial, compute a list of its Lie derivatives up to order n *)
NLieDerivatives[p_,n_, f_List, vars_List]:=Module[{},
NestList[LD[#,f,vars]&,p,n]
]


(* Given a polynomial, compute the condition requiring that its first n-1 Lie derivatives are 0 and its nth Lie derivative is < 0 *)
NthLieLtZero[p_,n_,f_List,vars_List]:=Module[{},
If[n==0, p<0,
If[n==1, p==0 && LD[p,f,vars]<0,
NLie = NLieDerivatives[p,n-1,f,vars];
NthLieCondition = LD[Last[NLie],f,vars]<0;
Apply[And,Map[Function[x,x==0],NLie]] && NthLieCondition
]]
]


(* Given a polynomial, compute the condition requiring that its first n-1 Lie derivatives are 0 and its nth Lie derivative is <= 0 *)
NthLieLeqZero[p_,n_,f_List,vars_List]:=Module[{},
If[n==0, p<0,
If[n==1, p==0 && LD[p,f,vars]<=0,
NLie = NLieDerivatives[p,n-1,f,vars];
NthLieCondition = LD[Last[NLie],f,vars]<=0;
Apply[And,Map[Function[x,x==0],NLie]] && NthLieCondition
]]
]


(* Given a polynomial, compute the condition requiring that its first n Lie derivatives are all 0 *)
NthLieEqZero[p_,n_,f_List,vars_List]:=Module[{},
NLie = NLieDerivatives[p,n,f,vars];
Apply[And,Map[Function[x,x==0],NLie]] 
]


(* Given a polynomial p and an integer n, check that the ideal <p, Lfp, Lf^2p, ..., Lf^np > is saturated under adding Lie derivatives of higher order  *)
Rank[p_,n_,f_List,vars_List]:=Module[{},
NLie=NLieDerivatives[p,n,f,vars];
NPlusOneLie = LD[Last[NLie],f,vars];
GB = GroebnerBasis[NLie, vars, MonomialOrder -> DegreeReverseLexicographic];
Remainder = PolynomialReduce[NPlusOneLie, GB, vars, MonomialOrder -> DegreeReverseLexicographic][[2]]
]


(* Given a polynomial p, compute its rank Rk(p), i.e. the smallest order n of the Lie derivative that saturates the ideal <p, Lfp, Lf^2p, ... > *)
Rank[p_,f_List,vars_List]:=Module[{},
rem=1;
n=0;
While[Not[PossibleZeroQ[rem]],
n++;
rem=Rank[p,n,f,vars];
];
n
]


InfpStrict[p_, f_List, vars_List]:=Module[{rank = Rank[p,f,vars]},
countToRank =Table[i,{i,0,rank}];
Apply[Or, Map[Function[x,NthLieLtZero[p,x,f,vars]], countToRank] ]
]


InfpNonStrict[p_, f_List, vars_List]:=Module[{rank = Rank[p,f,vars]},
countToRank =Table[i,{i,0,rank-1}];
Apply[Or, Map[Function[x,NthLieLtZero[p, x,f,vars]], countToRank] ] || NthLieLeqZero[p, rank,f,vars]
]


InfpEqual[p_, f_List, vars_List]:=Module[{rank = Rank[p,f,vars]}, NthLieEqZero[p, rank,f,vars] ]


InfS[S_, f_List, vars_List]:=Module[{processedS=PreProcess[S]},
processedS/.{
LessEqual[p_,0]:> InfpNonStrict[p, f,vars], 
Equal[p_,0]:> InfpEqual[p, f,vars], 
Less[p_,0]:>InfpStrict[p, f,vars]}
]


IvInfS[S_, f_List, vars_List]:=Module[{processedS=PreProcess[S]},
processedS/.{
LessEqual[p_,0] :> InfpNonStrict[p, -f,vars],
Equal[p_,0] :> InfpEqual[p, -f,vars], 
Less[p_,0] :>InfpStrict[p, -f,vars]}
]


ComplementS[S_]:=Module[{},PreProcess[Not[S]] ]


InvS[S_, f_List, vars_List, H_]:=Module[{
Cond2 = Implies[S && H && InfS[H,f,vars], InfS[S,f,vars]],
Cond3 = Implies[ComplementS[S] && H && IvInfS[H,f,vars], ComplementS[IvInfS[S,f,vars]]]
},
Resolve[ForAll[vars, Cond2 && Cond3], Reals] 
]


(* Implementation of differential invariants *)
DI[formula_, f_List, vars_List, H_]:=Module[{processed=PreProcess[formula]},
OrToAnd=processed/.{Or->And};
condition=OrToAnd/.{
Less[p_,0]:> LD[p,f,vars]<0,
Greater[p_,0]:> LD[p,f,vars]>0,
LessEqual[p_,0]:> LD[p,f,vars]<=0,
GreaterEqual[p_,0]:> LD[p,f,vars]>=0,
Equal[p_,0]:> LD[p,f,vars]==0
};
Implies[H,condition]
]


(* END OF INVARIANT CHECKING SECTION *)


(* DISCRETE ABSTRACTION SECTION *)


(* Discrete state space construction *)
Options[SignPartition]={Parallel->False,  TimeoutValue->5};
SignPartition[states_List, polynomials_List, vars_List,  opts:OptionsPattern[]]:=Module[{},

If[Length[polynomials]==0, Print["Total number of discrete states: ", Length[states]]];

If[Length[polynomials]==0 || Length[states]==0, Return[states]];

p= First[polynomials];
S={};

(* Partition each existing states *)
(* Internally, states are represented as a list in which the first element is always the 
    constraint H and the following entries are sign conditions on polynomilas, e.g. a 
    state has the form { H, p1>0, p2\[Equal]0, p3>0, p4<0, ... , pm\[Equal]0 } 
    When checking non-emptiness, this List is turned into a conjunction by Apply[And, _ ] *)
Do[
S = Append[S, Append[state, p>0]];
S = Append[S, Append[state, p==0]];
S = Append[S, Append[state, p<0]],
{state,states}
];

MAP=OptionValue[Parallel]/.{True-> ParallelMap, _->Map};

(* Filter out empty sets *)
S=Complement[MAP[If[TrueQ[
TimeConstrained[
Reduce[ForAll[vars,Not[Apply[And,#]]],Reals], OptionValue[TimeoutValue], True]
],False,#]&, S],{False}];

(* Pass non-empty states to the next iteration, removing the first polynomial from the list *)
SignPartition[S,Rest[polynomials],vars]
]


(* Syntactically check whether two given states are neighbourging *)
NeighbouringStatesQ[state1_List, state2_List]:=Module[{},

If[(Length[state1]<2 || Length[state2]<2) || Length[state1]!=Length[state2] || state1==state2, Return[False]];

(* Get sign conditions for polynomials in A. First element in state1 and state2 is always the domain constraint H. *)
signcond1=Rest[state1];
signcond2=Rest[state2];

(* Align the corresponding sign conditions: this relies on the ordering from the construction process *)
pairs = Transpose[{signcond1,signcond2}];

(* For each pair of sign conditions check that 0 cannot be skipped, i.e. cannot be neighbouring if p>0 is next to p<0 *)
Apply[And,
 Map[Function[ a,
  Not[ (MatchQ[a,{Greater[p_,0],Less[p_,0]}]) || (MatchQ[a,{Less[p_,0],Greater[p_,0]}]) ] 
 ],pairs]]
]


(* Construct the neighbouring transition relation T_n *)
Options[ConnectNeighbours]={Parallel->False};
ConnectNeighbours[states_List, opts:OptionsPattern[]]:=Module[{},

(* Start with an empty neighbour transition relation *)
Tn ={};

DistributeDefinitions[NeighbouringStatesQ];

MAP=OptionValue[Parallel]/.{True-> ParallelMap, _->Map};

(* For each state compute its neighbours and add the corresponding 
   transition to the neighbour transition relation *)
(* Parallel implementation *)
Do[
Tn=Union[Tn,Complement[MAP[ If[NeighbouringStatesQ[state,# ], state -> #, False ]&,
states],{False}]]
,{state,states}];

Print["Number of neighbouring transitions: ", Length[Tn]];

(* Return graph *)
Graph[states,Tn]
]


(* /// TRANSITION REMOVAL METHODS SECTION /// *)


Options[ValidateTransitionLZZvanilla]={TimeoutValue->5}
ValidateTransitionLZZvanilla[transition_DirectedEdge, f_List, vars_List, opts:OptionsPattern[]]:=Module[{
state1=Simplify[Apply[And,transition[[1]]],Reals],
state2=Simplify[Apply[And,transition[[2]]],Reals]
},
(* Apply Liu-Zhan-Zhao conditions to decide if a discrete transition between states is impossible *)
Print["Validating transition ", transition];
If[TrueQ[  
TimeConstrained[
InvS[state1, f,vars, Simplify[(state1 || state2),Reals]], OptionValue[TimeoutValue], False
]
], False, transition ]
]


ValidateTransitionLZZopt[transition_DirectedEdge, f_List, vars_List]:=Module[{
state1=transition[[1]],
state2=transition[[2]]
},
s1=Apply[And, state1];
s2=Apply[And, state2];
(* Get sign conditions for polynomials in A *)
signcond1=Rest[state1];
signcond2=Rest[state2];

(* Otherwise, align the corresponding sign conditions: this relies on the ordering from the construction process *)
pairs = Transpose[{signcond1,signcond2}];

(* Pairs converted to True if the transition can be removed using LZZ *)
condition = pairs/.{
{p_<0, p_==0} :> TrueQ[InvS[p<0, f,vars, Simplify[(s1 || s2),Reals]]], 
{p_>0, p_==0} :> TrueQ[InvS[p>0, f,vars, Simplify[(s1 || s2),Reals]]], 
{p_==0, p_<0} :> TrueQ[InvS[p==0, f,vars, Simplify[(s1 || s2),Reals]]], 
{p_==0, p_>0} :>  TrueQ[InvS[p==0, f,vars, Simplify[(s1 || s2),Reals]]],
{p_==0, p_==0} :> False,
{p_>0, p_>0} :> False,
{p_<0, p_<0} :> False,
{p_<0, p_>0} :> False,
{p_>0, p_<0} :> False
};
condition=Apply[Or,condition];

If[TrueQ[Reduce[condition, Reals]], False, transition]
]


ValidateTransitionDI[transition_DirectedEdge, f_List, vars_List]:=Module[{
state1=transition[[1]],
state2=transition[[2]]
},
context=Or[Apply[And, state1], Apply[And, state2]];
(* Get sign conditions for polynomials in A *)
signcond1=Rest[state1];
signcond2=Rest[state2];

(* Otherwise, align the corresponding sign conditions: this relies on the ordering from the construction process *)
pairs = Transpose[{signcond1,signcond2}];

(* Pairs converted to True if the transition can be removed using DI *)
condition = pairs/.{
{p_<0, p_==0} :> Implies[context,LD[p,f,vars]<=0], 
{p_>0, p_==0} :> Implies[context,LD[p,f,vars]>=0], 
{p_==0, p_<0} :> Implies[context,LD[p,f,vars]>=0 ], 
{p_==0, p_>0} :> Implies[context,LD[p,f,vars]<=0 ],
{p_==0, p_==0} :> False,
{p_>0, p_>0} :> False,
{p_<0, p_<0} :> False,
{p_<0, p_>0} :> False,
{p_>0, p_<0} :> False
};
condition=Apply[Or,condition];

If[TrueQ[Reduce[condition, Reals]], False, transition]
]


ValidateTransitionTiwari[transition_DirectedEdge, f_List, vars_List]:=Module[{
state1=transition[[1]],
state2=transition[[2]]
},
context=Apply[And, state1];
(* Get sign conditions for polynomials in A *)
signcond1=Rest[state1];
signcond2=Rest[state2];

(* Otherwise, align the corresponding sign conditions: this relies on the ordering from the construction process *)
pairs = Transpose[{signcond1,signcond2}];

(* Tiwari, FMSD'08, p 11. *)
(* Pairs converted to True if the transition can be removed using Tiwari's abstraction method *)
condition = pairs/.{
{p_<0, p_==0} :> Implies[context,LD[p,f,vars]<=0], 
{p_>0, p_==0} :> Implies[context,LD[p,f,vars]>=0], 
{p_==0, p_<0} :> Implies[context,LD[p,f,vars]>0 ] || Implies[context,LD[p,f,vars]==0 ], 
{p_==0, p_>0} :> Implies[context,LD[p,f,vars]<0 ] || Implies[context,LD[p,f,vars]==0 ],
{p_==0, p_==0} :> False,
{p_>0, p_>0} :> False,
{p_<0, p_<0} :> False,
{p_<0, p_>0} :> False,
{p_>0, p_<0} :> False
};
condition=Apply[Or,condition];

If[TrueQ[Reduce[condition, Reals]], False, transition]
]


ValidateTransitionTiwariStrict[transition_DirectedEdge, f_List, vars_List]:=Module[{
state1=transition[[1]],
state2=transition[[2]]
},
context=Apply[And, state1];
(* Get sign conditions for polynomials in A *)
signcond1=Rest[state1];
signcond2=Rest[state2];

(* Otherwise, align the corresponding sign conditions: this relies on the ordering from the construction process *)
pairs = Transpose[{signcond1,signcond2}];

(* Restricted version of Tiwari, FMSD'08, p 11. *)
(* Pairs converted to True if the transition can be removed using a restricted version of Tiwari's abstraction method *)
condition = pairs/.{
{p_<0, p_==0} :> Implies[context,LD[p,f,vars]<=0], 
{p_>0, p_==0} :> Implies[context,LD[p,f,vars]>=0], 
{p_==0, p_<0} :> Implies[context,LD[p,f,vars]>0 ], 
{p_==0, p_>0} :> Implies[context,LD[p,f,vars]<0 ],
{p_==0, p_==0} :> False,
{p_>0, p_>0} :> False,
{p_<0, p_<0} :> False,
{p_<0, p_>0} :> False,
{p_>0, p_<0} :> False
};
condition=Apply[Or,condition];

If[TrueQ[Reduce[condition, Reals]], False, transition]
]


(* \\\ END OF TRANSITION REMOVAL METHODS SECTION \\\ *)


Options[ValidateAllTransitions]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False};

(* Validating all transitions *)
ValidateAllTransitions[graph_Graph, f_List, vars_List, opts:OptionsPattern[]]:=Module[
{S=VertexList[graph],Tn=EdgeList[graph]},

(* Make sure ParallelMap is able to work *)
DistributeDefinitions[
	ValidateTransitionTiwari,
	ValidateTransitionTiwariStrict,
	ValidateTransitionDI,
	ValidateTransitionLZZvanilla,
	ValidateTransitionLZZopt
	];

MAP=OptionValue[Parallel]/.{True-> ParallelMap, _->Map};

(* Use the selected way of removing discrete transitions to construct the transition relation T from Tn *)
T=OptionValue[TransitionRemovalMethod]/.{
"Tiwari-FMSD"          -> Complement[MAP[ValidateTransitionTiwari[#,f,vars]&, Tn],{False}],
"Tiwari-FMSD-strict"   -> Complement[MAP[ValidateTransitionTiwariStrict[#,f,vars]&, Tn],{False}],
"Tiwari-DI"            -> Complement[MAP[ValidateTransitionDI[#,f,vars]&, Tn],{False}],
"LZZ-vanilla"          -> Complement[MAP[ValidateTransitionLZZvanilla[#,f,vars]&, Tn],{False}],
"LZZ-opt"              -> Complement[MAP[ValidateTransitionLZZopt[#,f,vars]&, Tn],{False}],
                     _ -> Tn
};

(* Return a transition system in which every transition has been validated *)
Graph[S,Complement[T,{False}],

(* Display options *)
VertexLabels->"Name",
VertexLabelStyle->Large,
VertexSize->Smaller[Medium],
VertexStyle->Directive[White],
BaseStyle->Directive[Thick,Black]]
]


Options[ConvertToFormulas]={Parallel->False};

ConvertToFormulas[graph_Graph, opts:OptionsPattern[]]:=Module[
{S=Map[Apply[And,#]&,VertexList[graph]],
T=EdgeList[graph]},

MAP=OptionValue[Parallel]/.{True-> ParallelMap, _->Map};

Tform=MAP[DirectedEdge[Apply[And,#[[1]]], Apply[And,#[[2]]]]&, T];

(* Return a transition system in which every transition has been validated *)
Graph[S,Complement[Tform,{False}],
(* Display options *)
VertexLabels->"Name",
VertexLabelStyle->Large,
VertexSize->Smaller[Medium],
VertexStyle->Directive[White],
BaseStyle->Directive[Thick,Black]]
]


Options[Abstraction]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False};

Abstraction[f_List,vars_List,H_,p_List, opts:OptionsPattern[]]:=Module[{},
S=SignPartition[{{H}},p,vars, Parallel->OptionValue[Parallel]];
Tn=ConnectNeighbours[S, Parallel->OptionValue[Parallel]];
graph=ValidateAllTransitions[Tn, f, vars,
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel]
];
ConvertToFormulas[graph, Parallel->OptionValue[Parallel]]
]


Options[AbstractInitialStates]={Parallel->False, TimeoutValue->Infinity};
AbstractInitialStates[graph_Graph, init_, opts:OptionsPattern[]]:=Module[{S=VertexList[graph]},

MAP=OptionValue[Parallel]/.{True-> ParallelMap, _->Map};

(* Check if a discrete state intersects the initial set of statesin parallel *)
initialStates=Complement[MAP[ If[TrueQ[TimeConstrained[
Reduce[Not[Apply[And,#] && init],Reals], OptionValue[TimeoutValue], False]], False, #]&, S],{False}];

(* Return the result *)
initialStates
]


(* Generate continuous invariant by computing the reachable set from the initial states in the full abstraction *)
Options[GenerateInvariant]={Parallel->False};
GenerateInvariant[graph_Graph, init_, opts:OptionsPattern[]]:=Module[{},
initialStates=AbstractInitialStates[graph,init, Parallel->OptionValue[Parallel]];
reachable=VertexOutComponent[graph,initialStates];
Apply[Or,reachable]
]


(* Returns a pair of the reachable set in the abstraction and the number of discrete states in this reachable set *)
ReachableStates[graph_Graph, init_]:=Module[{},
initialStates=AbstractInitialStates[graph,init];
inv=VertexOutComponent[graph,initialStates];
size=Length[inv];
If[size==0,Return[{0,False}]];
{size,If[size>1,FullSimplify[Apply[Or,inv],Reals],inv[[1]]]}
]


(* NON-LINEAR AND DISCRETE QUALITATIVE ABSTRACTION-BASED METHODS *)


Options[LazyReach]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->Simplify, WorkingPrecision -> \[Infinity] };

LazyReach[precond_, postcond_, system_List, A_List, opts:OptionsPattern[]]:=Module[{ f= system[[1]], vars=system[[2]], H=system[[3]] },
SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

Print["LazyReach with ", Length[A], " abstraction polynomials (at most ", 3^Length[A], " discrete states and ", 7^Length[A] -3^Length[A], " neighbouring transitions)."];

(* Compute the discretization and the neighbouring transition relation Tn *)
S=SignPartition[{{H}},A,vars, Parallel->OptionValue[Parallel]];
Tn=ConnectNeighbours[S, Parallel->OptionValue[Parallel]];

(* Mark the initial states as already visited  and no states as processed *)
Visited=AbstractInitialStates[Tn,precond, Parallel->OptionValue[Parallel]];
Processed={};

(* Function for computing the List of outgoing transitions from a given state *)
OutgoingTrans=Function[{graph,s},EdgeList[EdgeDelete[NeighborhoodGraph[graph,{s},1], Except[DirectedEdge[s,_]]]]];

(* Main worklist loop *)
While[Length[Processed] < Length[Visited],

(* Get visited states from last iteration for processing *)
Unprocessed=Complement[Visited,Processed];
Processed=Visited;

(* Compute the List of all potential outgoing transitions from unprocessed visited states *)
NextFromUnprocessed=Flatten[Map[OutgoingTrans[Tn,#]&,Unprocessed]];

(* Filter to all potential outgoing transitions from unprocessed visited to unvisited states only *)
Validate=If[Length[NextFromUnprocessed]>0,
Complement[Map[Function[{trans},If[MemberQ[Visited,trans[[2]]], False,trans]], NextFromUnprocessed], {False}],
{}];

(* Remove processed transitions from the transition relation *)
(* Tn=EdgeDelete[Tn,NextFromUnprocessed]; *)

(* Uncomment to see the states and transitions being processed
Print[Visited];
Print[Validate];
*)

(* Validate the potential outgoing transitions to unvisited states and
   add the reachable states to the set of visited states*)
Reachable=Graph[
           EdgeList[
            ValidateAllTransitions[Graph[Validate],f,vars,
              TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
              Parallel->OptionValue[Parallel]]]];

Visited = Union[Visited, VertexList[Reachable]];
];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> StandardForm};

(* Return the union of all the visited states *)
If[Length[Visited]==0, False, Simplify[Apply[Or, Map[Apply[And, #]&,Visited]],Reals]]
]


Options[EagerReach]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->Simplify, WorkingPrecision -> \[Infinity]};

EagerReach[precond_, postcond_, system_List, A_List, opts:OptionsPattern[]]:=Module[{f= system[[1]],vars=system[[2]],H=system[[3]]},
SetOptions[Reduce, WorkingPrecision-> OptionValue[WorkingPrecision]];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> StandardForm};

SIMPLIFY[
  GenerateInvariant[
	Abstraction[f,vars,H,A, TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], Parallel->OptionValue[Parallel] ],
	precond, Parallel->OptionValue[Parallel]]]
]


Options[DWC]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->Simplify, WorkingPrecision -> \[Infinity]};

DWC[precond_, postcond_, system_List, A0_List, opts:OptionsPattern[]]:=Catch[
Module[{GT,EQ,LT,p,f=system[[1]],vars=system[[2]],H0=system[[3]]},

SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWC, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> StandardForm};

(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[TrueQ[Reduce[ForAll[vars,Not[H0 && precond]],vars,Reals]], Throw[False] ]; 

(* DW check *)
If[TrueQ[Reduce[ForAll[vars,Implies[H0, postcond]],vars,Reals]], Throw[H0] ]; 

(* Main loop *)
Do[p=Simplify[A0[[i]],H0];

(* DC check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>=0]],vars,Reals]]) && (TrueQ[InvS[p>=0, f, vars, H0]]),
Print["DC on ", p>=0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p>=0), Reals]}, Delete[A0,i]]]
];

(* DC check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<=0]],vars,Reals]]) && (TrueQ[InvS[p<=0, f, vars, H0]]),
Print["DC on ", p<=0];
Throw[DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p<=0), Reals]}, Delete[A0,i]]]
];

(* DDC check 
If[TrueQ[TrueQ[InvS[p==0, f, vars, H0]] && TrueQ[InvS[p==0, -f, vars, H0]]],
Print["DDC on ", p==0];
GT=DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p<0 ), Reals]},Delete[A0,i]];
EQ=DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p==0), Reals]},Delete[A0,i]];
LT=DWC[precond,postcond,{f,vars, SIMPLIFY[(H0 && p>0 ), Reals]},Delete[A0,i]];

(* Combine reachable sets of the sub-systems *)
Throw[SIMPLIFY[(GT || EQ || LT),Reals]]

]; *)

,{i,1,Length[A0]}]; (* End of main loop *)

Print["No more cuts ... "];

Throw[H0]
]]


Options[DWCLZR]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->FullSimplify, WorkingPrecision -> \[Infinity]};

DWCLZR[precond_, postcond_, system_List, A0_List, opts:OptionsPattern[]]:=Catch[
Module[{GT,EQ,LT,p,f=system[[1]],vars=system[[2]],H0=system[[3]]},

SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DWCLZR, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];


(* Sufficiency check: No evolution from the initial set, so no reachable set *)
If[TrueQ[Reduce[ForAll[vars,Not[H0 && precond]],vars,Reals]], Throw[False] ]; 

(* DW check *)
If[TrueQ[Reduce[ForAll[vars,Implies[H0, postcond]],vars,Reals]], Throw[H0] ]; 

(* Main loop *)
Do[p=A0[[i]];

(* DC check 1 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>0]],vars,Reals]]) && (TrueQ[InvS[p>0, f, vars, H0]]),
Print["DC on ", p>0];
Throw[DWCLZR[precond,postcond,{f,vars,(H0 && p>0)}, Delete[A0,i]]]
];

(* DC check 2 *)
If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<0]],vars,Reals]]) && (TrueQ[InvS[p<0, f, vars, H0]]),
Print["DC on ", p<0];
Throw[DWCLZR[precond,postcond,{f,vars, (H0 && p<0)}, Delete[A0,i]]]
];

(* DDC check 
If[TrueQ[TrueQ[InvS[p==0, f, vars, H0]] && TrueQ[InvS[p==0, -f, vars, H0]]],
Print["DDC on ", p==0];
GT=DWCLZR[precond,postcond,{f,vars, (H0 && p<0 )},Delete[A0,i]];
EQ=DWCLZR[precond,postcond,{f,vars, (H0 && p==0)},Delete[A0,i]];
LT=DWCLZR[precond,postcond,{f,vars, (H0 && p>0 )},Delete[A0,i]];

(* Combine reachable sets of the sub-systems *)
Throw[(GT || EQ || LT)]

]; *)
,{i,1,Length[A0]}]; (* End of main loop *)

Print["No more cuts. Trying LazyReach with |A|=",Length[A0]];

Throw[LazyReach[precond,postcond,{f,vars,H0},A0, 
		TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
		Parallel->OptionValue[Parallel],
		WorkingPrecision-> OptionValue[WorkingPrecision] ]]
]]


Options[DCLoop]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->FullSimplify, WorkingPrecision -> \[Infinity]};

DCLoop[precond_, postcond_, system_List, A0_List, opts:OptionsPattern[]]:=Catch[
Module[{GT,EQ,LT,p,f=system[[1]],vars=system[[2]],H0=system[[3]]},

SetOptions[Reduce,WorkingPrecision-> OptionValue[WorkingPrecision]];

SetOptions[DCLoop, 
	TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
	Parallel->OptionValue[Parallel],
	WorkingPrecision-> OptionValue[WorkingPrecision] ];

(* Sufficiency check 1: No evolution from the initial set, so no reachable set *)
If[TrueQ[Reduce[ForAll[vars,Not[H0 && precond]],vars,Reals]],Throw[False]]; 

(* Sufficiency check 2: Apply DW *)
If[TrueQ[Reduce[ForAll[vars,Implies[H0, postcond]],vars,Reals]],Throw[H0]]; 

Do[p=Simplify[A0[[i]], H0];

If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p>0]],vars,Reals]]) && (TrueQ[InvS[p>0, f, vars, H0]]),
Print["DC on ", p>0];
Throw[DCLoop[precond,postcond,{f,vars,Simplify[(H0 && p>0), Reals]},Delete[A0,i]]];
];

If[(TrueQ[Reduce[ForAll[vars,Implies[H0 && precond, p<0]],vars,Reals]]) && (TrueQ[InvS[p<0, f, vars, H0]]),
Print["DC on ", p<0];
Throw[DCLoop[precond,postcond,{f,vars,Simplify[(H0 && p<0), Reals]},Delete[A0,i]]];
];

(* DDC optional
If[TrueQ[InvS[p==0, f, vars, H0]] && TrueQ[InvS[p==0, -f, vars, H0]],
Print["DDC on ", p==0];
GT=DCLoop[precond,postcond,{f,vars, Simplify[(H0 && p<0), Reals]},Delete[A0,i]];
EQ=DCLoop[precond,postcond,{f,vars, Simplify[(H0 && p==0), Reals]},Delete[A0,i]];
LT=DCLoop[precond,postcond,{f,vars, Simplify[(H0 && p>0), Reals]},Delete[A0,i]];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> StandardForm};
(* Combine reachable sets of the sub-systems *)
Throw[SIMPLIFY[(GT || EQ || LT),Reals]]
]; *)
,{i,1,Length[A0]}];

Throw[LazyReach[precond,postcond,{f,vars,H0},A0, 
		TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], 
		Parallel->OptionValue[Parallel],
		WorkingPrecision-> OptionValue[WorkingPrecision] ]]
]]


(* One-dimensional methods *)


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


OneDimPotential[problem_List]:=Module[{},
(* Pattern match problem input *)
{Init,{{f},{statevar},Q},Postcond} = problem;
potentialFn=-Integrate[f, statevar];
k=MaxValue[{potentialFn,Init},statevar];
-Integrate[f, statevar]<=k
]


End[]
EndPackage[]
