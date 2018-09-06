(* ::Package:: *)

Needs["LZZ`",NotebookDirectory[]<>"LZZ.m"] 


BeginPackage["DiscreteAbstraction`"];


Abstraction::usage="GenerateDiscreteAbstraction[f_List,vars_List,H_,p_List] 
    Generate a discrete abstraction of a continuous system."
    
LazyReach::usage="LazyReach[precond_, postcond_, system_List, A_List] 
    Lazily compute the continuous invariant by computing the reachable set in the abstraction from the initial set of states."

EagerReach::usage="EagerReach[precond_, postcond_, system_List, A_List] 
    Eagerly compute the continuous invariant by computing the full abstraction first and then generating the reachable set from the initial set of states."


Begin["`Private`"]


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


(* TRANSITION REMOVAL METHODS SECTION *)


Options[ValidateTransitionLZZvanilla]={TimeoutValue->5}
ValidateTransitionLZZvanilla[transition_DirectedEdge, f_List, vars_List, opts:OptionsPattern[]]:=Module[{
state1=Simplify[Apply[And,transition[[1]]],Reals],
state2=Simplify[Apply[And,transition[[2]]],Reals]
},
(* Apply Liu-Zhan-Zhao conditions to decide if a discrete transition between states is impossible *)
Print["Validating transition ", transition];
If[TrueQ[  
TimeConstrained[
LZZ`InvS[state1, f,vars, Simplify[(state1 || state2),Reals]], OptionValue[TimeoutValue], False
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
{p_<0, p_==0} :> TrueQ[LZZ`InvS[p<0, f,vars, Simplify[(s1 || s2),Reals]]], 
{p_>0, p_==0} :> TrueQ[LZZ`InvS[p>0, f,vars, Simplify[(s1 || s2),Reals]]], 
{p_==0, p_<0} :> TrueQ[LZZ`InvS[p==0, f,vars, Simplify[(s1 || s2),Reals]]], 
{p_==0, p_>0} :>  TrueQ[LZZ`InvS[p==0, f,vars, Simplify[(s1 || s2),Reals]]],
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


(* END OF TRANSITION REMOVAL METHODS SECTION *)


Options[ValidateAllTransitions]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False};

(* Validating all transitions *)
ValidateAllTransitions[graph_Graph, f_List, vars_List, opts:OptionsPattern[]]:=Module[
{S=VertexList[graph],Tn=EdgeList[graph]},

(* Make sure ParallelMap is able to work *)
DistributeDefinitions[
	ValidateTransitionTiwari,
	ValidateTransitionTiwariStrict,
	ValidateTransitionLZZvanilla,
	ValidateTransitionLZZopt
	];

MAP=OptionValue[Parallel]/.{True-> ParallelMap, _->Map};

(* Use the selected way of removing discrete transitions to construct the transition relation T from Tn *)
T=OptionValue[TransitionRemovalMethod]/.{
"Tiwari-FMSD"          -> Complement[MAP[ValidateTransitionTiwari[#,f,vars]&, Tn],{False}],
"Tiwari-FMSD-strict"   -> Complement[MAP[ValidateTransitionTiwariStrict[#,f,vars]&, Tn],{False}],
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


Options[EagerReach]={TransitionRemovalMethod->"LZZ-vanilla", Parallel->False, SimplifyInvariant->Simplify, WorkingPrecision -> \[Infinity]};

EagerReach[precond_, postcond_, system_List, A_List, opts:OptionsPattern[]]:=Module[{f= system[[1]],vars=system[[2]],H=system[[3]]},
SetOptions[Reduce, WorkingPrecision-> OptionValue[WorkingPrecision]];

SIMPLIFY=OptionValue[SimplifyInvariant]/.{FullSimplify-> FullSimplify, Simplify -> Simplify, _ -> StandardForm};

SIMPLIFY[
  GenerateInvariant[
	Abstraction[f,vars,H,A, TransitionRemovalMethod->OptionValue[TransitionRemovalMethod], Parallel->OptionValue[Parallel] ],
	precond, Parallel->OptionValue[Parallel]]]
]


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


End[]
EndPackage[]
