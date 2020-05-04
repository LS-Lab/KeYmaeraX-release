(* ::Package:: *)

(* Classifier for continuous safety verification problems. Rev 2.0. *)


BeginPackage["Classifier`"];


SystemDimension::"Return the size n of the system, or 0 if the system is malformed.";
ConstantSystemQ::"Check whether the system of ODEs has constant right-hand sides.";
LinearSystemQ::"Check whether the system of ODEs is linear.";
NilpotentSystemQ::"Check whether the system of ODEs is nilpotent linear.";
AffineSystemQ::"Check whether the system of ODEs is affine.";
MultiAffineSystemQ::"Check whether the system of ODEs is multi-affine.";
PolynomialSystemQ::"Check whether the system of ODEs is polynomial.";
HomogeneousSystemQ::"Check whether a given polynomial is homogeneous in the given variables.";
MaxSystemDegree::"Return the maximum polynomial degree of the right-hand side in the system of ODEs.";
NonLinPolySystemQ::"Check whether the system of ODEs is non-linear.";
ClassifyProblem::"Classify a given safety verification problem.";
AlgebraicPreQ::"Check whether the precondition is an algebraic set.";
AlgebraicPostQ::"Check whether the postcondition is an algebraic set.";
AlgebraicEvoConstQ::"Check whether the evolution domain constraint is an algebraic set.";
BoundedInitQ::"Check whether the initial set of states in the problem is bounded.";
BoundedUnsafeQ::"Check whether the unsafe set of states in the problem is bounded.";
BoundedEvoConstQ::"Check whether the evolution domain constraint in the problem is bounded.";
BoundedTimeProblemQ::"Determine whether the problem is bounded in time (i.e. 'time-triggered').";


Begin["`Private`"]


SystemDimension[vectorField_List, vars_List]:=Module[{},
If[TrueQ[Length[vars]==Length[vectorField]], Length[vars], 0]
]


ConstantSystemQ[vectorField_List, vars_List]:=Module[{zeroVector=Map[Function[X,0],vars]},
TrueQ[Grad[vectorField,vars].vars == zeroVector]
]


LinearSystemQ[vectorField_List, vars_List]:=Module[{},
TrueQ[Grad[vectorField,vars].vars == vectorField]
]


(* Check if the system matrix is nilpotent *)
NilpotentSystemQ[vectorField_List, vars_List]:=Module[{M},
If[LinearSystemQ[vectorField,vars], 
M=Grad[vectorField,vars];
TrueQ[First[Eigenvalues[M]//DeleteDuplicates]==0],
False]
]


PolynomialSystemQ[vectorField_List, vars_List]:=Module[{},
Apply[And,Map[PolynomialQ[#, vars]&, vectorField]]
]


MaxPolyDegree[polynomial_, vars_List]:=Module[{},
If[TrueQ[polynomial==0],
0,
Max[Map[Apply[Plus,#]&,Map[Exponent[#,vars]&,MonomialList[polynomial]]]]]
]


MaxSystemDegree[vectorField_List, vars_List]:=Module[{},
Max[Map[MaxPolyDegree[#, vars]&, vectorField]]
]


AffineSystemQ[vectorField_List, vars_List]:=Module[{},
If[TrueQ[PolynomialSystemQ[vectorField,vars]],
TrueQ[MaxSystemDegree[vectorField,vars]<=1], 
False]
]


MultiAffineSystemQ[vectorField_List, vars_List]:=Module[{},
If[TrueQ[PolynomialSystemQ[vectorField,vars]],
AllTrue[Map[MaxSystemDegree[vectorField,{#}]<=1&, vars], TrueQ], 
False]
]


MonomialExponents[polynomial_, vars_List]:=Module[{},
Map[Apply[Plus,#]&,Map[Exponent[#,vars]&,MonomialList[polynomial]]]
]


HomogeneousSystemQ[vectorField_List, vars_List]:=Module[{},
If[TrueQ[PolynomialSystemQ[vectorField,vars]],
TrueQ[Length[DeleteDuplicates[Flatten[Map[MonomialExponents[#,vars]&,vectorField]]]]==1], 
False]
]


NonLinPolySystemQ[vectorField_List, vars_List]:=Module[{},
TrueQ[MaxSystemDegree[vectorField,vars]>1]
]


RationalFunctionQ[expr_,vars_List]:=Module[{factor=Factor[expr],numerator,denominator},
numerator=Numerator[factor];
denominator=Denominator[factor];
If[Not[PolynomialQ[numerator,vars] && PolynomialQ[denominator,vars]], False,
Not[TrueQ[denominator==0]]
]
]


(* Set and formula classification section *)


AtomicFormulaQ[form_]:=Module[{},
(* Atomic formulas that don't feature \[NotEqual] *)
AnyTrue[{True,False,Greater,Less,Equal,LessEqual,GreaterEqual},TrueQ[Head[form]==#]&]
]


(* Determine if a given formula is a conjunction *)
ConjunctiveFormulaQ[form_]:=Catch[Module[{},
(* Atomic formulas that don't feature \[NotEqual] are not considered conjunctive, though this may be controversial *)
If[AtomicFormulaQ[form], Throw[False]];
(* If the top level connective in the DNF is &&, then the formula is a conjunction *)
Throw[If[TrueQ[Head[BooleanMinimize[form/.{Unequal[lhs_,rhs_]:>lhs-rhs>0 || lhs-rhs<0},"DNF"]]==And],
True, False]]
]]


(* Determine if a given formula is a disjunction *)
DisjunctiveFormulaQ[form_]:=Catch[Module[{},
If[TrueQ[Head[form]==Unequal],Throw[True]];
(* Atomic formulas that don't feature \[NotEqual] are not disjunctive *)
If[AtomicFormulaQ[form], Throw[False]];
(* If the top level connective in the CNF is ||, then the formula is a disjunction *)
Throw[If[TrueQ[Head[BooleanMinimize[form/.{Unequal[lhs_,rhs_]:>lhs-rhs>0 || lhs-rhs<0},"CNF"]]==Or],
True, False]]
]]


(* Wrapper function to determine whether a formula features any of the undesirable symbols supplied in a list *)
FormulaFreeQ[form_, undesirable_List]:=Module[{},
Map[ 
FreeQ[BooleanMinimize[Simplify[form]/.{Unequal[lhs_,rhs_]:>lhs-rhs>0 || lhs-rhs<0},"DNF"],#]&,
(* N.B. With this implementation we are at the mercy of the simplifier and may get conservative results *)
(* Alternative would be to convert to DNF and simplify conjunctive clauses ourselves *)
undesirable
]//AllTrue[#,TrueQ]&
]


EquationalFormulaQ[form_]:=FormulaFreeQ[form,{Less,Greater,Unequal,GreaterEqual,LessEqual}]
ClosedFormulaQ[form_]:=FormulaFreeQ[form,{Less,Greater,Unequal}]
OpenFormulaQ[form_]:=FormulaFreeQ[form,{LessEqual,GreaterEqual,Equal}]


(* Check whether an expression is a formula describing an algebraic set *)
AlgebraicSetQ[S_]:=EquationalFormulaQ[S]


AlgebraicProblemWrapper[problem_List, part_]:=Module[{pre,post,vectorField,vars,evoConstraint},
(* Pattern match fields in the problem *)
{ pre, { vectorField, vars, evoConstraint }, post } = problem;
AlgebraicSetQ[part/.{
"precondition"-> pre, 
"postcondition"-> post, 
"evolution constraint"-> evoConstraint, 
_ -> vars[[1]]<0} (* default non-algebraic set *)
]
]


AlgebraicPreQ[problem_List]:=AlgebraicProblemWrapper[problem, "precondition"]
AlgebraicPostQ[problem_List]:=AlgebraicProblemWrapper[problem, "postcondition"]
AlgebraicEvoConstQ[problem_List]:=AlgebraicProblemWrapper[problem, "evolution constraint"]


BoundedSetQ[expr_, vars_List]:=Module[{},
BoundedRegionQ[ImplicitRegion[expr, vars]]
]


(* Wrapper function for checking whether sets in the verification problem are bounded or not *)
BoundedProblemWrapper[problem_List, part_]:=Module[{pre,post,vectorField,vars,evoConstraint},
(* Pattern match fields in the problem *)
{ pre, { vectorField, vars, evoConstraint }, post } = problem;
BoundedSetQ[part/.{
"initial"-> (pre && evoConstraint), 
"unsafe"-> (Not[post] && evoConstraint), 
"evolution constraint"-> evoConstraint, 
_ -> True} (* default unbounded set *)
,vars]
]


(* Functions for determining whether initial and unsafe sets and the evolution constraint are bounded *)
BoundedInitQ[problem_List]:=BoundedProblemWrapper[problem,"initial"]
BoundedUnsafeQ[problem_List]:=BoundedProblemWrapper[problem,"unsafe"]
BoundedEvoConstQ[problem_List]:=BoundedProblemWrapper[problem,"evolution constraint"]


(* Compute the maximum value that a function can attain in a region described by a given formula *)
MaxValueInRegion[function_, regionFormula_, vars_List]:=Module[{},
MaxValue[function,vars\[Element]ImplicitRegion[ regionFormula,vars]]
]
(* Compute the minimum value that a function can attain in a region described by a given formula *)
MinValueInRegion[function_, regionFormula_, vars_List]:=Module[{},
MinValue[function,vars\[Element]ImplicitRegion[ regionFormula,vars]]
]


(* Recognizing bounded time problems - sometimes (confusingly) called 'time-triggered' problems *)
BoundedTimeProblemQ[problem_List]:=Catch[Module[{pre,post,vectorField,vars,evoConstraint,
clockVars,posClocks, negClocks},
(* Initialize the fields in the problem *)
{ pre, { vectorField, vars, evoConstraint }, post } = problem;
(* Determine the 'clock variables' in the system, i.e. those variables whose rate of change is a numeric non-zero constant *)
clockVars =  Select[Select[{vectorField,vars}//Transpose, Element[#[[1]], Reals]&], TrueQ[#[[1]]!=0//FullSimplify]&];
posClocks=#[[2]]&/@Select[clockVars, #[[1]]>0&];
negClocks=#[[2]]&/@Select[clockVars, #[[1]]<0&];

(* If any of the clock variables are bounded within the constraint, the problem is bounded in time *)
Throw[
Min[Abs /@
Union[
Map[MaxValueInRegion[#, evoConstraint,vars]&,posClocks],
Map[MinValueInRegion[#, evoConstraint,vars]&,negClocks]
]]//NumericQ ];
]]


ClassifyProblem[problem_List]:=Module[{pre,post,vectorField,vars,evoConstraint,
classCheck,systemHierarchy,classEval,classGraph,isSink, odeDim, odeKind, 
boundedInit, boundedUnsafe, boundedEvoConst, algebraicPre, algebraicPost,
algebraicEvoConst, boundedTime, booleanStructPre, booleanStructPost, 
booleanStructEvoConst, topologyPre, topologyPost, topologyEvoConst},

(* Pattern match fields in the problem *)
{ pre, { vectorField, vars, evoConstraint }, post } = problem;

systemHierarchy=Graph[
(* vertices *) {
"Constant",
"Linear",
"Affine",
"Multi-affine",
"Homogeneous",
"Polynomial",
"Non-polynomial"
},
(* edges     SOURCE   \[Rule]   DESTINATION *) {
DirectedEdge["Affine",        "Constant"],
DirectedEdge["Affine",        "Linear"],
DirectedEdge["Multi-affine",  "Affine"],
DirectedEdge["Homogeneous",   "Linear"],
DirectedEdge["Homogeneous",   "Constant"],
DirectedEdge["Polynomial",    "Homogeneous"],
DirectedEdge["Polynomial",    "Multi-affine"]
}, VertexLabels->"Name"
];

classEval[CHECK_, IFTRUE_]:=If[TrueQ[CHECK],IFTRUE,False];

classCheck={
"Constant"      :> classEval[ConstantSystemQ[vectorField,vars],       "Constant"],
"Linear"        :> classEval[LinearSystemQ[vectorField,vars],         "Linear"],
"Affine"        :> classEval[AffineSystemQ[vectorField,vars],         "Affine"],
"Multi-affine"  :> classEval[MultiAffineSystemQ[vectorField,vars],    "Multi-affine"],
"Homogeneous"   :> classEval[HomogeneousSystemQ[vectorField,vars],    "Homogeneous"],
"Polynomial"    :> classEval[PolynomialSystemQ[vectorField,vars],     "Polynomial"],
"Non-polynomial":> classEval[Not[PolynomialSystemQ[vectorField,vars]],"Non-polynomial"]
};

(* Delete False node from the processed hierarchy graph *)
classGraph=VertexDelete[
Graph[
VertexList[systemHierarchy]//.classCheck, 
EdgeList[systemHierarchy]//.classCheck, 
VertexLabels->"Name"],  False];

(* Check if a node is a sink *)
isSink[node_, graph_Graph]:=TrueQ[VertexOutComponent[graph,{node}]=={node}];

(* Dimension of the system of ODEs *)
odeDim=SystemDimension[vectorField,vars];
(* A list of the most specific classification kinds in the hierarchy *)
odeKind=Select[VertexList[classGraph], isSink[#,classGraph]&];
(* Set boundedness checks *)
boundedInit=If[BoundedInitQ[problem], "Initial Set" -> "Bounded", "Initial Set" -> "Unbounded"];
boundedUnsafe=If[BoundedUnsafeQ[problem], "Unsafe Set" -> "Bounded", "Unsafe Set" -> "Unbounded"];
boundedEvoConst=If[BoundedEvoConstQ[problem], "Evolution Constraint" -> "Bounded", "Evolution Constraint" -> "Unbounded"];
(* Algebraic set checks *)
algebraicPre=If[AlgebraicPreQ[problem], "Precondition" -> "Algebraic", "Precondition" -> "Semi-algebraic"];
algebraicPost=If[AlgebraicPostQ[problem], "Postcondition" -> "Algebraic", "Postcondition" -> "Semi-algebraic"];
algebraicEvoConst=If[AlgebraicEvoConstQ[problem], "Evolution Constraint" -> "Algebraic", "Evolution Constraint" -> "Semi-algebraic"];
(* Boolean structure checks *)
booleanStructPre=If[AtomicFormulaQ[pre], "Precondition" -> "Atomic",
(* else if *) If[ConjunctiveFormulaQ[pre], "Precondition" -> "Conjunctive",
(* else if *) If[DisjunctiveFormulaQ[pre], "Precondition" -> "Disjunctive",
(* else *)    "Precondition" -> "General"]
]];
booleanStructPost=If[AtomicFormulaQ[post], "Postcondition" -> "Atomic",
(* else if *) If[ConjunctiveFormulaQ[post], "Postcondition" -> "Conjunctive",
(* else if *) If[DisjunctiveFormulaQ[post], "Postcondition" -> "Disjunctive",
(* else *)    "Postcondition" -> "General"]
]];
booleanStructEvoConst=If[AtomicFormulaQ[evoConstraint], "Evolution Constraint" -> "Atomic",
(* else if *) If[ConjunctiveFormulaQ[evoConstraint], "Evolution Constraint" -> "Conjunctive",
(* else if *) If[DisjunctiveFormulaQ[evoConstraint], "Evolution Constraint" -> "Disjunctive",
(* else *)    "Evolution Constraint" -> "General"]
]];
(* Topological checks *)
topologyPre=If[TrueQ[pre==True || pre==False], "Precondition" -> "Clopen",
(* else if *)If[OpenFormulaQ[pre], "Precondition" -> "Open",
(* else if *) If[ClosedFormulaQ[pre], "Precondition" -> "Closed",
(* else *)    "Precondition" -> "Neither"]
]];
topologyPost=If[TrueQ[post==True || post==False], "Postcondition" -> "Clopen",
(* else if *)If[OpenFormulaQ[post], "Postcondition" -> "Open",
(* else if *) If[ClosedFormulaQ[post], "Postcondition" -> "Closed",
(* else *)    "Postcondition" -> "Neither"]
]];
topologyEvoConst=If[TrueQ[evoConstraint==True || evoConstraint==False], "Evolution Constraint" -> "Clopen",
(* else if *) If[OpenFormulaQ[evoConstraint], "Evolution Constraint" -> "Open",
(* else if *) If[ClosedFormulaQ[evoConstraint], "Evolution Constraint" -> "Closed",
(* else *)    "Evolution Constraint" -> "Neither"]
]];

boundedTime=If[BoundedTimeProblemQ[problem], "Time" -> "Bounded", "Time" -> "Unbounded"];

(* Return classification as a list *)
{odeDim, (* The first element is always the ODE system dimension *)
odeKind, (* The second element is a list describing the kind of ODE in the right-hand side *)
(* The third element is a list giving a summary of the features of the verification problem *)
{ "Boundedness" -> {boundedInit, boundedUnsafe, boundedEvoConst},  (* boundedness checks *)
  "Algebraity" -> {algebraicPre, algebraicPost, algebraicEvoConst}, (* 'algebraicity' checks *)
  "Boolean Structure" -> {booleanStructPre, booleanStructPost, booleanStructEvoConst}, (* boolean formula structure checks *)
  "Topology" -> {topologyPre, topologyPost, topologyEvoConst}, (* topological checks *)
  "Space Boundedness" -> {boundedTime} (* time boundedness check *)}
}
]


End[]


EndPackage[]
