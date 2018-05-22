(* ::Package:: *)

(* Classifier for discriminating systems of ODEs. *)


BeginPackage["Classifier`"];


SystemDimension::"Return the size n of the system, or 0 if the system is malformed."
ConstantSystemQ::"Check if the system of ODEs is constant"
LinearSystemQ::"Check if the system of ODEs is linear"
AffineSystemQ::"Check if the system of ODEs is affine"
MultiAffineSystemQ::"Check if the system of ODEs is multi-affine"
PolynomialSystemQ::"Check if the system of ODEs is polynomial"
HomogeneousSystemQ::"Check if a given polynomial is homogeneous in the given variables."
MaxSystemDegree::"Return the maximum polynomial degree of the right-hand side in the system of ODEs"
NonLinPolySystemQ::"Check if the system of ODEs is non-linear"
ClassifyProblem::"Classify a given safety verification problem"


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


RationalFunctionQ[expr_,vars_List]:=Module[{factor=Factor[expr]},
numerator=Numerator[factor];
denominator=Denominator[factor];
If[Not[PolynomialQ[numerator,vars] && PolynomialQ[denominator,vars]], False,
Not[TrueQ[denominator==0]]
]
]


ClassifyProblem[problem_List]:=Module[{},
(* Pattern match fields in the problem *)
{ pre, { vectorField, vars, evoConstraint }, post } = problem;

SystemHierarchy=Graph[
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
VertexList[SystemHierarchy]//.classCheck, 
EdgeList[SystemHierarchy]//.classCheck, 
VertexLabels->"Name"],  False];

(* Check if a node is a sink *)
isSink[node_,graph_Graph]:=TrueQ[VertexOutComponent[graph,{node}]=={node}];

(* Return the dimension and a list of sink nodes, i.e. the most specific classification in the hierarchy *)
{SystemDimension[vectorField,vars], Select[VertexList[classGraph], isSink[#,classGraph]&]}
]


End[]


EndPackage[]
