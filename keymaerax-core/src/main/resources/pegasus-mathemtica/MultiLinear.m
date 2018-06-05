(* ::Package:: *)

(* Description: Implementation of invariant generation methods for linear systems of ODEs.
   Comments: Tested in Mathematica 10.0   *)


Needs["FirstIntegralGen`",NotebookDirectory[]<>"FirstIntegralGen.m"] 


BeginPackage[ "MultiLinear`"]


MultiLinearMethod::usage="LinearMethod[problem_List]"
MultiLinearClass::usage="LinearClass[system]"


Begin["`Private`"]


MultiLinearClass[System_List]:=Module[{},
Which[
True, "Other"
]
]


EigenspacePolys[M_List,vars_List]:=Module[{},
Map[Rest[#].vars&,Select[Eigensystem[Transpose[M]]//Transpose,Element[First[#],Reals] &]]
]


FirstIntegrals[vectorField_List,vars_List,deg_Integer?NonNegative]:=Module[{},
(* Compute functionally independent first integrals up to given degree *)
FirstIntegralGen`FuncIndep[FirstIntegralGen`FindFirstIntegrals[deg, vars, vectorField],vars]
]


LyapunovIdentity[M_,vars_List]:=Module[{},
ID=IdentityMatrix[Length[vars]];
NDM=-(ID);
LM=LyapunovSolve[Transpose[M],NDM];
Expand[vars.LM.vars]
]


RandomPosMatrix[range_?IntegerQ,size_]:=Module[{},
Table[Table[RandomInteger[{1,range}]/RandomInteger[{1,range}],{i,1,size}],{j,1,size}]
]


LyapunovRand[M_,vars_List]:=Module[{},
RM=RandomPosMatrix[5,Length[vars]];
NDM=-(RM.Transpose[RM]);
LM=LyapunovSolve[Transpose[M],NDM];
Expand[vars.LM.vars]
]


MultiLinearMethod[Init_, Postcond_, System_List]:=Module[{
Jacobian=Grad[System[[1]], System[[2]]],
vectorField=System[[1]],
statevars=System[[2]]
},
initConnectedComponents=CylindricalDecomposition[Init,statevars,"Components"];
class=MultiLinearClass[System]/.{
"Other":> Block[{},
FI=FirstIntegralGen`FindFirstIntegrals[2, statevars, System[[1]]];
FI=FirstIntegralGen`FuncIndep[FI];
Print["Running Strat"];
Print[FI];
maximise=Union[{}, FI];
minimise=Union[{},FI];
maxFns = Map[#[[1]]-MaxValue[#,statevars]&, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-MinValue[#,statevars]&, Tuples[{minimise, initConnectedComponents}] ];
Union[minFns, maxFns, separatrices]
],
_-> {}
};
class
]


End[]
EndPackage[]
