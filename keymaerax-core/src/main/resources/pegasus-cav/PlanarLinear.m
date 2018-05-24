(* ::Package:: *)

(* Description: Implementation of invariant generation methods for planar linear systems of ODEs.
   Comments: Tested in Mathematica 10.0   *)


Needs["FirstIntegralGen`",NotebookDirectory[]<>"FirstIntegralGen.m"] 


BeginPackage[ "PlanarLinear`"]


PlanarLinearMethod::usage="PlanarLinearMethod[problem_List]"
PlanarLinearClass::usage="PlanarLinearClass[matrix]"
LyapunovIdentity::usage="LyapunovIdentity[problem_List]"
LyapunovRand::usage="LyapunovRand[problem_List]"


Begin["`Private`"]


PlanarLinearClass[M_?MatrixQ]:=Module[{
trace=Tr[M],
det=Det[M]
},
Which[
trace^2-4*det>0,Which[
det<=0, "Saddle",
det>0 && trace==0, "Saddle",
det>0 && trace>0, "Unstable Node",
det>0 && trace<0, "Stable Node"
],
trace^2-4*det==0,Which[
trace<0, "Stable Node",
trace>0, "Unstable Node"
],
trace^2-4*det<0, Which[
trace<0, "Stable Focus", 
trace>0, "Unstable Focus",
trace==0, "Centre"
]
]
]


EigenspacePolys[M_List, systemvars_List]:=Module[{},
(* Compute eigenvectors of the system matrix *)
eigenvectors=Eigenvectors[M];
(* Select only real-valued eigenvectors *)
realEigenvectors=Select[eigenvectors, AllTrue[#, Internal`RealValuedNumericQ]&];
(* Compute the nullspace of the real-valued eigenvectors and construct a linear polynomial evaluating to 0 on the nullspace *)
invarHyperplanes=Map[NullSpace[{#}][[1]].systemvars&,realEigenvectors]
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


PlanarLinearMethod[Init_, Postcond_, System_List]:=Module[{
M=Grad[System[[1]], System[[2]]],
statevars=System[[2]]
},
separatrices=EigenspacePolys[M, statevars];
initConnectedComponents=CylindricalDecomposition[Init,statevars,"Components"];
class=PlanarLinearClass[M]/.{
"Centre" :> Block[{FI=Select[FirstIntegralGen`FindFirstIntegrals[2, statevars,System[[1]]],Not[NumberQ[#]]&][[1]]},
max=Map[MaxValue[{FI, #},statevars]&, initConnectedComponents];
min=Map[MinValue[{FI, #},statevars]&, initConnectedComponents];
Map[FI-# &, Union[min, max]]
],
"Stable Focus":> Block[{},
LyapunovFn=LyapunovIdentity[M,statevars];
maxLyap=Map[MaxValue[{LyapunovFn, #},statevars]&, initConnectedComponents];
Map[LyapunovFn-# &, maxLyap]
],
"Stable Node":> Block[{},
LyapunovFn=LyapunovIdentity[M,statevars];
Krasovskii=System[[1]].System[[1]]; 
maximise=Union[separatrices, {LyapunovFn, Krasovskii}];
minimise=Union[separatrices];
maxFns = Map[#[[1]]-MaxValue[#,statevars]&, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-MinValue[#,statevars]&, Tuples[{minimise, initConnectedComponents}] ];
Union[separatrices, maxFns, minFns]
],
"Unstable Focus":> Block[{},
LyapunovFn=LyapunovIdentity[-M,statevars];
minLyap=Map[MinValue[{LyapunovFn, #},statevars]&, initConnectedComponents];
Map[LyapunovFn-# &, minLyap]
],
"Unstable Node":> Block[{},
LyapunovFn=LyapunovIdentity[-M,statevars];
Krasovskii=(-System[[1]]).(-System[[1]]); 
maximise=Union[separatrices];
minimise=Union[separatrices, {LyapunovFn, Krasovskii}];
maxFns = Map[#[[1]]-MaxValue[#,statevars]&, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-MinValue[#,statevars]&, Tuples[{minimise, initConnectedComponents}] ];
Union[separatrices, maxFns, minFns]
],
"Saddle":> Block[{},
maxFns = Map[#[[1]]-MaxValue[#,statevars]&, Tuples[{separatrices, initConnectedComponents}] ];
minFns = Map[#[[1]]-MinValue[#,statevars]&, Tuples[{separatrices, initConnectedComponents}] ];
Union[minFns, maxFns, separatrices]
],
_-> separatrices
};
class
]


End[]
EndPackage[]
