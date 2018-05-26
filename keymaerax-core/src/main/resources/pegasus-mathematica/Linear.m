(* ::Package:: *)

(* Description: Implementation of invariant generation methods for linear systems of ODEs.
   Comments: Tested in Mathematica 10.0   *)


Needs["FirstIntegralGen`",NotebookDirectory[]<>"FirstIntegralGen.m"] 


BeginPackage[ "Linear`"]


LinearMethod::usage="LinearMethod[problem_List]"
PlanarConstantMethod::usage="ConstantMethod[problem_List]"
FirstIntegralMethod::usage="FirstIntegralMethod[problem_List]"
LinearClass::usage="LinearClass[matrix]"
UpperRat::usage="UpperRat[number, precision]"
LowerRat::usage="LowerRat[number, precision]"
UpperRatCoeffs::usage="UpperRatCoeffs[number, precision]"


Begin["`Private`"]


(* Upper rational bound of a number *)
UpperRat[x_?NumericQ, precision_?Positive]:=Module[{},
uncertainty=Abs[x]*10^-precision;
Rationalize[N[x,precision]+uncertainty, uncertainty]
]
(* Lower rational bound of a number *)
LowerRat[x_?NumericQ, precision_?Positive]:=Module[{},
uncertainty=Abs[x]*10^-precision;
Rationalize[N[x,precision]-uncertainty, uncertainty]
]


UpperRatCoeffs[p_?PolynomialQ, vars_List, precision_?NonNegative]:=Module[{},
coeffRules=CoefficientRules[p, vars];
coeffRules=coeffRules/.{Rule[$MON_,$COEFF_]->Rule[$MON,UpperRat[$COEFF,precision]]};
FromCoefficientRules[coeffRules,vars]
]


LinearClass[M_?MatrixQ]:=Module[{},
Which[
AllTrue[Eigenvalues[M],Re[#]<0&], "Sink",
AllTrue[Eigenvalues[M],Re[#]>0&], "Source",
AllTrue[Eigenvalues[M],Re[#]==0&], "Centre",
True, "Other"]
]


EigenspacePolys[M_List,vars_List]:=Module[{},
Map[Rest[#].vars&,Select[Eigensystem[Transpose[M]]//Transpose,Element[First[#],Reals] &]]//Flatten
]


FirstIntegrals[M_List,vars_List,deg_Integer?NonNegative]:=Module[{},
(* Compute functionally independent first integrals up to given degree *)
FirstIntegralGen`FuncIndep[FirstIntegralGen`FindFirstIntegrals[deg, vars, M.vars],vars]
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


Options[LinearMethod]={RationalsOnly->False, RationalPrecision->10, FirstIntegralDegree->2};
LinearMethod[Init_, Postcond_, System_List, opts:OptionsPattern[]]:=Module[{
M=Grad[System[[1]], System[[2]]],
statevars=System[[2]]
},

(* Process options *)
rats=TrueQ[OptionValue[RationalsOnly]];
FIDeg=If[TrueQ[OptionValue[FirstIntegralDegree]>0],OptionValue[FirstIntegralDegree],2];
ratPrecision=If[TrueQ[OptionValue[RationalPrecision]>0],OptionValue[RationalPrecision],10];

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[rats && Element[num,Reals]], UpperRat[num, ratPrecision], num];
lowerRat[num_]:=If[TrueQ[rats && Element[num,Reals]], LowerRat[num, ratPrecision], num];

(* Compute the linear forms of the invariant sub-spaces *)
separatrices=EigenspacePolys[M, statevars]; 
separatrices=If[rats,Map[UpperRatCoeffs[#,statevars,ratPrecision]&, separatrices], separatrices];

(* Compute the connected components of the initial set *)
initConnectedComponents=CylindricalDecomposition[Init,statevars,"Components"];

class=LinearClass[M]/.{
"Centre" :> Block[{FIs=FirstIntegrals[M,statevars,FIDeg]},
maximise=FIs;
minimise=FIs;
maxFns = Map[#[[1]]-upperRat[MaxValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-lowerRat[MinValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{minimise, initConnectedComponents}] ];
Print[Union[ maxFns, minFns]];
Union[ maxFns, minFns]
],
"Stable":> Block[{},
LyapunovFn=LyapunovIdentity[M,statevars];
Krasovskii=System[[1]].System[[1]]; 
maximise=Union[separatrices, {LyapunovFn, Krasovskii}];
minimise=Union[separatrices];
maxFns = Map[#[[1]]-MaxValue[#,statevars]&, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-MinValue[#,statevars]&, Tuples[{minimise, initConnectedComponents}] ];
Union[separatrices, maxFns, minFns]
],
"Unstable":> Block[{},
LyapunovFn=LyapunovIdentity[-M,statevars];
Krasovskii=(-System[[1]]).(-System[[1]]); 
maximise=Union[separatrices];
minimise=Union[separatrices, {LyapunovFn, Krasovskii}];
maxFns = Map[#[[1]]-MaxValue[#,statevars]&, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-MinValue[#,statevars]&, Tuples[{minimise, initConnectedComponents}] ];
Union[separatrices, maxFns, minFns]
],
"Other":> Block[{FIs=FirstIntegrals[M,statevars,FIDeg]},
maximise=Union[separatrices, FIs]//Flatten;
minimise=Union[separatrices,FIs]//Flatten;
Print[FIs];
Print[maximise];
Print[minimise];
maxFns = Map[#[[1]]-upperRat[MaxValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-lowerRat[MinValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{minimise, initConnectedComponents}] ];
Print[Union[maxFns, minFns, separatrices]//Flatten];
Union[maxFns, minFns, separatrices]//Flatten
],
_-> separatrices
};
class
]


Options[PlanarConstantMethod]={RationalsOnly->False, RationalPrecision->10, FirstIntegralDegree->1};
PlanarConstantMethod[Init_, Postcond_, System_List, opts:OptionsPattern[]]:=Module[{
f=System[[1]],
statevars=System[[2]]
},

(* Process options *)
rats=TrueQ[OptionValue[RationalsOnly]];
FIDeg=If[TrueQ[OptionValue[FirstIntegralDegree]>0],OptionValue[FirstIntegralDegree],1];
ratPrecision=If[TrueQ[OptionValue[RationalPrecision]>0],OptionValue[RationalPrecision],10];

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[rats && Element[num,Reals]], UpperRat[num, ratPrecision], num];
lowerRat[num_]:=If[TrueQ[rats && Element[num,Reals]], LowerRat[num, ratPrecision], num];

(* Compute the connected components of the initial set *)
initConnectedComponents=CylindricalDecomposition[Init,statevars,"Components"];

(* Compute first integral *)
FIs=FirstIntegralGen`FuncIndep[FirstIntegralGen`FindFirstIntegrals[FIDeg, statevars, f],statevars];

maximise=Union[FIs,{f.statevars}]//Flatten;
minimise=Union[FIs,{f.statevars}]//Flatten;

maxFns = Map[#[[1]]-upperRat[MaxValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-lowerRat[MinValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{minimise, initConnectedComponents}] ];
Print[Union[ maxFns, minFns]];
partitioning=Union[ maxFns, minFns];
partitioning
]


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_]:=Module[{},
Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]]
]


Options[FirstIntegralMethod]={RationalsOnly->False, RationalPrecision->10, FirstIntegralDegree->0};
FirstIntegralMethod[Init_, Postcond_, System_List, opts:OptionsPattern[]]:=Module[{
f=System[[1]],
statevars=System[[2]]
},

(* Process options *)
rats=TrueQ[OptionValue[RationalsOnly]];
FIDeg=If[TrueQ[OptionValue[FirstIntegralDegree]>0],OptionValue[FirstIntegralDegree], Max[Map[PolynomDegree,f]]+1];
ratPrecision=If[TrueQ[OptionValue[RationalPrecision]>0],OptionValue[RationalPrecision],10];

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[rats && Element[num,Reals]], UpperRat[num, ratPrecision], num];
lowerRat[num_]:=If[TrueQ[rats && Element[num,Reals]], LowerRat[num, ratPrecision], num];

(* Compute the connected components of the initial set *)
initConnectedComponents=CylindricalDecomposition[Init,statevars,"Components"];

(* Compute first integral *)
FIs=FirstIntegralGen`FuncIndep[FirstIntegralGen`FindFirstIntegralsAlt[FIDeg, statevars, f],statevars];

maximise=Union[FIs,{f.statevars}]//Flatten;
minimise=Union[FIs,{f.statevars}]//Flatten;

maxFns = Map[#[[1]]-upperRat[MaxValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{maximise, initConnectedComponents}] ];
minFns = Map[#[[1]]-lowerRat[MinValue[#,statevars]/.{Infinity -> 0,-Infinity -> 0}] &, Tuples[{minimise, initConnectedComponents}] ];
Print[Union[ maxFns, minFns]];
partitioning=Union[ maxFns, minFns];
partitioning
]


End[]
EndPackage[]
