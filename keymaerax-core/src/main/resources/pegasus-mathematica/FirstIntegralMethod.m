(* ::Package:: *)

Needs["FirstIntegralGen`",NotebookDirectory[]<>"FirstIntegralGen.m"] 
Needs["Primitives`",NotebookDirectory[]<>"Primitives.m"] 


BeginPackage[ "FirstIntegralMethod`"]


FirstIntegralMethod::usage="FirstIntegralMethod[problem_List]"


Begin["`Private`"]


Options[FirstIntegralMethod]={RationalsOnly->False, RationalPrecision->10, FirstIntegralDegree->0};
FirstIntegralMethod[{pre_, {f_List,statevars_List,Q_}, post_}, opts:OptionsPattern[]]:=Module[{
rats,FIDeg,ratPrecision,upperRat,lowerRat,initConnectedComponents,FIs,maximise,minimise,maxFns,minFns,partitioning
},

(* Process options *)
rats=TrueQ[OptionValue[RationalsOnly]];
FIDeg=If[TrueQ[OptionValue[FirstIntegralDegree]>0],OptionValue[FirstIntegralDegree], Max[Map[Primitives`PolynomDegree,f]]+1];
ratPrecision=If[TrueQ[OptionValue[RationalPrecision]>0],OptionValue[RationalPrecision],10];

(* Create rationalization function wrappers *)
upperRat[num_]:=If[TrueQ[rats && Element[num,Reals]], Primitives`UpperRat[num, ratPrecision], num];
lowerRat[num_]:=If[TrueQ[rats && Element[num,Reals]], Primitives`LowerRat[num, ratPrecision], num];

(* Compute the connected components of the initial set *)
initConnectedComponents=CylindricalDecomposition[pre,statevars,"Components"];

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


End[]
EndPackage[]
