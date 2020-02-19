(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] (* Load primitives package *)


(* ::Input:: *)
(*(* Conic abstraction as following Giacobbe's thesis.  *)
(*SPECIFIATIONS: Requires a 2 dimensional affine system and needs A to have all real eigenvalues. *)*)


BeginPackage["ConicAbstractions`"];


ConicAbstractionsPartition::usage="Uses techniques from the thesis to partition state space; used in TransitionRel";


DimPartitionM::usage="Splits along dimensions";
ConicPartition::usage="Computes the conic partition for a linear system";


Begin["`Private`"]


(* Paritioning derivative space into uniform pizza slices in arbitrary dimensions 
using rotation matrices *)
RotateM[vec_List,splits_]:=Module[{u,v,rot,ang},
ang=Pi/splits;
{u,v}=vec;
rot=N[RotationMatrix[ang,{u,v}]];
Round[Table[MatrixPower[rot,i,u],{i,0 ,splits-1}],0.00001]
];


DimPartitionM[mat_,splits_,dim_]:=Module[{hd,tl},
hd=First[mat];
tl=Drop[mat,1];
Flatten[Map[RotateM[{#,hd},splits]&,tl],1]
]


ConicPartition[problem_List, splits_]:=Module[
	{pre,f,vars,X, Q,post,i, A, b, es, diagA, eigv, initRegPoints,
	ZPoints, v0, p, unifPartition,normals,mat},
{pre,{f,vars,Q},post}=problem;
(* Now we'll need to diagonalize our system *)
A = Grad[f, vars];
b = f - A.vars;
mat=IdentityMatrix[Length[vars]];
(*mat=Eigenvectors[Inverse[A]];*)
unifPartition = DimPartitionM[mat,splits, Length[vars]];
normals=Map[#.A&,unifPartition];
polys=Map[#.vars&,normals]
];


(* Checks if a matrix has all real eigenvalues-- *)
AllRealEigenvalues[A__]:=Module[{},
AllTrue[Eigenvalues[A], PossibleZeroQ[Im[#]]&]
]


(* Find a bounding box of an initial set *)
RecursiveCombineLists[inputList_] := Module[{i, newList, recList, len},
newList = {};
len =Length[inputList];
If[len ==0, Return[newList]];
If[len== 1, Return[ {{inputList[[1]][[1]]}, {inputList[[1]][[2]]} }]];
(* Otherwise we need it to be recursive *)
 recList = RecursiveCombineLists[Drop[inputList, -1]];For[i = 1, i <= Length[recList], i++, newList = Append[newList, Append[recList[[i]], inputList[[Length[inputList]]][[1]]]]; 
newList =  Append[newList, Append[recList[[i]], inputList[[Length[inputList]]][[2]]]];
];
Return[newList];
];
PolygonOverapprox[pre_, vars_] := Module[{X, regBounds, pointList, i, element},
regBounds= RegionBounds[ImplicitRegion[pre,Evaluate[vars]]];
Print["regBounds",regBounds];
pointList = RecursiveCombineLists[regBounds];
Print["pointList: ", pointList];
Return[pointList];
]


PartitionsM[vec_List,splits_, vars_]:=Module[{ls,ls2,result},
ls=RotateM[vec,splits];
ls2=RotateLeft[ls,1];
result=MapThread[vars.#1>0&&vars.#2<0&,{ls,ls2}]
]
CalcListToSplit[n_] :=Module[{i, returnList, unitVec}, 
returnList = {};
For[i = 2, i <= n, i++, unitVec = ConstantArray[0,n]; unitVec[[i]] = unitVec[[i]]+1;returnList = Append[returnList, unitVec]];
Return[returnList];
]
ExhaustivePartitionsM[splits_, vars_] :=Module[{ls,ls2,res, listToSplit, i,j, result, result2, turnVector, n},
n = Length[vars];
listToSplit = CalcListToSplit[n];
turnVector = ConstantArray[0,n]; 
turnVector[[1]] = turnVector[[1]] +1;
Print[listToSplit];
Print[turnVector];
result = PartitionsM[{listToSplit[[1]],turnVector}, splits, vars];
For[i = 2, i <= Length[listToSplit], i++, 
result2 = PartitionsM[{listToSplit[[i]],turnVector}, splits, vars];
result = Flatten[Map[And[#[[1]],#[[2]]]&,Tuples[{result,result2}]]];
For[j = 1, j <= Length[result], j++,
If[FindInstance[result[[j]]&& vars[[1]]!=0, vars] == {}, result = Delete[result, j]; j = j -1;];
];
];
result = result //.{Less -> LessEqual, Greater -> GreaterEqual};
Return[result];
];


(* *)
ConicAbstractionsPartition[problem_List, splits_]:=Module[{pre,f,vars,X, Q,post,i , A, b, es, diagA, eigv, initRegPoints, ZPoints, v0, p, unifPartition},
{pre,{f,vars,Q},post}=problem;
(* First, let's convert pre into a polygon (we'll do this with bounding boxes, it probably could be optimized further later )*)
X= PolygonOverapprox[pre, vars];
(* Now we'll need to diagonalize our system *)
A = Grad[f, vars];
b = f - A.vars;
es = Eigensystem[A];
If[AllRealEigenvalues[A]==False, Return[{}]];
diagA = DiagonalMatrix[Eigenvalues[A]];
eigv = Transpose[Eigenvectors[A]];

unifPartition = ExhaustivePartitionsM[splits, vars];
Return[{A,b,unifPartition}];
];


End[]
EndPackage[]
