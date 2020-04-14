(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] (* Load primitives package *)


(* ::Input:: *)
(*(* Conic abstraction as following Giacobbe's thesis.  *)
(*SPECIFIATIONS: Requires a 2 dimensional affine system and needs A to have all real eigenvalues. *)*)


BeginPackage["ConicAbstractions`"];


ConicAbstractionsPartition::usage="Uses techniques from the thesis to partition state space; used in TransitionRel";


DimPartitionM::usage="Splits along dimensions";
ConicPartition::usage="Computes the conic partition for a linear system";
ConicAbstraction::usage=" Given system matrix A, "


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


(* Partial implementation of full conic abstractions algorithm *)

(* Find the convex hull of the transformation of BoundaryMeshRegion co under matrix A *)
TransformCone[co_,A_]:=Module[{coord,Acoord},
coord = MeshCoordinates[co];
Acoord=Map[A.#&,coord];
Return[ConvexHullMesh[Acoord]];
];
(* Take the Minkowski sum of two BoundaryMeshRegions co and do *)
MinkowskiSum[co_,do_]:=Module[{i,acc,mdo,mco},
mdo=MeshCoordinates[do];
mco=MeshCoordinates[co];
acc={};
For[i=1,i<=Length[mdo],i++,
acc=Join[acc,Map[mdo[[i]]+#&,mco]];
];
(* Print["Coordinates: ",MeshCoordinates[ConvexHullMesh[acc]]]; *)
Return[ConvexHullMesh[acc]];
];

(* Partition 2D plane into k regions *)
Partition2D[k_,bnd_]:=Module[{regList,i,rota,rotb,curpt,nextpt},
regList = {};
eps=0.0001;
rota=Rationalize[RotationMatrix[2Pi/k-eps]];
rotb=Rationalize[RotationMatrix[2Pi/k+eps]];
curpt={bnd,0};
For[i=0,i<k,i++,
nextpt=rotb.curpt;
regList=Append[regList,ConvexHullMesh[{{0,0},curpt,nextpt}]];
curpt=rota.curpt;
];
regList=Append[regList,ConvexHullMesh[{{0,0},curpt,RotationMatrix[eps].{bnd,0}}]];
Return[regList];
];


(*
	Do a basic conic abstractions algorithm
*)
ConicAbstraction[A_, Init_, k_Integer, bnd_,rng_] :=Module[{
  diagA,z0,cones, ret, i, hd,rc, conesgfx, conesactivegfx,
  redz0,MAXITERS, iter, sp, ctr,imgsz,
  H,c,intc,transc,msc,msic,d,intd,transd,msd,msid,fin,retgfx,rd
  },

  (* ctr, H, int, transc, msc, msd, msic, msid, c, inf, intc, intd,transd,d, hd,tl,rc},*)

(* maximum iterations *)
MAXITERS=100;
imgsz=300;

diagA = A; (* Instead of diagonalizing, work directly over A. DiagonalMatrix[Eigenvalues[A]];*)

(* Init is a list of 2D points, and we take the convex hull  as the initial set *)
z0 = Init;

(* Partition plane into k regions with bnd *)
cones = Map[TransformCone[#,Inverse[diagA]]&, Partition2D[k,bnd]];

ret = {};
For[i = 1, i <= Length[cones], i++,
  ret=Append[ret, EmptyRegion[2]]
];

sp = StreamPlot[A.{x,y},{x,-rng,rng},{y,-rng,rng}];
Print["Initial state (red) and conic partition (blue)"];
redz0 = Graphics[Show[z0]]/.{Directive[x_] :> Directive[{Opacity[0.8],Red}]};
conesgfx = Map[Graphics[Show[#]]/.{Directive[x_] :> Directive[{Opacity[0.2],Cyan,EdgeForm[Black]}]}&,cones];
conesactivegfx = Map[Graphics[Show[#]]/.{Directive[x_] :> Directive[{Opacity[0.3],Blue,EdgeForm[Black]}]}&,cones];
(* The cones in state space *)
Print[Show[sp, conesgfx ,redz0,ImageSize->imgsz]];

(* Compute the initial intersections *)
H = {};
For[ctr=1,ctr<=Length[cones],ctr++,
  c=cones[[ctr]];
  intc=RegionIntersection[z0,c];
  If[intc===EmptyRegion[2],Continue[]];

  transc=TransformCone[c,diagA];
  msc=MinkowskiSum[transc,intc];
  msic=RegionIntersection[msc,c];
  ret[[ctr]]=msic;
  H=Join[H,{ctr}];
];

(* Active initial cones *)
Print["Active initial cones"];
Print[Show[conesgfx,conesactivegfx[[H]],redz0,PlotRange->{{-rng,rng},{-rng,rng}},ImageSize->imgsz]];

iter=0;
While[Length[H]!= 0,
  (* Make sure it does not infinite loop *)
  iter=iter+1;
  If[iter > MAXITERS, Break[]];

  {{hd},H}=TakeDrop[H,1];
  rc=ret[[hd]];

  For[ctr=1,ctr<=Length[cones],ctr++,
    If[hd==ctr,Continue[]];
    d=cones[[ctr]];
    intd = RegionDifference[RegionIntersection[RegionBoundary[rc],RegionBoundary[d]],ret[[ctr]]];

    If[intd===EmptyRegion[2],Continue[]];
    (* Skip if it has already been added*)
    (*rd=RegionDifference[intd,ret[[ctr]]];
    If[rd===EmptyRegion[2],Continue[]];
    Print["intd ",intd];
    Print["ret ",ret[[ctr]]];
    Print["rd :",rd];*)

    transd=TransformCone[d,diagA];
    msd=MinkowskiSum[transd,intd];

    msid=RegionIntersection[msd,d];

    Print["Step: ",iter," From: ",hd," To: ",ctr];
    Print[Show[sp,conesgfx,Graphics[{Opacity[0.8],Green,rc}],
      conesactivegfx[[hd]],
      conesactivegfx[[ctr]],
      Graphics[{Opacity[0.8],Yellow,msid}],PlotRange->{{-rng,rng},{-rng,rng}},ImageSize->imgsz]];

    ret[[ctr]]=RegionUnion[ret[[ctr]],msid];
    If[MemberQ[H,ctr],,H=Join[H,{ctr}]]
  ];
];

fin=Select[ret,Not[Head[#]===EmptyRegion]&];
retgfx= Map[Graphics[Show[#]]/.{Directive[x_] :> Directive[{Opacity[0.8],Green,EdgeForm[Black]}]}&,fin];

Print["Final tube:"];
Print[Show[sp,conesgfx,retgfx]];

(* Show[cones,Graphics[{Red,z0}]] *)
(* Show[Map[TransformCone[#,diagA]&,{C0,C1,C2}]] *)

Return[{cones,ret}];
];


End[]
EndPackage[]
