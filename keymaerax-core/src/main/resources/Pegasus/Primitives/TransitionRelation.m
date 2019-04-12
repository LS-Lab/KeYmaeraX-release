(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{ParentDirectory[],"Primitives.m"}]] (* Load primitives package *)


(* ::Input:: *)
(*(* Polynomial generation for qualitative analysis *)*)


BeginPackage["TransitionRelation`"];


ConstantDirections::usage="ConstantDirections[problem]"


Begin["`Private`"]


(* Obtain a list of factors by Solve insted of Factor *)
SFactorList[f_,vars_] := Module[{factorList,
i,j,tooHighDegree,partialFactorList,maxDeg},
factorList = {};
maxDeg=3;
(* If any variable has degree > maxDeg, ignore that part of the dynamics *)
For[i = 1, i <= Length[f], i++, 
tooHighDegree = 0;
For[j = 1, j <= Length[vars], j++, If[Exponent[f[[i]] , vars[[j]]]>maxDeg,tooHighDegree = 1]];
(* Determine whehther the current part of the dynamics will be considered *)
If [tooHighDegree == 0,
partialFactorList = {};
For[j = 1, j <= Length[vars], j++, 
If[tooHighDegree == 0,  
partialFactorList = Join[partialFactorList, Flatten[Solve[f[[i]] == 0, vars[[j]], Reals]]]];
];
factorList = Append[factorList, {i, DeleteDuplicates[partialFactorList]}];
]
];
factorList
];
(*	Determine which directions the variables have to move in order to go from init to unsafe
	1 = increase, -1 = decrease, 0 = no information *)
PrePostDirections[boundsStart_,boundsUnsafe_,vars_]:=Module[{directions,i},
directions = {};
For[i = 1, i <= Length[vars], i++, If[boundsStart[[i]][[1]]> boundsUnsafe[[i]][[2]],directions = Append[directions, -1], If[boundsStart[[i]][[2]] <   boundsUnsafe[[i]][[1]], directions = Append[directions, 1], directions = Append[directions, 0]]
]
];
directions
];

ConstantDirections[problem_List]:=Module[
{pre,f,vars,Q,post,factorList,allPolyFactors,
startRegion, unsafeRegion,
boundsStart,boundsUnsafe,
directions,i ,
componentIndex,componentList,
directionInComponent,moveDirectionInComponent,invariantsCandidate},

{pre,{f,vars,Q},post}=problem;
factorList=SFactorList[f,vars]; (* factors from solving *)
allPolyFactors = Flatten[Map[#[[2]]&,factorList]];

(* Calculate region bounds *)
startRegion = ImplicitRegion[pre, Evaluate[vars]];
unsafeRegion = ImplicitRegion[Not[post], Evaluate[vars]];
boundsStart = RegionBounds[startRegion];
boundsUnsafe = RegionBounds[unsafeRegion];
directions = PrePostDirections[boundsStart,boundsUnsafe,vars];

invariantsCandidate={};
(*Print["Directions: ",directions]; *)
(* Handle the case where one of the directions is (potentially) constant *)
For[i = 1, i <= Length[factorList], i++,  
componentIndex = factorList[[i]][[1]];
componentList = factorList[[i]][[2]];

(* First we'll figure out whether there is constant flow in any component and produce a candidate invariant in that case
It is important to treat this separately so as to distinguish it from the case when we have no information *)
If[Length[componentList] == 0, 
(*Print[StringJoin["Potentially constant direction in component "],ToString[vars[[componentIndex]]]];*)
directionInComponent = f[[componentIndex]]/. Map[#->1&,vars];
moveDirectionInComponent= directions[[componentIndex]];
If[directionInComponent > 0 && moveDirectionInComponent <= 0,
  invariantsCandidate = Append[invariantsCandidate, vars[[componentIndex]] - boundsStart[[componentIndex]][[2]]],
If[directionInComponent < 0 && moveDirectionInComponent >= 0, 
  invariantsCandidate = Append[invariantsCandidate, vars[[componentIndex]] - boundsStart[[componentIndex]][[1]]]];
]];
];
invariantsCandidate
];


End[]
EndPackage[]
