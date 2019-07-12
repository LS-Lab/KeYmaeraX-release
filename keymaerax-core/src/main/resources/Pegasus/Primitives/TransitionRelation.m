(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] (* Load primitives package *)
Needs["QualitativeAbstraction`",FileNameJoin[{Directory[],"Primitives","QualitativeAbstractionPolynomials.m"}]]


(* ::Input:: *)
(*(* Polynomial generation for qualitative analysis *)*)


BeginPackage["TransitionRelation`"];


ConstantDirections::usage="ConstantDirections[problem] determines if one of the coordinate axes has flow in constant direction"
TransitionRel::usage="Abstraction based on transition relation computation for neighboring cells";


Begin["`Private`"]


(*  Determine which directions the variables have to move in order to go from init to unsafe
	1 = increase, -1 = decrease, 0 = no information *)
PrePostDirections[boundsStart_,boundsUnsafe_,vars_]:=Module[{directions,i},
directions = {};
For[i = 1, i <= Length[vars], i++, If[boundsStart[[i]][[1]]> boundsUnsafe[[i]][[2]],directions = Append[directions, -1], If[boundsStart[[i]][[2]] <   boundsUnsafe[[i]][[1]], directions = Append[directions, 1], directions = Append[directions, 0]]
]
];
directions
];

ConstantDirections[problem_List]:=Module[
{pre,f,vars,Q,post,factorList,
startRegion, unsafeRegion,
boundsStart,boundsUnsafe,
directions,i ,componentList,
directionInComponent,moveDirectionInComponent,invariantsCandidate},

{pre,{f,vars,Q},post}=problem;
factorList=QualitativeAbstraction`SFactorList[problem]; (* factors from solving *)

(* Calculate region bounds *)
startRegion = ImplicitRegion[pre, Evaluate[vars]];
unsafeRegion = ImplicitRegion[Not[post], Evaluate[vars]];
boundsStart = RegionBounds[startRegion];
boundsUnsafe = RegionBounds[unsafeRegion];
directions = PrePostDirections[boundsStart,boundsUnsafe,vars];

invariantsCandidate={};
(* Handle the case where one of the directions is (potentially) constant *)
For[i = 1, i <= Length[factorList], i++,  

(* First we'll figure out whether there is constant flow in any component and produce a candidate invariant in that case
It is important to treat this separately so as to distinguish it from the case when we have no information *)
If[Length[factorList[[i]]] == 0, 
(*Print[StringJoin["Potentially constant direction in component "],ToString[vars[[componentIndex]]]];*)
  directionInComponent = f[[i]]/. Map[#->1&,vars];
  moveDirectionInComponent= directions[[i]];
  If[directionInComponent > 0 && moveDirectionInComponent <= 0,
    invariantsCandidate = Append[invariantsCandidate, vars[[i]] - boundsStart[[i]][[2]]],
  If[directionInComponent < 0 && moveDirectionInComponent >= 0, 
    invariantsCandidate = Append[invariantsCandidate, vars[[i]] - boundsStart[[i]][[1]]]];
  ]
 ];
];
invariantsCandidate
];


TestPolynomialChanges[polyList_, region_, regionIndex_, signTuple_, samplePoints_, vars_,vf_]:=Module[{
  pointInRegion, secondPointInRegion, signInRegion, i,j,
  counter, returnList, pointMap, secondPointMap, evalAtFirstPoint, evalAtSecondPoint,lieList},
pointInRegion = samplePoints[[regionIndex]];
pointMap={};
For[j=1,j<=Length[vars],j++,
  pointMap=Append[pointMap,vars[[j]]->pointInRegion[[j]]]];
lieList=Map[Primitives`Lf[#,vf,vars]&,polyList];
returnList = {};
For[i = 1, i <= Length[polyList], i++, 
evalAtFirstPoint = lieList[[i]]/.pointMap ;
	If[evalAtFirstPoint == 0, returnList = Append[returnList, 0]];
	If[evalAtFirstPoint < 0, returnList = Append[returnList, -1]];
	If[evalAtFirstPoint > 0, returnList = Append[returnList, 1]];
];

Return[returnList];
]


TransitionRel[problem_List]:=Module[{
  pre,f,vars,Q,post,
  i, j, k, startRegion, partitionSpace, partitionSpaceSigns, newPartitionSpaceSigns, 
  signList, signTuple, newPartitionSpace, componentIndex, componentList,allPolyFactors,fringeBeforeEval,
  moveDirectionInComponent, directionInComponent, evalAtList, reachableRegions,fringe, fringeElement, pointInRegion,
  invariantsCandidate, pointMap, regionIndex, signInRegion, samplePoints, polyChangeList, allInvariant,
  polyValInRegion, transitionSignList, transitionList, allTransitions,allTransitionsHelper, pointMapList, regionCandidate, positionOfRegionCand,pos},
{pre,{f,vars,Q},post}=problem;
(* factors from solving *)
allPolyFactors = Flatten[QualitativeAbstraction`SFactorList[problem]];
(*Print["all poly factors ",allPolyFactors];*)
If[Length[allPolyFactors] == 0,
  Print["Unable to find partitioning polynomials"];
  Return[{}]];
  
(* Calculate region bounds *)
startRegion = ImplicitRegion[pre, Evaluate[vars]];
regionCandidate = {};

(* Next we need to partition space *)
partitionSpace = {ImplicitRegion[allPolyFactors[[1]] == 0, Evaluate[vars]],
                  ImplicitRegion[allPolyFactors[[1]] > 0, Evaluate[vars]],
                  ImplicitRegion[allPolyFactors[[1]] < 0, Evaluate[vars]]};
partitionSpaceSigns = {{0}, {1}, {-1}};
(* Precomputes all regions in the abstraction *)
For[i = 2, i <= Length[allPolyFactors], i++,
  newPartitionSpace = {};
  newPartitionSpaceSigns = {};
  (* Intersect the i-th element with everything that comes before *)
  For[j = 1, j <= Length[partitionSpace], j++,
    newPartitionSpace = Join[newPartitionSpace,
      {RegionIntersection[partitionSpace[[j]], ImplicitRegion[allPolyFactors[[i]] == 0,Evaluate[vars]]],
       RegionIntersection[partitionSpace[[j]], ImplicitRegion[allPolyFactors[[i]] > 0,Evaluate[vars]]],
       RegionIntersection[partitionSpace[[j]], ImplicitRegion[allPolyFactors[[i]] < 0, Evaluate[vars]]]}];
    newPartitionSpaceSigns = Join[newPartitionSpaceSigns, {Append[partitionSpaceSigns[[j]], 0], Append[partitionSpaceSigns[[j]], 1], Append[partitionSpaceSigns[[j]], -1]}]
  ];
  partitionSpace = newPartitionSpace;
  partitionSpaceSigns = newPartitionSpaceSigns;
];

(* We need to know the signs of each region *)
(* Get rid of empty cells *)
(*partitionSpace = DeleteCases[partitionSpace, EmptyRegion[_]]; *)
For[i = 1, i <= Length[partitionSpace], i++, 
(*Print[partitionSpace[[i]]];*)
  If[Length[Cases[{partitionSpace[[i]]}, EmptyRegion[_]]] > 0,
    partitionSpace = Delete[partitionSpace, i];
    partitionSpaceSigns = Delete[partitionSpaceSigns, i];
    i = i-1;
  ];
];

If[Length[partitionSpace] == 0,
  Print["Unable to proceed: empty partition space"];
  Return[{}]];
  
(* partitionSpace tracks all the regions
  partitionSpaceSigns tracks the signs of polynomials in the list actualPolynomials in each corresponding region
*)

(*Print["Here is the paritioning of space"];
Print[partitionSpace];
Print["Here are the signs in that partition"];
Print[partitionSpaceSigns];*)

(* Sample points in each region *)
signList = {};
signTuple = {};
samplePoints = {};
pointMapList = {};
For[i = 1, i <= Length[partitionSpace], i++,
  pointInRegion = vars/.FindInstance[vars\[Element]partitionSpace[[i]],vars,Reals];
  (*Print["point: ",pointInRegion]*);
  samplePoints = Append[samplePoints, Flatten[pointInRegion]];
  pointMap = {};
  For[j = 1, j<= Length[vars], j++, pointMap = Append[pointMap, vars[[j]] -> pointInRegion[[1]][[j]]]];
  signTuple = Append[signTuple, f/.pointMap];
  pointMapList = Append[pointMapList, pointMap];
];
(*Print["sample points for each region"];
Print[samplePoints];*)

(* Now we'll compute transition relations *)
fringe = {};
(* Figure out which regions startRegion intersects *)
For[i = 1, i <= Length[partitionSpace], i++,
  (* TODO: is this equality efficient? *)
  If[Not[RegionIntersection[startRegion, partitionSpace[[i]]] === EmptyRegion[Length[vars]]],
    fringe = Append[fringe, partitionSpaceSigns[[i]]]
  ];
];
(*Print["Here is the fringe set: ",fringe]*);

(* Loop until stabilization *)
reachableRegions = {};
While[Length[fringe] > 0,

  (* Consider each region individually *)
  fringeElement = First[fringe];
  reachableRegions = Append[reachableRegions, fringeElement];
  fringe = Rest[fringe];

  (*Print["Here is the fringe element that we are considering: ",fringeElement];

  Print["This is paritionSpaceSigns"];
  (* Sometimes fringeElement doesn't have a position in partitionSpaceSigns.  That means that it 
  corresponds to an empty region.  But what does that mean geometrically? *)
  Print[partitionSpaceSigns];*)

  (* The position of this fringeElement in partitionSpaceSigns *)
  pos = Position[partitionSpaceSigns,fringeElement][[1]][[1]];
  polyChangeList = TestPolynomialChanges[allPolyFactors, 
  partitionSpace[[pos]],pos, 
  signTuple, samplePoints, vars,f];

  (*Print["Here is how the polynomials are changing: ",polyChangeList];
  Print["Computing the transition list for each polynomial"];*)

    transitionList = {};
  For[j = 1, j <= Length[polyChangeList], j++, 
    transitionSignList = {};
    transitionSignList = Append[transitionSignList, fringeElement[[j]]];
    If[fringeElement[[j]] > 0 && polyChangeList[[j]]< 0, transitionSignList = Append[transitionSignList, 0];];
    If[fringeElement[[j]] == 0 && polyChangeList[[j]]< 0, transitionSignList = Append[transitionSignList, -1];];
    If[fringeElement[[j]]< 0 && polyChangeList[[j]]> 0, transitionSignList = Append[transitionSignList, 0];];
    If[fringeElement[[j]] == 0 && polyChangeList[[j]]> 0, transitionSignList = Append[transitionSignList, 1];];
    (*Print[transitionSignList]*);
    transitionList = Append[transitionList, DeleteDuplicates[transitionSignList]];
  ];

  (*Print["transitionlist: ",transitionList];*)
  allTransitions = Tuples[transitionList];
  (* Probably need to add an extra check here to make sure that what we're adding to fringe actually makes geometric 
  sense.  But it seems like it shouldn't go wrong like this in the first place. *)
  For[i =1, i <=Length[allTransitions], i++, 
    (*If[Not[MemberQ[partitionSpaceSigns,allTransitions[[i]]]],Print["weird ",allTransitions[[i]]]];*)
    If[Not[MemberQ[reachableRegions, allTransitions[[i]]]] && MemberQ[partitionSpaceSigns,allTransitions[[i]]], fringe = Append[fringe, allTransitions[[i]]]]
  ];
  fringe = DeleteDuplicates[fringe];
];

positionOfRegionCand = Position[partitionSpaceSigns, reachableRegions[[1]]][[1]][[1]];
regionCandidate = partitionSpace[[positionOfRegionCand]];
For[i = 2, i <= Length[reachableRegions], i++, 
  positionOfRegionCand = Position[partitionSpaceSigns, reachableRegions[[i]]][[1]][[1]];
  regionCandidate = RegionUnion[regionCandidate, partitionSpace[[positionOfRegionCand]]];
];
(*Print["this is the invariant candidate: ",regionCandidate];*)

Primitives`WeakenInequalities[regionCandidate /.{ImplicitRegion[vv_,_] -> vv, FullRegion[_] -> True}]
]


End[]
EndPackage[]
