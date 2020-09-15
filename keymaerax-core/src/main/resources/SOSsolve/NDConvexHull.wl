(* ::Package:: *)

(*

The MIT License (MIT)

Copyright (c) 2016, by Loren Petrich

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

*)


BeginPackage["NDConvexHull`"]

CHNGiftWrapping::usage = "CHNGiftWrapping[vts] returns {sorted list of vertices, sorted list of simplexes} The simplexes are sorted with the last two indices reversed if needed so that the sorting will be an even permutation.  The gift wrapping algorithm is used."
CHNChanShattering::usage = "CHNChanShattering[vts] returns {sorted list of vertices, sorted list of simplexes} The simplexes are sorted with the last two indices reversed if needed so that the sorting will be an even permutation.  Chan's algorithm is used."
CHNQuickHull::usage = "CHNQuickHull[vts] returns {sorted list of vertices, sorted list of simplexes} The simplexes are sorted with the last two indices reversed if needed so that the sorting will be an even permutation.  The quick hull algorithm is used."
CH2QuickHull::usage = ""
CHNIncremental::usage = "CHNIncremental[vts] returns {sorted list of vertices, sorted list of simplexes} The simplexes are sorted with the last two indices reversed if needed so that the sorting will be an even permutation.  The incremental convex hull algorithm is used." 


Begin["`Private`"]

(* Indices of the minimum and maximum values *)

IndexMin[xlst_] := First[Ordering[xlst, 1]];

IndexMax[xlst_] :=  First[Ordering[xlst, -1]];

IndexMinBySortFunc[xlst_, sortfunc_] := 
 First[Ordering[xlst, 1, sortfunc]];

IndexMaxBySortFunc[xlst_, sortfunc_] := 
 First[Ordering[xlst, -1, sortfunc]];

IndexMinBySortByFunc[xlst_, sortbyfunc_] := 
 IndexMinBySortFunc[xlst, OrderedQ[{sortbyfunc[#1], sortbyfunc[#2]}] &];

IndexMaxBySortByFunc[xlst_, sortbyfunc_] := 
 IndexMaxBySortFunc[xlst, OrderedQ[{sortbyfunc[#1], sortbyfunc[#2]}] &];

MinBySortFunc[xlst_, sortfunc_] := 
 xlst[[IndexMinBySortFunc[xlst, sortfunc]]];

MaxBySortFunc[xlst_, sortfunc_] := 
 xlst[[IndexMaxBySortFunc[xlst, sortfunc]]];

MinBySortByFunc[xlst_, sortbyfunc_] := 
 xlst[[IndexMinBySortByFunc[xlst, sortbyfunc]]];

MaxBySortByFunc[xlst_, sortbyfunc_] := 
 xlst[[IndexMaxBySortByFunc[xlst, sortbyfunc]]];

(* Add indices -- (index,value) *)

AddIndices[xlst_] := Transpose[{Range[Length[xlst]], xlst}];

(* Select using list of conditions *)

SelWithList[sllst_, xlst_] := #[[2]] & /@ 
  Select[Transpose[{sllst, xlst}], #[[1]] &];

(* Rotate a list so that it starts with its minimum value *)

RotateToMin[xlst_] := Module[{ixmin},
  If[Length[xlst] > 0,
   ixmin = IndexMin[xlst];
   Join[Take[xlst, {ixmin, -1}], Take[xlst, {1, ixmin - 1}]],
   xlst
   ]
  ];

(* Connect the ends *)

MakeLoop[lst_] := If[Length[lst] > 0, Append[lst, First[lst]], {}];

(* Extract from Reap output *)

ExtractReaped[rpres_, k_] := Module[{rpi},
  rpi = rpres[[2, k]];
  If[Length[rpi] > 0, rpi[[1]], {}]
  ];

VecSqr[x_] := x.x;

(* Functions for simplexes: n-D generalizations of triangles and \
tetrahedra *)

(* Flips a simplex to get the opposite orientation. A single point \
ought to have a polarity, either begin or end of a line. *)

SimplexFlip[sx_] := 
  If[Length[sx] >= 2, Join[Drop[sx, -2], sx[[{-1, -2}]]], sx];

(* Gets a simplex into canonical order: sorted or sorted with last \
two interchanged *)

SimplexCanon[sx_] := 
  If[Signature[sx]*Signature[#] < 0, SimplexFlip[#], #] & @ Sort[sx];

(* Subsets of the simplex: one step down. Also references *)

SimplexSubs[sx_] := 
  Table[If[EvenQ[k], SimplexFlip[#], #] & @ Delete[sx, -k], {k, 
    Length[sx]}];

SimplexSubRefs[sx_, sxtosbsxs_, sbsxtosx_] := Module[{sbsxs, sbsx},
   sbsxs = SimplexSubs[sx];
   sxtosbsxs[sx] = sbsxs;
   Table[sbsxtosx[sbsx] = sx, {sbsx, sbsxs}]
   ];

(* Volume factor: true volume is 1/(# dims)! times it *)

SubFirstFromVecSet[vts_] := 
  Table[vt - #, {vt, Rest[vts]}] & @ First[vts];

SimplexVolume[vts_] := Det[SubFirstFromVecSet[vts]];

SimplexOrient[vts_] := SimplexVolume[vts] > 0;

(* For calculating several volumes *)

SimplexVolData[
   vts_] := {Mean[vts], (Cross @@ SubFirstFromVecSet[vts])};

SimplexVolEval[data_, vt_] := data[[2]].(vt - data[[1]]);

SimplexOrientEval[data_, vt_] := SimplexVolEval[data, vt] > 0;

(* Verification *)

SimplexVolDataTest[vts_] := 
  SimplexVolEval[SimplexVolData[Most[vts]], Last[vts]] - 
   SimplexVolume[vts];

SimplexVolDataTestArray[a_, n_] := 
  SimplexVolDataTest[Array[a, {n + 1, n}]] // Factor;

SimplexVolDataTestArrSet[a_, n_] := 
  Array[SimplexVolDataTestArray[a, #] &, n - 1, 2];

(* Circumscribed circle/sphere/hypersphere *)

CircumData[vts_] := Module[{vtsred, ctrx},
   vtsred = SubFirstFromVecSet[vts];
   ctrx = LinearSolve[vtsred, VecSqr /@ vtsred]/2;
   {First[vts] + ctrx, VecSqr[ctrx]}];

CircumEval[data_, vt_] := VecSqr[vt - data[[1]]] - data[[2]];

CircumInside[data_, vt_] := CircumEval[data, vt] <= 0;

CircumTest[vts_] := Module[{data}, data = CircumData[vts];
   CircumEval[data, #] & /@ vts];

CircumTestArray[a_, n_] := 
  CircumTest[Array[a, {n + 1, n}]] // Factor;

(* Equivalent to Det[{v1,v2}] *)
Cross2D[v1_,v2_] :=v1[[1]]*v2[[2]] - v1[[2]]*v2[[1]]
(* Edges and triangle-edge references *)
TriEdges[tri_] := {{tri[[1]],tri[[2]]},{tri[[2]],tri[[3]]},{tri[[3]],tri[[1]]}}
TriEdgeRefs[tri_,trieds_,edtri_] := Module[{eds,ed},
eds = TriEdges[tri];
trieds[tri] = eds;
Do[edtri[ed] = tri,{ed,eds}];
]
(* 2D triangle area. Factor of 1/2 ignored *)
TriArea2D[vts_] := Cross2D[vts[[2]]-vts[[1]],vts[[3]]-vts[[1]]]
(* 2D triangle orientation -- true if canonical *)
TriOrient2D[vts_] := TriArea2D[vts] > 0
(* Speed up testing of 2D triangle area and orientation *)
TriAreaData2D[vts_] := {Mean[vts],{-#[[2]],#[[1]]}& @ (vts[[2]] - vts[[1]])}
TriAreaEval2D[data_,vt_] := data[[2]].(vt - data[[1]])
TriOrientEval2D[data_,vt_] := TriAreaEval2D[data,vt] > 0

(* Assumes that the faces are already in canonical form *)

CHNDOutputFromSimplexes[hullfcs_] := Module[{hullvts, hull},
   hullvts = Union[Flatten[hullfcs]];
   hull = {hullvts, Sort[hullfcs]};
   hull
   ];

CHNGWMakeProjection[vts_] := Module[{refpt, diffs, trdiffs, pjmat},
  refpt = Mean[vts];
  diffs = SubFirstFromVecSet[vts];
  trdiffs = Transpose[diffs];
  pjmat = 
   IdentityMatrix[Length[First[vts]]] - 
    trdiffs.Inverse[diffs.trdiffs].diffs;
  {refpt, pjmat}
  ];

CHNGWPartProj[prj_, dir_] := prj[[2]].dir;

CHNGWProjectOut[prj_, vt_] := CHNGWPartProj[prj, vt - prj[[1]]];

CHNPartialGiftWrapping[vts_, indef_: True, nmax_: 0] := 
 Module[{nvts, ndims, ix0, vt, ixvts, ixvts1, ixvts11, ix1, face, 
   dvts, k, prj, ix, bdrysbfcs, bdryoppoverts, iscomplete, initial, n,
    res, sbfc, prevdir, fcsubfcs, fcoppoverts, bdrysel, fcsel, pos, 
   hullfcs},
  If[Length[vts] == 0, Return[{False, {{}, {}}}]];
  {nvts, ndims} = Dimensions[vts];
  If[ndims <= 2, Return[{False, {{}, {}}}]];
  (* Degenerate cases *)
  If[nvts < ndims,
   Return[{True, {Range[nvts], {}}}]
   ];
  If[! (indef || nmax > 0),
   Return[{False, {{}, {}}}]
   ];
  (* Find a farthest-out point *)
  ix0 = IndexMin[First /@ vts];
  vt = vts[[ix0]];
  (* Find the closest-to-outward point using its direction *)
  
  ixvts = AddIndices[vts];
  ixvts1 = Select[ixvts, #[[1]] != ix0 &];
  ixvts11 = {#[[1]], First[Normalize[#[[2]] - vt]]} & /@ ixvts1;
  ix1 = First[MinBySortByFunc[ixvts11, #[[2]] &]];
  ixvts1 = Select[ixvts1, #[[1]] != ix1 &];
  face = {ix0, ix1};
  (* Find the next closest-to-outward ones *)
  Do[
   prj = CHNGWMakeProjection[vts[[face]]];
   ixvts11 = {#[[1]], 
       First[Normalize[CHNGWProjectOut[prj, #[[2]]]]]} & /@ ixvts1;
   ix = First[MinBySortByFunc[ixvts11, #[[2]] &]];
   ixvts1 = Select[ixvts1, #[[1]] != ix &];
   AppendTo[face, ix],
   {k, ndims - 2}];
  (* Adjust the orientation of the initial face *)
  face = Sort[face];
  If[First[Cross @@ SubFirstFromVecSet[vts[[face]]]] < 0,
   face = SimplexFlip[face]
   ];
  iscomplete = False;
  initial = True;
  res = Reap[For[n = 0, indef || (n < nmax), n++,
     If[initial,
      (* Setup for the initial face *)
      Sow[face];
      bdrysbfcs = SimplexSubs[face];
      bdryoppoverts = Reverse[face];
      initial = False;
      Continue[]
      ];
     (* Find the remaining faces *)
     sbfc = bdrysbfcs[[1]];
     ix = bdryoppoverts[[1]];
     prj = CHNGWMakeProjection[vts[[sbfc]]];
     prevdir = - CHNGWProjectOut[prj, vts[[ix]]];
     (* Select the vertex that's closest to that direction. *)
     
     ixvts1 = Select[ixvts, ! MemberQ[sbfc, #[[1]]] &];
     ixvts1 = {#[[1]], 
         prevdir.Normalize[CHNGWProjectOut[prj, #[[2]]]]} & /@ 
       ixvts1;
     ix = First[MaxBySortByFunc[ixvts1, #[[2]] &]];
     (* Compose the new face from that vertex *)
     
     face = SimplexCanon[Append[SimplexFlip[sbfc], ix]];
     Sow[face];
     fcsubfcs = SimplexSubs[face];
     fcoppoverts = Reverse[face];
     (* Add its subfaces to the list of subfaces, 
     but subtract where they duplicate. *)
     
     bdrysel = ConstantArray[True, Length[bdrysbfcs]];
     fcsel = ConstantArray[True, Length[face]];
     Do[
      pos = Position[bdrysbfcs, SimplexFlip[fcsubfcs[[k]]]];
      If[Length[pos] > 0,
       ix = pos[[1, 1]];
       bdrysel[[ix]] = False;
       fcsel[[k]] = False
       ],
      {k, Length[face]}
      ];
     bdrysbfcs = 
      Join[SelWithList[bdrysel, bdrysbfcs], 
       SelWithList[fcsel, fcsubfcs]];
     bdryoppoverts = 
      Join[SelWithList[bdrysel, bdryoppoverts], 
       SelWithList[fcsel, fcoppoverts]];
     If[Length[bdrysbfcs] == 0,
      iscomplete = True;
      Break[]
      ]
     ]];
  hullfcs = res[[2, 1]];
  {iscomplete, CHNDOutputFromSimplexes[hullfcs]}
  ];

CHNGiftWrapping[vts_] := Module[{iscomplete, hull},
  {iscomplete, hull} = CHNPartialGiftWrapping[vts];
  If[iscomplete, hull, {{}, {}}]
  ];


GenChanShattering[vts_, HullVertices_, CHParts_, PartGiftWrap_, 
  MapVertices_] := 
 Module[{nvts, rng, nhtrial, nregs, seg, segs, shathulls, res, hull},
  nvts = Length[vts];
  (* Degenerate cases *)
  If[nvts <= 2, Return[CHParts[vts]]];
  (* Loop through trial lengths *)
  
  For[nhtrial = 3, True, nhtrial *= 3,
   nregs = Round[nvts/nhtrial];
   segs = Round[(nvts/nregs)*Range[0, nregs]];
   segs = (Range @@ (# + {1, 0})) & /@ Partition[segs, 2, 1];
   shathulls = Table[hull = CHParts[vts[[seg]]];
     seg[[HullVertices[hull]]],
     {seg, segs}];
   If[Length[shathulls] == 1,
    Break[]
    ];
   shathulls = Flatten[shathulls];
   res = PartGiftWrap[vts[[shathulls]], False, nhtrial];
   If[res[[1]],
    hull = MapVertices[shathulls, res[[2]]];
    Break[]
    ]
   ];
  hull
  ];

GenChanShattering[vts_, HullVertices_, CHParts_, PartGiftWrap_, 
  MapVertices_] := 
 Module[{nvts, rng, nhtrial, nregs, seg, segs, shathulls, res, hull},
  nvts = Length[vts];
  (* Degenerate cases *)
  If[nvts <= 2, Return[CHParts[vts]]];
  (* Loop through trial lengths *)
  
  For[nhtrial = 3, True, nhtrial *= 3,
   nregs = Round[nvts/nhtrial];
   segs = Round[(nvts/nregs)*Range[0, nregs]];
   segs = (Range @@ (# + {1, 0})) & /@ Partition[segs, 2, 1];
   shathulls = Table[hull = CHParts[vts[[seg]]];
     seg[[HullVertices[hull]]],
     {seg, segs}];
   If[Length[shathulls] == 1,
    Break[]
    ];
   shathulls = Flatten[shathulls];
   res = PartGiftWrap[vts[[shathulls]], False, nhtrial];
   If[res[[1]],
    hull = MapVertices[shathulls, res[[2]]];
    Break[]
    ]
   ];
  hull
  ]

CHNCSMapVertices[shathulls_, hull_] := If[Length[hull[[2]]] > 0,
  CHNDOutputFromSimplexes[shathulls[[#]] & /@ hull[[2]]],
  {SimplexCanon[shathulls[hull[[1]]]], {}}
  ];

CHNChanShattering[vts_, CHParts_: CHNGiftWrapping] := 
 GenChanShattering[vts, First, CHParts, CHNPartialGiftWrapping, 
  CHNCSMapVertices];


(* Find the faces visible from the a new vertex and replace them with \
ones containing the new vertex. Also returns the old faces and the \
new faces. *)
CHNVisFacesFromVert[vts_, origfaces_, startface_, ix_, fctosbfcs_, 
  sbfctofcs_, orient_] := 
 Module[{oldfaces, facestat, unchecked, nfaces, sbfc, k, face, facex, 
   newfaces, updfaces},
  oldfaces = {startface};
  (* Find which existing faces are visible from the vertex. 0 = 
  unchecked, 1 = visible, 2 = invisible *)
  facestat[startface] = 0;
  unchecked = True;
  While[unchecked,
   unchecked = False;
   nfaces = Length[oldfaces];
   Do[face = oldfaces[[k]];
    If[facestat[face] == 0, unchecked = True;
     (* Look at a face's neighboring faces *)
     
     Do[facex = sbfctofcs[SimplexFlip[sbfc]];
      If[Head[facestat[facex]] === facestat,
       AppendTo[oldfaces, facex];
       facestat[facex] = 0],
      {sbfc, fctosbfcs[face]}];
     facestat[face] = 
      If[orient[vts[[Append[SimplexFlip[face], ix]]]], 1, 2]],
    {k, nfaces}]
   ];
  (* Find the horizon subfaces, 
  those between visible and invisible faces, and the new faces *)
  
  newfaces = {};
  Do[If[facestat[face] == 1,
    Do[facex = sbfctofcs[SimplexFlip[sbfc]];
     If[facestat[facex] == 2,
      AppendTo[newfaces, SimplexCanon[Append[sbfc, ix]]]
      ],
     {sbfc, fctosbfcs[face]}
     ]
    ],
   {face, oldfaces}];
  Do[
   SimplexSubRefs[face, fctosbfcs, sbfctofcs] ,
   {face, newfaces}];
  (* Remove the old faces *)
  
  oldfaces = Select[oldfaces, facestat[#] == 1 &];
  updfaces = Join[Complement[origfaces, oldfaces], newfaces];
  {updfaces, oldfaces, newfaces}
  ];


(* Returns indices of positive-side vertices and the maximum-distance \
one *)
CHNQHExternalVertices[vts_, vtixs_, face_] := 
 Module[{fdval, ixvts, ixpos, ixmax},
  fdval = SimplexVolData[vts[[SimplexFlip[face]]]];
  ixvts = {#, SimplexVolEval[fdval, vts[[#]]]} & /@ vtixs;
  ixpos = #[[1]] & /@ Select[ixvts, #[[2]] > 0 &];
  ixmax = If[Length[ixvts] > 0,
    #[[1]] & @ MaxBySortByFunc[ixvts, #[[2]] &],
    Null];
  {ixpos, ixmax}
  ];

CHNQuickHull[vts_] := 
 Module[{nvts, ndims, hullvts, hullfcs, hull, ixvts, ix, ixinit, 
   vtstrim, k, ixvtarea, face, fctosbfcs, sbfctofcs, extsfs, kx, evs, 
   ixmax, oldfcs, newfcs},
  If[Length[vts] == 0, Return[{{}, {}}]];
  {nvts, ndims} = Dimensions[vts];
  If[ndims <= 2, Return[{{}, {}}]];
  (* Degenerate cases *)
  If[nvts <= ndims,
   hullvts = Range[nvts];
   hullfcs = If[nvts == ndims,
     {hullvts, SimplexFlip[hullvts]},
     {}
     ];
   hull = {hullvts, hullfcs};
   Return[hull]
   ];
  ixvts = Range[nvts];
  ixinit = {};
  (* First two points *)
  vtstrim = First /@ vts;
  ix = IndexMin[vtstrim];
  AppendTo[ixinit, ix];
  ix = IndexMax[vtstrim];
  AppendTo[ixinit, ix];
  ixvts = Complement[ixvts, ixinit];
  (* Remaining points *)
  Do[
   vtstrim = Take[#, k] & /@ vts;
   ixvtarea = {#, 
       Abs[SimplexVolume[vtstrim[[Append[ixinit, #]]]]]} & /@ ixvts;
   ix = MaxBySortByFunc[ixvtarea, #[[2]] &][[1]];
   AppendTo[ixinit, ix];
   ixvts = Complement[ixvts, {ix}],
   {k, 2, ndims}];
  ixinit = Sort[ixinit];
  If[! SimplexOrient[vts[[ixinit]]], ixinit = SimplexFlip[ixinit]];
  hullfcs = SimplexSubs[ixinit];
  (* Find the subfaces for each face *)
  
  Do[SimplexSubRefs[face, fctosbfcs, sbfctofcs];
   extsfs[face] = CHNQHExternalVertices[vts, ixvts, face],
   {face, hullfcs}];
  While[True,
   (* Search for a face with vertices outside of it *)
   kx = Null;
   Do[face = hullfcs[[k]];
    {evs, ixmax} = extsfs[face];
    If[Length[evs] > 0,
     (* Found a non-empty outside volume *)
     kx = k;
     Break[]
     ],
    {k, Length[hullfcs]}];
   If[kx === Null, Break[]];
   (* Get updated hull faces, old faces (removed), 
   and new faces (added) *)
   {hullfcs, oldfcs, newfcs} = 
    CHNVisFacesFromVert[vts, hullfcs, face, ixmax, fctosbfcs, 
     sbfctofcs, SimplexOrient];
   (* Find the outward points for the new faces. 
   Start with all those for the old faces. *)
   
   evs = Union @@ (extsfs[#][[1]] & /@ oldfcs);
   evs = Complement[evs, {ixmax}];
   Do[
    extsfs[face] = CHNQHExternalVertices[vts, evs, face],
    {face, newfcs}]
   ];
  CHNDOutputFromSimplexes[hullfcs]
  ];


CHNGenIncremental[vts_, extradims_, orient_, datafunc_, dataorient_] := 
 Module[{nvts, ndims, hullvts, hullfcs, hull, facedata, face, 
   fctosbfcs, sbfctofcs, ix, kx, k, oldfcs, newfcs},
  If[Length[vts] == 0, Return[{{}, {}}]];
  {nvts, ndims} = Dimensions[vts];
  ndims -= extradims;
  If[ndims <= 2, Return[{{}, {}}]];
  (* Degenerate cases *)
  If[nvts < ndims,
   hullvts = Range[nvts];
   hullfcs = {};
   hull = {hullvts, hullfcs};
   Return[hull]
   ];
  hullvts = Range[ndims];
  hullfcs = {hullvts, SimplexFlip[hullvts]};
  Do[facedata[face] = datafunc[vts[[SimplexFlip[face]]]];
   SimplexSubRefs[face, fctosbfcs, sbfctofcs],
   {face, hullfcs}];
  Do[
   kx = Null;
   Do[face = hullfcs[[k]];
    If[dataorient[facedata[face], vts[[ix]]],
     kx = k;
     Break[]
     ],
    {k, Length[hullfcs]}];
   If[kx === Null, Continue[]];
   {hullfcs, oldfcs, newfcs} = 
    CHNVisFacesFromVert[vts, hullfcs, face, ix, fctosbfcs, sbfctofcs, 
     orient];
   If[Length[hullfcs] == 0, Break[]];
   Do[facedata[face] = datafunc[vts[[SimplexFlip[face]]]],
    {face, newfcs}],
   {ix, ndims + 1, nvts}];
  CHNDOutputFromSimplexes[hullfcs]
  ];

CHNIncremental[vts_] := 
 CHNGenIncremental[vts, 0, SimplexOrient, SimplexVolData, 
  SimplexOrientEval];

CH2QHExternalVertices[vts_,vtixs_,seg_] := Module[{tdval,ixvts,ixpos,ixmax},
	(* ixvts = {#,TriArea2D[vts[[{seg[[2]],seg[[1]],#}]]]}& /@ vtixs; *)
	tdval =  TriAreaData2D[vts[[seg[[{2,1}]]]]];
	ixvts = {#,TriAreaEval2D[tdval,vts[[#]]]}& /@ vtixs;
	ixpos = #[[1]]& /@ Select[ixvts,#[[2]]>0&];
	ixmax = If[Length[ixvts] > 0,
	#[[1]]& @ MaxBySortByFunc[ixvts,#[[2]]&],
	Null];
	{ixpos,ixmax}
];

CH2QuickHull[vts_] := Module[{nvts,ix1,ix2,ixvts,tdval,ixvtria,ivtng,ivtps,ixps,ixng,taps,tang,ix3,hull,k,kn,hlen,seg,extvts,kx,kxn,evsimx,evs,ixh,ixhn,ixmax,seg1,seg2},
	(* Degenerate cases *)
	nvts = Length[vts];
	If[nvts <= 2,Return[Range[nvts]]];
	(* Starting points: first two *)
	ix1 = IndexMin[First /@ vts];
	ix2 = IndexMax[First /@ vts];
	(* Starting points: third one *)
	ixvts = Complement[Range[nvts],{ix1,ix2}];
	(* ixvtria = {#,TriArea2D[vts[[{ix1,ix2,#}]]]}& /@ ixvts; *)
	tdval = TriAreaData2D[vts[[{ix1,ix2}]]];
	ixvtria = {#,TriAreaEval2D[tdval,vts[[#]]]}& /@ ixvts;
	ivtng = MinBySortByFunc[ixvtria,#[[2]]&];
	ivtps = MaxBySortByFunc[ixvtria,#[[2]]&];
	ixng = ivtng[[1]];
	ixps = ivtps[[1]];
	tang = - ivtng[[2]];
	taps = ivtps[[2]];
	hull = If[taps >= tang,
	ix3 = ixps;
	{ix1,ix2,ix3},
	ix3 = ixng;
	{ix2,ix1,ix3}];
	ixvts = Complement[ixvts,{ix3}];
	(* Find the outward vertices for each edge *)
	hlen = Length[hull];
	Do[kn = Mod[k,hlen]+1;
		seg =hull[[{k,kn}]];
		extvts [seg] = CH2QHExternalVertices[vts,ixvts,seg],
		{k,hlen}];
	While[True,
	(* Search for an edge with outward points *)
	kx = Null;
	kxn = Null;
	hlen = Length[hull];
	Do[
	kn = Mod[k,hlen]+1;
	seg = hull[[{k,kn}]];
	evsimx = extvts[seg];
	evs = evsimx[[1]];
	ixmax = evsimx[[2]];
	If[Length[evs] > 0,
	kx = k;
	kxn = kn;
	Break[]
	],
	{k,hlen}];
	If[kx === Null,Break[]];
	(* Find a point on the hull from it *)
	ixh = hull[[kx]];
	ixhn = hull[[kxn]];
	evs = Complement[evs,{ixmax}];
	hull = If[kxn < kx,Join[Take[hull,{kxn,kx}],{ixmax}],
	Join[Take[hull,{kxn,-1}],Take[hull,{1,kx}],{ixmax}]];
	(* Find the outward points for the new hull segments *)
	seg1 = {ixh,ixmax};
	seg2 = {ixmax,ixhn};
	extvts[seg1] = CH2QHExternalVertices[vts,evs,seg1];
	extvts[seg2] = CH2QHExternalVertices[vts,evs,seg2];
];
RotateToMin[hull]
]
  
End[];
EndPackage[];

