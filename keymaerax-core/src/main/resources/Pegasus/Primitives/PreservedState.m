(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]]

BeginPackage["PreservedState`"];

PreservedPre::usage=
"PreservedPre[vectorField_List,vars_List,pre,domain]
A naive implementation for selecting invariants from the pre state conditions of the polynomial vector field.";

Begin["`Private`"];

PreservedPre[vf_List, vars_List, pre_, domain_] :=
    Module[{normalized, disjuncts, conjunctLists, conjuncts, preserved, polys, poly},
     (*pre is usually in disjunctive normal form, see Dependency`FilterVars, but redo if called from somewhere else not in that form *)
     disjuncts = Primitives`Disjuncts[Primitives`DNFNormalizeGtGeq[pre]];
     disjuncts = If[ListQ[disjuncts], disjuncts, { disjuncts }];
     conjunctLists = Map[Primitives`Conjuncts, disjuncts];
     Print["Filtering conjuncts ", conjunctLists];
     preserved = {};
     Do[
         p = {};
         Do[If[TimeConstrained[LZZ`InvSFast[f, vf, vars, domain], 1, False],
             AppendTo[p, f], Null], {f, conjuncts}];
         AppendTo[preserved, p]
         ,
         {conjuncts, conjunctLists}
     ];
     Print["Preserved ", preserved];
     (* TODO interfaces are not ideal: want original precondition in (not DNF) and write formulas out *)
     (* Extract left-hand sides since invariant extractor expects polynomials, not formulas *)
     polys = Map[Primitives`GtGeqLhs, preserved//DeleteDuplicates];
     (* Map disjunction p1>0&p2>=0 | p3>=0 | p4>=0 to Max[Min[p1,p2],p3,p4] *)
     poly = { Fold[Max, If[Length[polys] > 1, Map[Fold[Min, #] &, polys], polys]] }//Flatten;
     Return[poly]
    ]

End[]
EndPackage[]
