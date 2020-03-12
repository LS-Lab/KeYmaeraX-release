(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]]

BeginPackage["PreservedState`"];

PreservedPre::usage=
"PreservedPre[vectorField_List,vars_List,pre,domain]
A naive implementation for selecting invariants from the pre state conditions of the polynomial vector field.";

Begin["`Private`"];

PreservedPre[vf_List, vars_List, pre_, domain_] :=
    Module[{normalized, conjuncts, preserved, polys},
     normalized = Primitives`CNFNormalizeGtGeq[pre];
     conjuncts = Primitives`Conjuncts[pre];
     preserved = {};
     Do[If[TrueQ[TimeConstrained[LZZ`InvSFast[f, vf, vars, domain], 1, False]],
       AppendTo[preserved, f], Null], {f, conjuncts}];
     (*Scan[If[
      TimeConstrained[LZZ`InvSFast[#, vf, vars, domain], 1, False],
      AppendTo[preserved, #], Null] &, normalized];*)
     (*Extracting left-hand sides since invariant extractor expects polynomials, not formulas*)
     polys = Map[Primitives`GtGeqLhs,preserved];
     (*TODO: Filter duplicate left-hand sides due to equalities*)
     Return[polys]
    ]

End[]
EndPackage[]
