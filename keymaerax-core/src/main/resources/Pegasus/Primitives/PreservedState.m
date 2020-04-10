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
     conjunctLists = Map[({# /. {And->List}}//Flatten)&, disjuncts];
     Print["Filtering conjuncts ", conjunctLists];
     preserved = {};
     Do[
         p = {};
         (*Print["conj",conjuncts];*)
         Do[
         If[TimeConstrained[LZZ`InvSDI[f, vf, vars, domain], 1, False],
             AppendTo[p, f], Null],
             (* Simplify undoes the GtGeq normalization of Dependency`FilterVars to obtain equations again (reduces number of InvSDI calls) *)
             {f, ({Simplify[conjuncts/.{List->And}]/.{And->List}}//Flatten)/.{{True} -> {}} }];
         AppendTo[preserved, p]
         ,
         {conjuncts, conjunctLists}
     ];
     Print["Preserved ", preserved];
     (* TODO disjunctions *)
     If[Length[preserved] >= 1, preserved[[1]], {}]
    ]

End[]
EndPackage[]
