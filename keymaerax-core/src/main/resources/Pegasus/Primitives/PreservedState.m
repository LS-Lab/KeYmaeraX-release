(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["LZZ`",FileNameJoin[{Directory[],"Primitives","LZZ.m"}]]

BeginPackage["PreservedState`"];

PreservedPre::usage=
"PreservedPre[vectorField_List,vars_List,pre,domain]
A naive implementation for selecting invariants from the pre state conditions of the polynomial vector field.";

TimeTrigger::usage=
"TimeTrigger[vectorField_List,vars_List,domain]
Generates substitutions T -> (T-t) where t is a time-like variable"

Begin["`Private`"];

FlattenEq[ls_List]:= Module[{lss,res,skip,i,lhs,pos},
    res={};
    skip={};
    lss=Select[ls,Head[#]===Greater||Head[#]===GreaterEqual&];
    For[i=1,i<=Length[lss],i++,
      If[MemberQ[skip,i],Continue[]];
      lhs=lss[[i]][[1]];
      pos=Position[lss,_?(#[[1]]+lhs===0&),1,Heads->False]//Flatten;
      If[Length[pos]>0,
      res=Join[res,{lhs==0}]; skip=Join[skip,pos],
      res=Join[res,{lss[[i]]}]]
      ];
    Return[res];
]

TimeTrigger[vf_List,vars_List,domain_] := Module[
	{disjuncts,conjuncts,constRHS,candidates,subst,ls,i,rhses},
	disjuncts = Primitives`Disjuncts[Primitives`DNFNormalizeGtGeq[Simplify[domain]]];
    If[ListQ[disjuncts], Return[{}]];
    conjuncts = {disjuncts/.{And->List}}//Flatten;
    conjuncts = FlattenEq[conjuncts];
    
    (* the ODEs with "constant" RHS *)
    constRHS = Position[vf,_?(Intersection[Variables[#],vars]==={}&),{1},Heads->False]//Flatten;
    candidates = vars[[constRHS]];
    rhses=vf[[constRHS]];
    (* vars with bounds in the domain constraints >, \[GreaterEqual] *)
    subst={};
    For[i=1,i<=Length[candidates],i++,
    ls=Map[
      If[Head[#]===GreaterEqual || Head[#]===Greater,
      {#[[1]]+candidates[[i]]}, {}
      ]&, conjuncts]//Flatten;
    ls=Select[ls,Intersection[Variables[#],vars]==={}&];
    subst=Join[subst,Map[#->#-candidates[[i]]/rhses[[i]]&,ls]];
    ];
    Return[subst]
]

PreservedPre[vf_List, vars_List, pre_, domain_] :=
    Module[{normalized, disjuncts, conjunctLists, conjuncts, preserved, polys, poly,subst,cands},
     (*pre is usually in disjunctive normal form, see Dependency`FilterVars, but redo if called from somewhere else not in that form *)
     disjuncts = Primitives`Disjuncts[Primitives`DNFNormalizeGtGeq[Simplify[pre]]];
     If[ListQ[disjuncts], Return[{}]];
     
     conjuncts = {disjuncts/.{And->List}}//Flatten;
     conjuncts = FlattenEq[conjuncts];
     
     subst=TimeTrigger[vf,vars,domain];
     
     cands=Join[conjuncts,Map[conjuncts/.#&,subst]//Flatten];
     
    
     (* TODO: disjunctions *)
     preserved = {};
     Do[
         Print["f: ", f];
         If[TrueQ[TimeConstrained[LZZ`InvS[f, vf, vars, domain], 1, False]],
           AppendTo[preserved, f], Null],
         (* Simplify undoes the GtGeq normalization of Dependency`FilterVars to obtain equations again (reduces number of InvSDI calls) *)
         {f, cands}
     ];
     Print["Preserved ", preserved];
     preserved
    ]

End[]
EndPackage[]



