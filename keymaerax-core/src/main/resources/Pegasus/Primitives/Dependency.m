(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] (* Load primitives package *)


(* ::Input:: *)
(*(* Polynomial generation for qualitative analysis *)*)


BeginPackage["Dependency`"];


FilterVars::usage="FilterVar[problem,fvars] filters problem to keep only pre/post/ODEs about fvars";
VariableDependencies::usage="VariableDependencies[problem] finds the dependency clusters in a problem";


Begin["`Private`"];


FilterAtom[formula_,vars_]   :=  Module[{},formula/.{
	Equal[a_,b_]        :>  If[SubsetQ[vars,Variables[a+b]],Equal[a,b],{}],
	Unequal[a_,b_]      :>  If[SubsetQ[vars,Variables[a+b]],Unequal[a,b],{}],
	Greater[a_,b_]      :>  If[SubsetQ[vars,Variables[a+b]],Greater[a,b],{}],
	GreaterEqual[a_,b_] :>  If[SubsetQ[vars,Variables[a+b]],GreaterEqual[a,b],{}],
	Less[a_,b_]         :>  If[SubsetQ[vars,Variables[a+b]],Less[a,b],{}], 
	LessEqual[a_,b_]    :>  If[SubsetQ[vars,Variables[a+b]],LessEqual[a,b],{}]
}];


FilterTrue[formula_] :=  Module[{},formula/.{
	{}        :>  True
}];


FilterDrop[formula_]:=Module[{},formula/.{
  HoldPattern[And[a__]] :>And@@(Select[Map[FilterDrop,a//List],Not[ListQ[#]]&]),
  HoldPattern[Or[a__]] :>Or@@(Select[Map[FilterDrop,a//List],Not[ListQ[#]]&])
 }];


FilterVars[problem_List,fvars_]:=Module[{
pre,f,vars,Q,post,
prefil,Qfil,postfil,
ffil,varsfil
},
{pre,{f,vars,Q},post}=problem;
If[Not[IntersectingQ[fvars,vars]],
	Print["No vars left after filtering! Filter ignored."];
	Return[problem]];
prefil = FilterAtom[pre,fvars]//FilterTrue;
Qfil = FilterAtom[Q,fvars]//FilterTrue;
postfil = (FilterAtom[post,fvars]//FilterDrop)/.{ {} :> False };
{ffil,varsfil}=Transpose[Select[Transpose[{f,vars}],MemberQ[fvars,#[[2]]]&]];

Return[{prefil,{ffil,varsfil,Qfil},postfil}];
];


VariableDependenciesHelper[vectorField_List,stateVars_List]:=Module[{
Jac=Map[Grad[#,stateVars]&, vectorField], returnList, listElement, i, j, AdjMatEarly, AdjMat, AdjGraph, AdjGraphClose
},
(* Compute the adjacency matrix for the system  *)
AdjMatEarly=Map[If[TrueQ[Simplify[#==0]],0,1]&,Jac, {2}];
AdjGraph=AdjacencyGraph[stateVars,AdjMatEarly, VertexLabels->"Name"];
AdjGraphClose = TransitiveClosureGraph[AdjGraph];
(*Print[AdjGraph];
Print["Closure: ",AdjGraphClose];*)
AdjMat = AdjacencyMatrix[AdjGraphClose];
(*Print[AdjMat];
Print[vectorField];
Print[AdjMatEarly];
*)(* Use the adjacency matrix to find variable dependencies *)
returnList = {};
For[i = 1, i <= Length[stateVars], i++,
listElement = {stateVars[[i]]};
For[j = 1 , j <=Length[stateVars], j++,
If[AdjMat[[i]][[j]] == 1, listElement = Append[listElement,  stateVars[[j]]]];
];
returnList = Append[returnList, listElement//DeleteDuplicates//Sort]
];
returnList = DeleteDuplicates[returnList];
returnList = SortBy[returnList, Length];
Return[returnList];
];
VariableDependencies[problem_List]:=Module[
{pre,f,vars,Q,post, varsList},
{pre,{f,vars,Q},post}=problem;
Return[VariableDependenciesHelper[f, vars]]
];


End[]
EndPackage[];
