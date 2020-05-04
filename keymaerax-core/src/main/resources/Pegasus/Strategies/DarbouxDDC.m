(* ::Package:: *)

(* Description: Generic strategies for non-linear vector fields. *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]] 
Needs["DarbouxPolynomials`",FileNameJoin[{Directory[],"Primitives","DarbouxPolynomials.m"}]]


BeginPackage[ "DarbouxDDC`"]


DarbouxPolynomialsM::usage="DarbouxPolynomialsM[problem,time,maxdeg] finds Darboux
   polynomials for the problem with a given timeout and maxdegree";
DarbouxDDCWeakIn::usage="DarbouxDDCWeakIn[problem_List]";
DarbouxDDCStrongIn::usage="DarbouxDDCStrongIn[problem_List]";


Begin["`Private`"];


DarbouxPolynomialsM[ode_List,time_,maxdeg_Integer]:=Catch[Module[{f,vars,Q,deg,dbx,realdbx,i},
{f,vars,Q}=ode;

dbx={};
TimeConstrained[For[i=1,i<=maxdeg,i++,
  dbx=Union[dbx,DarbouxPolynomials`DbxDefault[{f,vars,Q}, i]]],time];
Print["Generated Darboux polynomials: ",dbx];
Throw[dbx]
]]


TestConsistency[vars_, pre_, post_] := Module[{},
Return[Resolve[Exists[Evaluate[vars], pre && post], Reals]];
]


DarbouxDDCWeakIn[problem_List]:=Module[{pre,post,vf,vars,Q,fIs,maxVs,minVs,deg,rat,DPList,DPIneqList,item,prob, i,j, returnList, returnListRefined},
{pre, { vf, vars, Q }, post} = problem;
DPList = DarbouxPolynomialsM[{vf,vars,Q}, 10, Max[10-Length[vars],1]];

(* Note that if there are no Darboux polynomials, a list containing the original problem will be returned *)
returnList = {};
returnList = Append[returnList, {pre, { vf, vars, Q }, post}];

For[i = 1, i <= Length[DPList], i++, 
	returnListRefined = {};
	item = DPList[[i]];
	For[j = 1, j <= Length[returnList], j++, 
		prob = returnList[[j]];
		If[TestConsistency[vars, pre, Q&&item >= 0], returnListRefined = Append[returnListRefined, {prob[[1]]&&item>=0, {prob[[2]][[1]], prob[[2]][[2]], prob[[2]][[3]]&& item >= 0}, prob[[3]]}]];
		If[TestConsistency[vars, pre, Q&&item <= 0], returnListRefined = Append[returnListRefined, {prob[[1]]&&item<=0, {prob[[2]][[1]], prob[[2]][[2]], prob[[2]][[3]]&& item <= 0}, prob[[3]]}]];
	];
	returnList = returnListRefined;
];

Return[returnList];
]


DarbouxDDCStrongIn[problem_List]:=Module[{pre,post,vf,vars,Q,fIs,maxVs,minVs,deg,rat,DPList,DPIneqList,item,prob, i,j, returnList, returnListRefined},
{pre, { vf, vars, Q }, post} = problem;
DPList = DarbouxPolynomialsM[{vf,vars,Q}, 10, Max[10-Length[vars],1]];

(* Note that if there are no Darboux polynomials, a list containing the original problem will be returned *)
returnList = {};
returnList = Append[returnList, {pre, { vf, vars, Q }, post}];

For[i = 1, i <= Length[DPList], i++, 
	returnListRefined = {};
	item = DPList[[i]];
	For[j = 1, j <= Length[returnList], j++, 
		prob = returnList[[j]];
		If[TestConsistency[vars, pre, Q&&item == 0], returnListRefined = Append[returnListRefined, {prob[[1]]&&item==0, {prob[[2]][[1]], prob[[2]][[2]], prob[[2]][[3]]&& item == 0}, prob[[3]]}]];
		If[TestConsistency[vars, pre, Q&&item > 0], returnListRefined = Append[returnListRefined, {prob[[1]]&&item>0, {prob[[2]][[1]], prob[[2]][[2]], prob[[2]][[3]]&& item > 0}, prob[[3]]}]];
		If[TestConsistency[vars, pre, Q&&item < 0], returnListRefined = Append[returnListRefined, {prob[[1]]&&item<0, {prob[[2]][[1]], prob[[2]][[2]], prob[[2]][[3]]&& item < 0}, prob[[3]]}]];
	];
	returnList = returnListRefined;
];

Return[returnList];
]


DarbouxList[problem_List]:=Module[{pre,post,vf,vars,Q,fIs,maxVs,minVs,deg,rat},
{pre, { vf, vars, Q }, post} = problem;

Print[pre];
Print[post];
vars
]


End[];
EndPackage[];
