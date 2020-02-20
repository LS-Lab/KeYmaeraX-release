(* ::Package:: *)

(* A draft generic strategy *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]];
Needs["Dependency`",FileNameJoin[{Directory[],"Primitives","Dependency.m"}]];
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]];
Needs["DarbouxDDC`",FileNameJoin[{Directory[],"Strategies","DarbouxDDC.m"}]];
Needs["Helper`",FileNameJoin[{Directory[],"Strategies","Helper.m"}]];
Needs["DiffSaturation`",FileNameJoin[{Directory[],"Strategies","DiffSaturation.m"}]]


BeginPackage[ "Generic`"];


(* Precomputes some ODE-specific information *)
PrecomputeFIs::usage="PrecomputeFIs[ode_List]";
PrecomputeDbx::usage="PrecomputeDbx[ode_List]";
(* TODO: name this properly *)
DiffSplit::usage="DiffSplit[problem_List]";


Begin["`Private`"];


PrecomputeDbxM[ode_List]:=Module[{vf,vars,Q},
{vf,vars,Q} = ode;
DarbouxDDC`DarbouxPolynomialsM[{vf,vars,Q}, 20, Max[6-Length[vars],1]]]


PrecomputeDbx[ode_List, deps_List]:=Module[{vf,vars,Q,subs,dbx,fIs},
{vf,vars,Q} = ode;
subs=Map[Dependency`FilterVars[{True,ode,True},#][[2]]&,deps]//DeleteDuplicates;
fIs=Map[PrecomputeDbxM,subs]//Flatten//DeleteDuplicates;
fIs
]


PrecomputeFIsM[ode_List]:=Module[{vf,vars,Q},
{vf,vars,Q} = ode;
Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vf,vars,Q},Max[5-Length[vars],1]],vars]]


PrecomputeFIs[ode_List, deps_List]:=Module[{vf,vars,Q,subs,dbx,fIs},
{vf,vars,Q} = ode;
subs=Map[Dependency`FilterVars[{True,ode,True},#][[2]]&,deps]//DeleteDuplicates;
fIs=Map[PrecomputeFIsM,subs]//Flatten//DeleteDuplicates;
fIs
]


AugmentFIs[prob_List,fIs_List]:=Module[{pre,vf,vars,Q,post,reps,fIconj,constvars,constQ},
If[Length[fIs]==0, Return[prob]];
{{pre,{vf,vars,Q},post,{constvars,constQ}},reps} = Helper`InjectOld[prob];
fIconj = Map[#==(#//.reps)&,fIs]//.List->And;
{pre,{vf,vars,And[Q,fIconj]},post,{constvars,constQ}}
];



Reducible[p_, ps_List] := Module [{},
MemberQ[Flatten[Map[PolynomialReduce[p,#,Variables[p]][[1]][[1]]&,ps]],1]
]


TestConsistency[vars_, pre_, post_] := Module[{},
Return[Resolve[Exists[vars, pre && post], Reals]];
]


AddToPre[prob_ ,premore_] := Module[{pre,f,vars,Q,post,constvars,constQ},

{pre, { f, vars, Q }, post, {constvars,constQ}} = prob;
{pre && premore, { f, vars, Q &&premore }, post, {constvars,constQ}}
]


GenerateRatFI[dbx_,vf_,vars_] :=Module[{cofactors},
If[Length[dbx]==0,Return[{}]];
cofactors=FirstIntegrals`DbxCofactors[dbx,vf,vars];
(*Print["rational: ",dbx,cofactors,vars];*)
FirstIntegrals`RatFIGen[dbx,cofactors,vars]
]


(* Recursive DDC-ification -- pre \[Equal] continue proof, False \[Equal] no branch*)
ConstrainedDDC[dbxs_List, pre_, vars_, added_, polys_, vf_, cont_] := Module[{lt,eq,gt,hd,tl},

If[Length[dbxs]==0,
	(* Run the "continuation" *)
	Return[cont[added, GenerateRatFI[polys,vf,vars]]]];

{hd}=Take[dbxs,1];
tl=Rest[dbxs];
(* dbx < 0*)
lt=TestConsistency[Join[vars],pre && added, hd < 0];
eq=TestConsistency[Join[vars],pre && added, hd == 0];
gt=TestConsistency[Join[vars],pre && added, hd > 0];
{hd,
If[lt,ConstrainedDDC[tl, pre, vars, added && hd<0, Join[polys,{hd}], vf, cont],False],
If[eq,ConstrainedDDC[tl, pre, vars, added && hd==0, polys, vf, cont],False],
If[gt,ConstrainedDDC[tl, pre, vars, added && hd>0, Join[polys,{hd}], vf, cont],False]}
]


DiffSplit[prob_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,post,f,vars,Q,fIs,dbx,pre1,post1,probs,augprob,constvars,constQ,deps,cont},

{pre, { f, vars, Q }, post, {constvars,constQ}} = prob;
Print["Input Problem: ",prob];

deps = Join[Dependency`VariableDependenciesHelper[f,vars],{vars}];
Print["Dependencies: ",deps];

fIs = PrecomputeFIs[prob[[2]],deps];
Print["First integrals: ", fIs];

dbx = PrecomputeDbx[prob[[2]],deps];
(* Forget about first integrals *)
dbx=Select[dbx, Not[TrueQ[Simplify[Grad[#,vars].f]==0]] &];
Print["Filtered Darboux polynomials: ",dbx];

SetOptions[GenericNonLinear`FirstIntegrals,Timeout->0];
SetOptions[GenericNonLinear`DbxPoly,Timeout->0];
SetOptions[GenericNonLinear`HeuInvariants,Timeout->40];
SetOptions[GenericNonLinear`BarrierCert,Timeout->Infinity];
(*SetOptions[DiffSaturation`DiffSat,UseDependencies\[Rule]False];*)

cont[add_,ratFIs_]:=Block[{prob2,prob3},
Print["Continuing with: ",add,ratFIs];

prob2=AugmentFIs[prob,Join[fIs,ratFIs]];
prob3=AddToPre[prob2,add];
Print[prob3];
DiffSaturation`DiffSat[prob3]
];

ConstrainedDDC[dbx, pre&&Q&&constQ, Join[vars,constvars], True, {}, f, cont]

]]


End[]
EndPackage[];
