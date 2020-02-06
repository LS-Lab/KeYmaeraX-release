(* ::Package:: *)

(* A draft generic strategy:
1) Find first integrals
*)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]];
Needs["Dependency`",FileNameJoin[{Directory[],"Primitives","Dependency.m"}]];
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]];
Needs["DarbouxDDC`",FileNameJoin[{Directory[],"Strategies","DarbouxDDC.m"}]];
Needs["Helper`",FileNameJoin[{Directory[],"Strategies","Helper.m"}]];
Needs["DiffSaturation`",FileNameJoin[{Directory[],"Strategies","DiffSaturation.m"}]]


BeginPackage[ "Generic`"];


(* Precomputes some ODE-specific information *)
Precompute::usage="Precompute[ode_List]";
(* TODO: name this properly *)
DiffSplit::usage="DiffSplit[problem_List]";


Begin["`Private`"];


PrecomputeDbx[ode_List]:=Module[{vf,vars,Q},
{vf,vars,Q} = ode;
(* TODO: fix timeouts *)
DarbouxDDC`DarbouxPolynomialsM[{vf,vars,Q}, 2, Max[5-Length[vars],1]]]


PrecomputeFIs[ode_List]:=Module[{vf,vars,Q},
{vf,vars,Q} = ode;
Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vf,vars,Q},Max[5-Length[vars],1]],vars]]


Precompute[ode_List]:=Module[{vf,vars,Q,deps,subs,dbx,fIs},
{vf,vars,Q} = ode;
deps = Join[Dependency`VariableDependenciesHelper[vf,vars],{vars}];
Print["Dependencies: ",deps];
subs=Map[Dependency`FilterVars[{True,ode,True},#][[2]]&,deps]//DeleteDuplicates;
(*dbx=Map[PrecomputeDbx,subs]//Flatten//DeleteDuplicates;
Print["Dbx: ",dbx];*)
(* TODO: somehow make use of dbx to generate rational FIs? *)
(* TODO: ignore Dbx that are first integrals *)
fIs=Map[PrecomputeFIs,subs]//Flatten//DeleteDuplicates;
Print["FIs: ",fIs];
(* TODO: add algebraic invariants *)
fIs
]


AugmentFIs[prob_List,fIs_List]:=Module[{pre,vf,vars,Q,post,reps,fIconj,constvars,constQ},
If[Length[fIs]==0, Return[prob]];
{{pre,{vf,vars,Q},post,{constvars,constQ}},reps} = Helper`InjectOld[prob];
fIconj = Map[#==(#//.reps)&,fIs]//.List->And;
{pre,{vf,vars,And[Q,fIconj]},post,{constvars,constQ}}
];



DiffSplit[prob_List, opts:OptionsPattern[]]:=Catch[Module[
{pre,post,f,vars,Q,fIs,dbx,pre1,post1,probs,augprob,constvars,constQ},

{pre, { f, vars, Q }, post, {constvars,constQ}}=prob;
Print["Input Problem: ",prob];
fIs = Precompute[prob[[2]]];
augprob = AugmentFIs[prob,fIs];

DiffSaturation`DiffSat[augprob]
]]


End[]
EndPackage[];
