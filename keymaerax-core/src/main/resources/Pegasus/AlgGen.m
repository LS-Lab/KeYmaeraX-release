(* ::Package:: *)

(* Copyright (c) Carnegie Mellon University, 2019.
 * See LICENSE.txt for the conditions of this license.
 *)


Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["FirstIntegrals`",FileNameJoin[{Directory[],"Primitives","FirstIntegrals.m"}]]
Needs["DarbouxDDC`",FileNameJoin[{Directory[],"Strategies","DarbouxDDC.m"}]]
Needs["LinearAlgebraicInvariants`",FileNameJoin[{Directory[],"Primitives","LinearAlgebraicInvariants.m"}]]


BeginPackage["AlgGen`"];
(* top-level interface for generating an algebraic invariant 
	p = 0
	for a given ODE and initial condition
	todo: possibly consider non-algebraic invariants like p>0 found using dbx, etc. *)


FindAlgs::usage="FindAlgs[system_List] Generate first integrals";
(* FindDBXs::usage="FindDBXs[system_List] Generate Darboux polynomials"; *)


Begin["`Private`"]


FindAlgs[systems_List, opts:OptionsPattern[]]:=Catch[Module[
{vf,vars,init,fIs,prefIs,DEFAULTDEG,subst,fIinst,fIAlg,linalg},
{vf,vars,init}=systems;
If[Length[vf]!=Length[vars] || Length[vars]!=Length[init],
	Print["Input malformed: ",systems];
	Return[{}]
];
DEFAULTDEG=5;
subst=MapThread[#1->#2&,{vars,init}];
fIs=Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vf,vars,True},DEFAULTDEG],vars];
fIinst=Map[#/.subst&,fIs];
fIAlg=MapThread[#1-#2&,{fIs,fIinst}];
Print["FirstIntegrals: ",fIAlg];
(* May be useful to add, but need to handle rational functions *)
(*Print[FirstIntegrals`FindLinSysIntegrals[{vf,vars,True}]];*)
(* This is also useful but the generation needs to be done more carefully by already
	determining the Darboux polynomials that are useable as divisors *)
(*Print[FirstIntegrals`FindRationalFirstIntegrals[{vf,vars,True},2]];*)
(* Carbonell & Tiwari
	In principle, the solutions found here should include fIs
	TODO: run this only for low degree and linear definitions with timeout *)
initConj=MapThread[#1==#2&,{vars,init}]/.{List->And};
linalg=TimeConstrained[
	LinearAlgebraicInvariants`LinAlgInv[{initConj,{vf,vars,True},True}],10,{}];
Print["LinAlgInv: ",linalg];

Return[Join[fIAlg,linalg]//DeleteDuplicates];
]]


FindDBXs[systems_List, opts:OptionsPattern[]]:=Catch[Module[
{vf,vars,init,DEFAULTDEG,subst,polys,polysinst},
{vf,vars,init}=systems;
DEFAULTDEG=3;
subst=MapThread[#1->#2&,{vars,init}];
polys = DarbouxDDC`DarbouxPolynomialsM[{vf,vars,True},5,DEFAULTDEG];
polysinst=Map[#/.subst&,polys];
Print[polys];
Print[polysinst];
(* check which side of the polynomial the initial conditions are on? *)
(*
fIs=Primitives`FuncIndep[FirstIntegrals`FindFirstIntegrals[{vf,vars,True},DEFAULTDEG],vars];
fIinst=Map[#/.subst&,fIs];*)
]]


End[]
EndPackage[]
