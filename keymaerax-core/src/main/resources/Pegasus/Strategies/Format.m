(* ::Package:: *)

(* Defines the output format used for various strategies *)


BeginPackage[ "Format`"];


(* Precomputes some ODE-specific information *)
FormatDiffSat::usage="FormatDiffSat[inv,cuts,timings,proved]
	Formats the result in diff sat result into the right format.
	inv = the generated invariant,
	cuts = list of cuts building that invariant,
	timings = list of time measurements for executing parts of this strategy,
	proved = whether this invariant proves the given problem.";
FormatErr::usage="FormatErr[str, internal]
	Reports an error. internal is a flag indicating whether this is an unexpected internal error.";
FormatDDC::usage="FormatDDC[p,branches]
	Formats the DDC result in the right format.
	p = dbx polynomial to split on,
	branches = the 3 branches resulting from splitting on p.";
FormatTriv::usage="FormatTriv[index]
	Returns the corresponding (indexed) reason for concluding that the problem is trivial.";



Begin["`Private`"];


FormatDiffSat[inv_, cuts_List, timings_List, proved_]:=Module[{formatcuts},
If[Not[AllTrue[cuts,Length[#]==2&]],
	Return[FormatErr["Incorrect cuts format to FormatDiffSat (expect 2 entries per element of list)", True]]];
formatcuts = Map[ {#[[1]], Symbol["Hint"] -> #[[2]]} & ,cuts];
{
	Symbol["ResultType"] -> Symbol["DiffSat"],
	Symbol["Result"] -> {
		Symbol["Invariant"] -> inv,
		Symbol["Cuts"] -> formatcuts,
		Symbol["Proved"] -> proved
	},
	Symbol["Meta"] -> {
		Symbol["Timing"] -> timings
	}
}
];


FormatErr[str_String,internal_]:=Module[{},
{
	Symbol["ResultType"] -> Symbol["Error"],
	Symbol["Result"] -> {
		Symbol["ErrorString"] -> str,
		Symbol["InternalError"] -> internal
	}
}
];


FormatDDC[p_, branches_List]:=Module[{},
	If[Length[branches]!=3,
		Return[FormatErr["Wrong number of branches to FormatDDC (expected exactly 3)", True]]];
	
{
	Symbol["ResultType"] -> Symbol["DiffDC"],
	Symbol["Result"] -> {
		Symbol["Poly"] -> p,
		(* p < 0 *)
		Symbol["Less"] -> branches[[1]],
		(* p = 0 *)
		Symbol["Equal"] -> branches[[2]],
		(* p > 0 *)
		Symbol["Greater"] -> branches[[3]]
	}
}];


FormatTriv[reason_Integer]:=Module[{ilist},
(* The master list of reasons *)
ilist={
	Symbol["PreInv"], (* 1: precondition already invariant *)
	Symbol["PostInv"], (* 2: postcondition already invariant *)
	Symbol["PreDomFalse"], (* 3: precondition & domain implies False (subsubmed in 1, but can be more specific where possible) *)
	Symbol["DomImpPost"]   (* 4: domain implies postcondition immediately *)
	Symbol["PreNoImpPost"] (* 5: precondition does not imply postcondition, so problem is trivially false *)
};
If[Length[ilist]<reason || reason <=0,
	Return[FormatErr["Incorrect index to FormatTriv (expected 1 <= reason <= " <> ToString[Length[ilist]], True]]];
{
	Symbol["ResultType"] -> Symbol["Trivial"],
	Symbol["Result"] -> ilist[[reason]]
}];


End[]
EndPackage[];
