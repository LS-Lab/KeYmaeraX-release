(* ::Package:: *)

Needs["NDConvexHull`",FileNameJoin[{Directory[],"NDConvexHull.wl"}]]


BeginPackage["sossolve`"];


FindWitness::"FindWitness[polys,vars]
Given a list of polynomials p1,...,pk over variables vars attempts to prove that they do not have a common zero";


Begin["Private`"];


allMonomials[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,0,m}]]


mapSymmetric[n_, f_] := Block[{f1, f2},
	f1 = LowerTriangularize[#, -1] + Transpose@LowerTriangularize[#] &@ ConstantArray[Range@#, #] &;
	f2 = {#, Reverse[(Length@# + 1) - #, {1, 2}]} &;
	f @@ f2@f1@n
]


LinIndepRows[m_]:=Block[{pos,rank},
	pos=Flatten[Position[#,Except[0,_?NumericQ],1,1]&/@RowReduce@Transpose@m];
	{pos,m[[pos]]}
]


LDLT[mat_?SymmetricMatrixQ] := 
     Module[{n = Length[mat], mt = mat, v, w},
            Do[
               If[j > 1,
                  w = mt[[j, ;; j - 1]]; v = w Take[Diagonal[mt], j - 1];
                  mt[[j, j]] -= w.v;
                  If[j < n,
                     mt[[j + 1 ;;, j]] -= mt[[j + 1 ;;, ;; j - 1]].v]];
               If[mt[[j,j]]!=0,mt[[j + 1 ;;, j]] /= mt[[j, j]]],
               {j, n}];
            {LowerTriangularize[mt, -1] + IdentityMatrix[n], Diagonal[mt]}]


(* Deletes monomials that cannot possibly in the basis *)
ReduceBasis[monbasis_List, gcoeff_List, gb_List, vars_List, filter_, monOrder_]:= Module[{
	mb,kp,R,coeffs,filpos,umonomials,i,lgb,tt,gmons,gc},
	
	mb = monbasis;
	gc = Map[#[[1]]&,gcoeff];
	
	{tt,kp} = Timing[KroneckerProduct[mb,mb]];
	Print["Kronecker time: ",tt];	
	
	(* The reduced outer product matrix of the basis *)
	{tt,R} = Timing[
		Table[PolynomialReduce[kp[[i, j]],gb,vars,MonomialOrder->monOrder][[2]],
		{i, Length[mb]}, {j, Length[mb]}]
	];
	Print["Reduction time: ",tt];

	{tt,coeffs} = Timing[
		Table[CoefficientRules[R[[i, j]],vars,monOrder],
		{i, Length[mb]}, {j, Length[mb]}]
	];
	Print["Coeffs time: ",tt];
	
	(* Filtering monomials *)
	While[True,
	(* The unique monomials appearing anywhere on the diagonal *)
	umonomials = Map[#[[1]]&, Flatten[Diagonal[coeffs]]]//DeleteDuplicates;
	
	(* Positions to be filtered *)
	filpos={};
	For[i=1,i <= Length[umonomials],i++,
	Block[{lk,umon, mon,coeff,constr},
		umon = umonomials[[i]];
		If[MemberQ[gc,umon], Continue[]]; (* The RHS is non-zero *)
		mon = FromCoefficientRules[{umon->1},vars];
		lk=Flatten[Map[Lookup[#,{umon},0]&,coeffs,{2}],{3}][[1]];
		If[DiagonalMatrixQ[lk],
		Block[{pos},
			pos=Position[Diagonal[lk],_?(#!=0&)];
			If[Length[pos]==1, filpos=Join[filpos,pos[[1]]]; ]
		];
		]
	]
	];
	filpos=filpos // DeleteDuplicates;
	If[Not[filter] || Length[filpos]==0,Break[]];
	Print["Filtering monomials: ",mb[[filpos]]];
	mb=Delete[mb,List/@filpos];
	
	R=Delete[R,List/@filpos];
	R=Map[Delete[#,List/@filpos]&,R];
	coeffs=Delete[coeffs,List/@filpos];
	coeffs=Map[Delete[#,List/@filpos]&,coeffs];
	];
	Return[{mb,R,coeffs}]
]


(* Reduce monomials to a linearly independent set (post-reduction) *)
ReduceLin[prem_,gb_,vars_,monOrder_]:=Module[{red,linred,mons,lin,pos,mat,postmons},
	red = Map[
		PolynomialReduce[#,gb,vars,MonomialOrder -> monOrder][[2]]&,
		prem];
	linred=Map[CoefficientRules[#,vars,monOrder]&,red];
	mons =Map[#[[1]]&,Flatten[linred,1]]//DeleteDuplicates;
	lin=Map[Lookup[#,mons,0]&,linred];
	{pos,mat}=LinIndepRows[lin];
	postmons=prem[[pos]];
	postmons	
];


(* Round result
	res - the result to round
	monbasis, gtrm, gb, vars - book keeping needed for the rounding 
	skipround - whether to round the result at all *)
RoundResult[res_,monbasis_,gtrm_,gb_,vars_,skipround_,monOrder_]:= Module[{
	matrix, L, vals, sos, fin, power, seq, rem, maxiters,i,denom,powdenom},
	maxiters=50;
	powdenom=32;
	denom=1;
	(* use 1/1, 1/2, ..., 1/powdenom, then double the denominator until maxiters *)
	For[i=1, i <= maxiters, i++,
	power=1/denom;
	If[i < powdenom, denom=denom+1, denom=2*denom];
	(* Force matrix to be symmetric then rationalize *)
	matrix=res;
	If[Not[skipround],
		matrix=1/2*(matrix+Transpose[matrix]);
		matrix=Rationalize[Round[matrix,power]]];
	
	{L,vals}=LDLT[matrix]; (* Compute an LDLT such that L.DiagionalMatrix[vals].Transpose[L] = matrix *)

	(* Heuristic: just clip all vals that are < 0 to 0
	vals = Map[Clip[#,{0,Infinity}]&,vals]; *)
	If[Not[AllTrue[vals, # >= 0&]],
		If[skipround,Return[{}], Continue[]]
	];

	(* The polynomials in the SOS are given by this *)
	sos = Dot[Transpose[L],monbasis];
	(* This is the thing that must reduce to zero *)
	fin = gtrm+Dot[vals,Map[#^2&,sos]];
	{seq,rem} = PolynomialReduce[fin,gb,vars,MonomialOrder->monOrder];
	(* Print["Rounding: ",power," SOS: ",fin," Remainder: ",rem]; *)
	If[rem===0,Return[{vals,sos,seq}]];
	If[skipround,Return[{}]]
	];
	Return[{}];
]


(* Find monomials that can be eliminated *)
Pvars[polys_,vars_,monOrder_]:= Module[{
	newvars,linred,mons,i,row,nz,z,coeffs,
	newmons,mon,newvar,replacement,flg,j,int,repr,rep},
	linred=Map[CoefficientRules[#,vars,monOrder]&,polys];
	mons=Map[#[[1]]&,Flatten[linred,1]]//DeleteDuplicates;
	newvars=vars;
	newmons=mons;
	replacement={};
	
	For[i=1,i <= Length[newmons],i++,
		row=newmons[[i]];
		nz=Position[newmons[[i]],_?Positive]//Flatten;
		z=Position[newmons[[i]],_?(#===0&)]//Flatten;
		(* Special case where elimination doesn't save anything *)
		If[Length[nz]===1 && row[[nz]][[1]]<=2,Continue[]];

		flg=True;
		(* Every row r_j can be written as z*r_i + c,
		 where c does not share entries with r_i *)
		coeffs={};
		For[j=1, j <= Length[newmons], j++,
			(* Integer part *)
			int=newmons[[j]][[nz]]/row[[nz]]//DeleteDuplicates;
			If[Length[int]===1 && IntegerQ[int[[1]]],
				coeffs=Join[coeffs, int],
				flg=False];
		];
		If[flg,
		mon=FromCoefficientRules[{row->1},newvars];		
		newvar=Unique["FV"];
		If[AllTrue[row,EvenQ[#]&],
			newmons=MapThread[Prepend,{newmons[[All,z]],2*coeffs}];
			repr=newvar->FromCoefficientRules[{row/2->1},newvars],
			newmons=MapThread[Prepend,{newmons[[All,z]],coeffs}];
			repr=newvar->mon
		];
		Print["Eliminating Monomial: ",mon," with: ",repr];
		replacement=Join[{repr},replacement];
		newvars=Join[{newvar},newvars[[z]]];
		Print["mons: ",newmons//MatrixForm];
		]
	];
	rep=MapThread[#1->#2&,{mons,newmons}];
	{FromCoefficientRules[linred/.rep,newvars],newvars,replacement}
];


FlattenSymmetric[mat_,k_]:=Module[{mm,i,j,c},
	mm={};
	For[i=1,i<=k,i++,
	For[j=i,j<=k,j++,
		c=If[i==j,mat[[i,j]],2*mat[[i,j]]];
		mm=Append[mm,c]
	]];
	Return[mm];
]


fastRF[a_List, b_List] :=
  Module[{c, o, x},
    c = Join[b, a];
    o = Ordering[c];
    x = 1 - 2 UnitStep[-1 - Length[b] + o];
    x = FoldList[Max[#, 0] + #2 &, x];
    x[[o]] = x;
    Pick[c, x, -1]
  ]


(* Eliminate
linear constraints x-t =0 (x does not appear in t) or
almost-linear ones x^2-SOS=0 (x does not appear in SOS)
*)
ElimLinear[polys_, vars_, monOrder_] := Module[{
	curpolys, i, j, lc, rhs, delvars, curineq, coeff,
	mlist, lininst},
	curpolys = polys;
	(* curineq=ineq; *)
	delvars = {};
	lininst = {};
	For[i = 1, i <= Length[vars], i++,
	For[j = 1, j <= Length[curpolys], j++, 
	coeff=CoefficientRules[curpolys[[j]],{vars[[i]]},monOrder]; 
	If[Length[coeff] > 2, Continue[]];
	(* Linear constraint *)
	lc = Lookup[coeff, {{1}}];
	If[NumericQ[lc[[1]]],
	rhs = If[Length[coeff] == 0, 0, Lookup[coeff, {{0}}]];
	If[Head[rhs[[1]]] === Missing, Continue[]];
	Print["Eliminating Var: ", vars[[i]], " RHS: ", -rhs[[1]]/lc[[1]]];
	curpolys = Delete[curpolys, j];
	curpolys = curpolys /. {vars[[i]] -> -rhs[[1]]/lc[[1]]};
	(* curineq=curineq/.{vars[[i]]\[Rule] -rhs[[1]]/ lc[[1]]}; *)
	delvars = Join[{vars[[i]]}, delvars];
	lininst = Join[lininst,{{j,vars[[i]],-rhs[[1]]/lc[[1]],lc[[1]]}}];
	Break[]
	]
	(* Disabled: SOS constraint
	lc = Lookup[coeff, {{2}}];
	If[NumericQ[lc[[1]]],
		rhs = If[Length[coeff] == 0, 0, Lookup[coeff, {{0}}]];
		If[Head[rhs[[1]]] === Missing, Continue[]];
		mlist = CoefficientRules[-rhs[[1]]/lc[[1]], vars, monOrder];
		If[(* RHS is an SOS *)
		AllTrue[Map[#[[2]] &, mlist], NonNegative[#] &] &&
		AllTrue[Map[#[[1]] &, mlist] // Flatten // DeleteDuplicates, EvenQ] &&
		(* TODO: var appears in even powers everywhere in curpolys *)
		False, Print["Eliminating Squared Var: ", vars[[i]]^2," RHS: ", -rhs[[1]]/lc[[1]]];
		curpolys = Delete[curpolys, j];
		curpolys = curpolys /. {vars[[i]] -> Sqrt[-rhs[[1]]/lc[[1]]]};
		(* curineq=curineq/.{vars[[i]]\[Rule] -rhs[[1]]/lc[[1]]}; *)
		delvars = Join[{vars[[i]]}, delvars];
		Break[]]] *)
	]];
	{curpolys,(* curineq,*)fastRF[vars, delvars],lininst}
	];


FlattenSymmetric[mat_,k_]:=Module[{mm,i,j,c},
	mm={};
	For[i=1,i<=k,i++,
	For[j=i,j<=k,j++,
		c=If[i==j,mat[[i,j]],2*mat[[i,j]]];
		mm=Append[mm,c]
	]];
	Return[mm];
]
ExpandSymmetric[ls_,k_]:=Module[{mm,ctr,i,j,},
	mm=ConstantArray[0,{k,k}];
	ctr=1;
	For[i=1,i<=k,i++,
	For[j=i,j<=k,j++,
		If[i==j,
			mm[[i,j]]=ls[[ctr]],
			mm[[i,j]]=ls[[ctr]];
			mm[[j,i]]=ls[[ctr]]];
		ctr=ctr+1;
	]];
	Return[mm];
]
(* Convert to primal form *)
ConvertPrimalRaw[constraints_,cs_,k_]:=Module[{prim,ns,sol},
	prim = Map[FlattenSymmetric[#,k]&,constraints];
	ns = NullSpace[prim];
	(* Exact orthogonalization is too slow:
		ns = Orthogonalize[ns]; *)
	sol = LinearSolve[prim,cs];
	If[Head[sol]===LinearSolve || Length[sol]==0 || Length[ns]===0, Return[{}]];
	Return[{ns,sol}]
]

MonomialQ[a_,L_List] :=
PolynomialQ[a, L] &&               (* must be Polynomial and *)
  Head[Expand[a, x_ /; MemberQ[L, x]]] =!= Plus;


(* Given:
	gb - groeber basis
	vars - variables
	gcoeff - coefficient rule representaiton of g
	mons - monomials
	1) Minimizes the list of monomials
	2) Solves the resulting constraints for g + SOS \in ideal generated by gb
Others:
	filter - whether to do step 1) filtering
	primal - whether to solve in primal or dual form
	monOrder - monomial ordering
Return:
	{} - no solution
	{sdm,monbasis,constraints,cs} - dual solution, sdm is a PSD matrix,
		monbasis is the final list of monomials used, where the generated constraints are such that constraints \[Equal] cs
	{bs,ns,ys,monbasis,constraints,cs} - primal olution bs + ys.ns is a PSD matrix solving the constraints
*)
MonSolve[gb_List,vars_List,gcoeff_List, mons_List, filter_, primal_, monOrder_]:=Module[{
	redseq,redg,
	prem, monbasis, R, coeffs, umonomials,
	constraints, cs, k, tt, res, i},
		
	prem = mons;	
	Print["No. input monomials: ",Length[prem]];
	
	(* No monomials left *)
	If[Length[prem]===0, Return[{}]];
	
	(* Further simplify the basis and precompute data *)
	{monbasis, R, coeffs} = ReduceBasis[prem,gcoeff,gb,vars,filter, monOrder];

	umonomials = Flatten[Map[#[[1]]&,coeffs,{3}],2]//DeleteDuplicates;
	If[Not[SubsetQ[umonomials,Map[#[[1]]&,gcoeff]]],
		Print["Skipped solving because of unsatisfiable constraint."];
		Return[{}]
	];
	
	Print["Solving for constraints "];
	(* Compute the constraints *)
	constraints={};
	cs={};
	(* For each unique monomial, we add a constraint *)
	For[i=1,i <= Length[umonomials],i++,
	Block[{lk,mon,umon,coeff,constr},
		umon = umonomials[[i]];
		mon = FromCoefficientRules[{umon->1},vars];
		lk=Flatten[Map[Lookup[#,{umon},0]&,coeffs,{2}],{3}][[1]];
		coeff=-Lookup[gcoeff,{umon},0][[1]];
		constraints=Append[constraints,lk];
		cs=Append[cs,coeff];
	]
	];
	
	If[Length[constraints]===0, Return[{}]];
	
	(* Finally solve the SDP *)
	k=Length[monbasis];
	Print["Total constraints: ",Length[constraints]];
	Print["Dimension: ",Length[monbasis]];
	
	(* Solving in primal *)
	If[primal,
		Block[{ns,bs},
		Print["Solving in primal form"];
		{tt,nsbs} = Timing[ConvertPrimalRaw[constraints,cs,k]];
		Print["Converted to primal time: ",tt];
		If[Length[nsbs]===0, Print["Conversion to primal failed."];Return[{}]];
		{nss,bss}=nsbs;
		
		bs = ExpandSymmetric[bss,k];
		ns = Map[ExpandSymmetric[#,k]&,nss];
		If[Length[ns]===0, Return[{}]];
	
		{tt,res}=Timing[
			SemidefiniteOptimization[ConstantArray[0,Length[ns]],
			Join[{bs},ns],
			{"DualityGap","PrimalMinimizer"}]
		];
		Print["SDP time: ",tt];
		Print["Duality gap: ",res[[1]]];
		If[MemberQ[res[[2]],Indeterminate],
			Print["No solution"];
			Return[{}]];

		vals= res[[2]];
		Print["Primal solution: ",vals];
		(*
		For[ctr=1,ctr <= 19,ctr++,
		Print["Refining solution space"];
		Print["Before: ",Length[nss]];
		as=Round[10^20 vals];
		mat=Join[IdentityMatrix[Length[vals]],{-as}]//Transpose;
		lattice=LatticeReduce[mat];
		rr=Transpose[Drop[Transpose[lattice],-1]][[1;;1]];
		nss=NullSpace[rr].nss;
		Print["After: ",Length[nss]];
		
		bs = ExpandSymmetric[bss,k];
		ns = Map[ExpandSymmetric[#,k]&,nss];
		If[Length[ns]===0, Return[{}]];
	
		{tt,res}=Timing[
			SemidefiniteOptimization[ConstantArray[0,Length[ns]],
			Join[{bs},ns],
			{"DualityGap","PrimalMinimizer"}]
		];
		Print["SDP time: ",tt];
		Print["Duality gap: ",res[[1]]];
		If[MemberQ[res[[2]],Indeterminate],
			Print["No solution"];
			Return[{}]];
		vals= res[[2]];
		Print["Primal solution: ",vals];
		]; *)
		
		Return[{bs,ns,res[[2]],monbasis,constraints,cs}];
		]
	];

	(* Solving in dual form *)
	Print["Solving in dual form"];
	cos=DiagonalMatrix[Map[If[MonomialQ[#,vars],1,0.01]&,monbasis]];
	
	{tt,res}=Timing[
		SemidefiniteOptimization[cs,
		Join[{cos},constraints],
		{"DualityGap","DualMaximizer"},
		Method->"DSDP"]
	];

	Print["SDP time: ",tt];
	Print["Duality gap: ",res[[1]]];
	If[MemberQ[res[[2]],Indeterminate,{2}],
		Print["No solution"];
		Return[{}]];

	Print["Eigenvalues: ",Eigenvalues[res[[2]]]];
	Return[{res[[2]],monbasis,constraints,cs}];
]


(* Directly solve the SOS problem in primal form *)
DirectSolve[poly_,vars_List, mb_List, monOrder_]:=Module[{
	redseq,redg,
	prem, monbasis, R, coeffs, umonomials,
	constraints, cs, k, tt, res, i},
	Print["Directly solving: SOS = ",poly," vars: ",vars];
	Print["Monomials: ",mb];
	
	R= KroneckerProduct[mb,mb];
	coeffs = Table[CoefficientRules[R[[i, j]],vars,monOrder],
		{i, Length[mb]}, {j, Length[mb]}];

	umonomials = Flatten[Map[#[[1]]&,coeffs,{3}],2]//DeleteDuplicates;
	
	gcoeff=CoefficientRules[poly,vars,monOrder];
	
	Print["Solving for constraints "];
	(* Compute the constraints *)
	constraints={};
	cs={};
	(* For each unique monomial, we add a constraint *)
	For[i=1,i <= Length[umonomials],i++,
	Block[{lk,mon,umon,coeff,constr},
		umon = umonomials[[i]];
		mon = FromCoefficientRules[{umon->1},vars];
		lk=Flatten[Map[Lookup[#,{umon},0]&,coeffs,{2}],{3}][[1]];
		coeff=Lookup[gcoeff,{umon},0][[1]];
		constraints=Append[constraints,lk];
		cs=Append[cs,coeff];
	]
	];
	If[Length[constraints]===0, Return[{}]];
	
	(* Finally solve the SDP *)
	k=Length[mb];
	Print["Total constraints: ",Length[constraints]];
	Print["Dimension: ",Length[mb]];
	
	primal=False;
	(* Solving in primal *)
	If[primal,
		Block[{ns,bs},
		Print["Solving in primal form"];
		{tt,nsbs} = Timing[ConvertPrimalRaw[constraints,cs,k]];
		Print["Converted to primal time: ",tt];
		If[Length[nsbs]===0, Print["Conversion to primal failed."];Return[{}]];
		{ns,bs}=nsbs;
		bs = ExpandSymmetric[bs,k];
		ns = Map[ExpandSymmetric[#,k]&,ns];
		If[Length[ns]===0, Print[bs];Return[{}]];
	
		{tt,res}=Timing[
			SemidefiniteOptimization[ConstantArray[0,Length[ns]],
			Join[{bs},ns],
			{"DualityGap","PrimalMinimizer"}]
		];
		Print["SDP time: ",tt];
		Print["Duality gap: ",res[[1]]];
		If[MemberQ[res[[2]],Indeterminate],
			Print["No solution"];
			Return[{}]];
		Print["Primal solution: ", res[[2]]];
		Return[{bs,ns,res[[2]],monbasis,constraints,cs}];
		]
	];

	(* Solving in dual form *)
	Print["Solving in dual form"];
	cos=DiagonalMatrix[Map[If[MonomialQ[#,vars],1,0.01]&,mb]];
	Print[cos];
	
	{tt,res}=Timing[
		SemidefiniteOptimization[cs,
		Join[{cos},constraints],
		{"DualityGap","DualMaximizer"},
		Method->"DSDP"]
	];

	Print["SDP time: ",tt];
	Print["Duality gap: ",res[[1]]];
	If[MemberQ[res[[2]],Indeterminate,{2}],
		Print["No solution"];
		Return[{}]];

	Print["Eigenvalues: ",Eigenvalues[res[[2]]]];
	Print[Normal[res[[2]]]//MatrixForm];
	Return[{res[[2]],mb,constraints,cs}];
];


SolveNorm[f_,test_]:=Block[{eqs,norm,c},
	eqs=Map[#-f[[1]]&,Drop[f,1]];
	norm=NullSpace[eqs][[1]];
	c=norm.f[[1]];
	{norm,c,Sign[norm.test-c]}
]
(* Turns a convex hull (facets as produced by NDConvexHull
	into its constraint representation. The convex hull must be full dimensional
*)
ConstraintRep[msco_]:=Block[{pts,facets,chullpts,mid,facetsraw,hyps,dim},
	Print["No. input points: ",Length[msco]];
	If[Length[msco]==0,Return[{}]];
	dim=Length[msco[[1]]];
	If[dim===0, Return[{}]];
	Print["dimension ",dim];
	If[dim==1,
		min=Min[msco];
		max=Max[msco];
		hyps={{{1},min,1},{{1},max,-1}};
		Return[hyps]
	];
	If[dim>2,
		{pts,facets}=NDConvexHull`CHNQuickHull[msco],
		pts=NDConvexHull`CH2QuickHull[msco];
		facets=Transpose[{pts,RotateLeft[pts,1]}]
	];
	Print["Converting hull with ",Length[facets]," facets in dimension ",dim
		," to constraint representation."];
	chullpts=msco[[pts]];
	mid=Mean[chullpts];
	facetsraw=Map[msco[[#]]&,facets];
	hyps=Map[SolveNorm[#,mid]&,facetsraw]//DeleteDuplicates;
	hyps=Select[hyps,#[[3]]!=0&];
	If[Length[hyps]===0,
		Block[{},
		Print["WARNING: convex hull may not be full dimensional."];
		(* Arbitrarily extend points in all directions *)
		ff=Function[{a},Map[#+a&,IdentityMatrix[dim]]];
		msco2=Flatten[Map[ff,msco],1]//DeleteDuplicates;
		Return[ConstraintRep[msco2]]]
	];
	Return[hyps];
];
TestConstraint[pt_,constraints_]:=Block[{},
	AllTrue[Map[#[[3]]*(pt.#[[1]]-#[[2]])>=0&,constraints],TrueQ]
];
(* Test a point against the constraint representation *)
FilterPolytopeConstraint[mons_,vars_,constraints_,monOrder_]:=Module[{
	mm,coeffs,tests,pos},
	(* Print[Map[2*CoefficientRules[#,vars,monOrder][[1]][[1]]&,mons]]; *)
	coeffs=Map[2*CoefficientRules[#,vars,monOrder][[1]][[1]]&,mons];
	tests=Map[TestConstraint[#,constraints]&,coeffs];
	pos=Position[tests,True]//Flatten;
	Return[mons[[pos]]]
];
ShiftHyp[{norm_,c_,sgn_},dirs_]:=Block[{shifts,m},
	shifts=Map[sgn*(norm.#)&,dirs];
	m=Min[Join[{0},shifts]];
	{norm,c+sgn*m,sgn}
];
ExtendConstraints[constraints_,dirs_]:=Block[{},
	Map[ShiftHyp[#,dirs]&,constraints]
];


TruncateEigen[mat_]:=Block[{vals,vecs,pos},
	(* Truncate small eigenvalues *)
	{vals,vecs}=Eigensystem[mat];
	pos=Position[vals,_?(# > 0.1&)]//Flatten;
	vals=vals[[pos]];
	vecs=Orthogonalize[vecs[[pos]]];
	Transpose[vecs].DiagonalMatrix[vals].vecs
]


monomialList[poly_,vars_,monOrder_]:=Block[{},
Times @@ (vars ^#) & /@ CoefficientRules[poly,vars,monOrder][[All,1]]
]
Ptwise[a_,b_]:=Block[{}, Map[#*b &,a]//Flatten]
ListHalf[ls_]:=Tuples[Map[If[EvenQ[#],{#/2},{Floor[#/2],Ceiling[#/2]}]&,ls]];


(* Input:
polys {p_1,p_2,...} - polynomials assumed to be = 0
ineqs {g_1,g_2,...} - polynomials assumed to be \[NotEqual] 0
varsPre  {v_1,v_2,...} - variables (order is important)
degBound - degree bound on monomials
monOrder - monomial order (default DegreeReverseLexicographic)
monomials - optional argument that uses that fixed list of monomials (overrides degBound)
*)
FindWitness[polysPre_List, ineqs_List,
	varsPre_List, degBound_Integer,
	monOrder_ : DegreeReverseLexicographic,
	monomials_List : {}
]:= Module [{
	maxcofdeg, hullbound, failure,
	polys,vars,lininst,
	gtrm1, gtrm,trivseq, trivg, replacement,
	gb, conv, redseq, redg, gcoeff, vstemp, ivars,
	ms, msco, hull, polytope, vv, fvv, polydeg, deg, prem,
	done, prevdeg, rm,
	res,monbasis,constraints,cs, rres,
	soscoeff, sos, seq, pos,
	trunclim, primaltrunclim,
	pts,facets,hullconstraints,primalmonbound,tt
	},
	
	(* The return is a 5-element list:
	{g, soscoeff, sos, lininst}
	Where:
		g + \sum_i soscoeff_i . sos_i reduces to 0 under the given polys i.e.,
		g + \sum_i soscoeff_i . sos_i =
		\sum_i polys_i conv_i
		
	lininst is a list of eliminated linear equations in polys of the form:
	{pos, lhs, rhs, cofc} where pos is the list position in polys that got removed,
	lhs=rhs is the linear equation (typically lhs is a single variable)
	cofc is a factor so that polys[[pos]] can be rewritten to the form cofc*(lhs-rhs).
	*)	
	(* result type encoding of failure*)
	failure = {0,{},{},{},{}};

	(* Some of these can be made parameters, but these defaults should be more or less representative *)
	maxcofdeg=15; (* Max degree of cofactors *)
	hullbound=2000; (*stops using convex hull if (number of points * dimension^2) is above this number *)	
	
	trunclim=15; (* Controls rounding truncation when attempting to round solution 10^-0, 10^-1, ..., 10^-trunclim*) 
	primaltrunclim=15; (* Same as above but used for the final primal truncation *)
	primalmonbound=80;
	
	diagthresh = 10^-6;
	
	(* Eliminate linear equations *)
	{polys,vars,lininst}=If[ineqs==={},
		ElimLinear[polysPre,varsPre,monOrder],
		{polysPre,varsPre,{}}
	];	(* NOTE: vars is kept in same order as input (deletions in place) *)	
	
	(* Eliminate some monomialsc *)
	{polys,vars,replacement}=If[ineqs==={},
		Pvars[polys,vars,monOrder],
		{polys,vars,{}}
	];	(* NOTE: vars is kept in same order as input *)	
	
	Print["Polynomials assumed to be zero: ",polys];
	Print["Polynomials assumed to be non-zero: ",ineqs];

	(* gtrm is a term known to be strictly positive i.e., we will attempt to find gtrm+sos = 0 *)
	gtrm1 = (Apply[Times,ineqs]);
	gtrm = gtrm1^2; (* Typically gtrm = 1 if ineqs = {} *)

	(* Trivial: polys already trivially reduces gtrm to 0 *)
	If[Not[MemberQ[polys,0]], (* NOTE: there's a weird bug with PolynomialReduce when polys has a 0 in it *)
		{trivseq,trivg} = PolynomialReduce[gtrm, polys, vars, MonomialOrder -> monOrder];
		If[trivg===0,
			Return[{gtrm, {}, {}, trivseq, lininst}/.replacement]]];
	
	(* Solve for the Groebner basis and its conversion matrix *)
	{gb, conv} = GroebnerBasis`BasisAndConversionMatrix[polys, vars, MonomialOrder -> monOrder];
	Print["Groebner basis: ",gb];
	
	(*ls = Map[monomialList[#,vars,monOrder]&,gb]//Flatten//DeleteDuplicates;*)
	mpolys = Map[monomialList[#,vars,monOrder]&,polys]; 
	mconv = Map[monomialList[#,vars,monOrder]&,conv,{2}]; 
	ls={};
	For[i=1,i<=Length[mconv],i++,
		ls=Join[ls,MapThread[Ptwise,{mconv[[i]],mpolys}]//Flatten];
	];
	
	(* Trivial: Groebner basis already trivially reduces gtrm to 0 *)
	{redseq,redg} = PolynomialReduce[gtrm,gb,vars,MonomialOrder -> monOrder];
	If[redg===0,
		Print["Polynomial ",gtrm, " trivially reduced to 0."];
		Return[{gtrm,{},{},Dot[redseq,conv],lininst}/.replacement]];

	Print["Using g: ", gtrm, " reduced to: ",redg];
	vstemp=Map[Variables[#]&,Join[{redg},gb]]//Flatten//DeleteDuplicates;
	(* ivars is the same as vars, although the elimination might have got rid of a bunch of variables *)
	ivars=Select[vars,MemberQ[vstemp,#]&];
	gcoeff=CoefficientRules[redg,ivars,monOrder];
	
	Print["Reduced variable set: ",ivars];

	ls=Select[DeleteDuplicates[ls],MonomialQ[#,ivars]&];
	lscoeffs=Flatten[Map[ListHalf,Map[CoefficientRules[#,ivars,monOrder][[1]][[1]]&,ls]],1]//DeleteDuplicates;
	lsmons= Map[FromCoefficientRules[{#->1},ivars]&,lscoeffs];
	
	(* Computing the "approximate" convex hull from the Groebner basis *)
	ms = Map[CoefficientRules[#,ivars,monOrder]&, gb];
	msco = Flatten[Map[#[[1]]&,ms,{2}],1] // DeleteDuplicates;
	If[Length[ivars]^2*Length[msco] > hullbound,
		Print["Switched to bounding box"];
		msco=Join[{ConstantArray[0,Length[ivars]]},DiagonalMatrix[Map[Max,Transpose[msco]]]]
	];
	(* hullconstraints is a list of constraints *)
	hullconstraints = ConstraintRep[msco];
	vv = IdentityMatrix[Length[ivars]];
	
	(* Some book-keeping:
		done tracks the monomial lists that have already been done
		prevdeg *)
	done = {};	
	primaldone={};
	prevdeg=1;

	(* Outer loop: loop over the cofactor degrees *)
	For[polydeg=0, polydeg <= maxcofdeg, polydeg++,
	
	Print["Using polytope from cofactor degree: ",polydeg];
	(*Print[hullconstraints];*)

		(* Inner loop: loop over the monomial degrees *)
		For[deg=0, deg <= degBound, deg++,
		If[deg > 0 && monomials!={},
			Print["Fixed monomials failed"];
			Return[failure]
		];
		
		Print["Degree bound: ",deg];
		
		If[monomials=={},
			(* All monomials up to the degree bound and filtered under the Newton polytope *)
			prem = allMonomials[ivars,deg];
			Print["Initial length: ",Length[prem]];	
			{tt,prem} = Timing[FilterPolytopeConstraint[prem,ivars,hullconstraints,monOrder]];
			Print["After Newton polytope: ",Length[prem], " Time: ",tt];
			Print["Heuristics: ",lsmons//Sort//DeleteDuplicates];
			prem = Join[prem,lsmons]//DeleteDuplicates;
			Print["Monomials (with heuristics): ",Length[prem]];
			{tt,prem} = Timing[Select[prem, PolynomialReduce[#,gb,ivars,MonomialOrder->monOrder][[2]]===#&]];
			Print["Standard monomials (not reduced): ",Length[prem]," Time: ",tt],
			prem = monomials;
			Print["Using fixed monomials: ",Length[prem]]
		];
		(* Filter linearly dependent monomials -- these essentially do not filter anything more *)
		(* {tt,prem}=Timing[ReduceLin[prem, gb, ivars, monOrder]];
		Print["After linear filter: ",Length[prem], " Time: ",tt]; *)
		If[MemberQ[done,prem] || Length[prem]===0,
			Print["Skipping (prev max deg: ",prevdeg,")"];
			If[deg <= prevdeg, Continue[], Break[]]];
		done=Join[{prem},done];
		prevdeg=Max[{prevdeg,deg}];
		
		(* Start by solving in dual form *)
		rm = MonSolve[gb, ivars, gcoeff, prem, True, False, monOrder];
		If[rm==={}, Continue[]];
		
		{res,monbasis,constraints,cs} = rm;
		lthresh=diagthresh;
		(* Refine the result by repeatedly discarding monomials with small diagonal entries until solving fails *)
		While[True,
			diagonal = Diagonal[Normal[res]];
			Print["Threshold: ",lthresh];
			Print["Diagonal: ",diagonal];
			posvals=Position[diagonal,_?(# >= lthresh&)]//Flatten;

			If[Length[posvals] == Length[diagonal],
				lthresh=lthresh*10;
				Continue[];
			];
			rm2 = MonSolve[gb, ivars, gcoeff, monbasis[[posvals]], True, False, monOrder];
			If[rm2==={},
				Break[],
				{res,monbasis,constraints,cs} = rm2]
		];
		(* Experimental
		{vals,vecs}=Eigensystem[Normal[res]];
		pos=Position[vals,_?(# > diagthresh&)]//Flatten;
		vals=vals[[pos]];
		vecs=Rationalize[Map[Chop[#,diagthresh]&,vecs[[pos]]],diagthresh];
		polys= vecs.monbasis;
		newmons = Join[polys,monbasis];
		rm2 = MonSolve[gb, ivars, gcoeff, newmons, True, False, monOrder];
		If[rm2==={},,{res,monbasis,constraints,cs} = rm2]
		
		(* Refine the result by repeatedly discarding monomials with small diagonal entries until solving fails *)
		While[True,
			diagonal = Diagonal[Normal[res]];
			Print["Diagonal: ",diagonal];
			posvals=Position[diagonal,_?(# \[GreaterEqual] diagthresh&)]//Flatten;
			If[Length[posvals] == Length[diagonal], Break[]];
			rm2 = MonSolve[gb, ivars, gcoeff, monbasis[[posvals]], True, False, monOrder];
			If[rm2==={},
				Break[],
				{res,monbasis,constraints,cs} = rm2]
		];*)
		
		Print["Monomials after diagonal filtering: ",Length[monbasis]];	
		Print[monbasis];
		(*Transpose[vecs].DiagonalMatrix[vals].vecs*)
		
		
		(* Attempt to round the result *)
		rres = RoundResult[Normal[res], monbasis, gtrm, gb, ivars, False, monOrder];

		(* Naive rounding failed. Trying harder. *)
		If[Length[rres]==0,
			(* Attempt to resolve by truncating "zeros" *)
			Print["Rounding heuristic failed, attempt resolve."];
			Block[{diag, prev, i, thresh, goodpos, rmloc, monbasisloc, constraintsloc,
				resloc, csloc, bs, ns, ys, j, yss,rr,trybasis,
				vals,vecs,posvals,ppp,ord,ordsub,cur},
			
			(* The set up here is as follows:
				From the initial input set "monbasis",
				Construct a list of (sub-) monomial (or polynomial) bases to try
				For each group, attempt to solve in primal form *)
			trybasis={};
			
			(* Truncation based on numerical SVD *)
			{vals,vecs}=Eigensystem[Normal[res]];
			posvals=Position[vals,_?(# >= diagthresh&)]//Flatten;
			vals=vals[[posvals]];
			ppp=Map[monbasis[[#[[2]]]]&,Position[vecs[[posvals]],_?(# > 10^-6&)]]//DeleteDuplicates;
			trybasis=Join[trybasis,{ppp}];
			(* Truncation based on the diagonal *)
			diag=Normal[Diagonal[res]];
			(*Print["Diagonal: ",diag];*)
			ord=Reverse[Ordering[diag]];
			For[i=1, i <= 10, i++,
				ordsub = Take[ord,Round[i/10*Length[diag]]];
				trybasis=Join[trybasis,{monbasis[[ordsub]]}]];
			trybasis=Map[Sort,trybasis]//DeleteDuplicates;

			trybasis=Select[trybasis,Length[#]<=primalmonbound&];
			(* Don't bother with primal if it will take too long *)
			
			For[i=1,i<=Length[trybasis],i++,
			cur=trybasis[[i]];
			If[MemberQ[primaldone,cur],Continue[]];
			
			primaldone=Join[{cur},primaldone];
			Print["Trying: ",cur];
			rmloc = MonSolve[gb,ivars,gcoeff, cur, True, True, monOrder];
			If[rmloc==={},Continue[]];
			{bs,ns,ys,monbasisloc,constraintsloc,csloc}=rmloc;
			(*
			rrraw = bs+ys.ns;
			(* Refine the result by repeatedly discarding monomials with small diagonal entries until solving fails *)
			While[True,
				diagonal = Diagonal[rrraw];
				Print["Diagonal: ",diagonal];
				posvals=Position[diagonal,_?(# \[GreaterEqual] 10&)]//Flatten;
				If[Length[posvals] == Length[diagonal], Break[]];
				rmloc2 = MonSolve[gb, ivars, gcoeff, monbasisloc[[posvals]], True, True, monOrder];
				If[rmloc2==={},
					Break[],
					{bs,ns,ys,monbasisloc,constraintsloc,csloc}=rmloc2;
					rrraw = bs+ys.ns
				]
			];*)
				
			For[j=1,j <= primaltrunclim,j++,
				yss = Rationalize[Round[Normal[ys],10^-j]];
				rr = bs+yss.ns;
				(*Print[bs//MatrixForm];
				Print[Map[MatrixForm,ns]];
				Print[Length[rr]];
				Print[MatrixRank[rr]];*)
				Print[Diagonal[rr]];
				(*Print["rr: ",rr // MatrixForm];*)
				Print["Eigenvalues: ",N[Eigenvalues[rr]]];
				ppp=1+monbasisloc.(rr).monbasisloc;
				Print[PolynomialReduce[ppp,gb,ivars,MonomialOrder->monOrder]];
				(* {seq,result}=PolynomialReduce[ppp,gb,ivars,MonomialOrder->monOrder];			
				ds=DirectSolve[seq.gb-gtrm,ivars,monbasisloc,monOrder];
				If[ds==={}, Continue[]];
				{res,monbasis,constraints,cs} = ds;
				rres = RoundResult[Normal[res], monbasis, gtrm, gb, ivars, False, monOrder];
				Print["resolve ",rres]; *)
				
				rres = RoundResult[rr,monbasisloc,gtrm,gb,ivars,True, monOrder];
				If[Length[rres]==0, , Break[]];
			];
			If[Length[rres]==0, , Print["Primal Done."];Break[]];
			];
			];
		];
		If[Length[rres]==0, Continue[]];
		(* Return successfully afer cleaning it up somewhat *)
		{soscoeff,sos,seq} = rres;
		pos=Position[soscoeff, x_ /; ! TrueQ[x == 0], {1}, Heads -> False]//Flatten;
		Print["seq: ",seq];
		Return[{
			gtrm,
			soscoeff[[pos]],
			sos[[pos]],
			Dot[seq,conv],
			lininst}/.replacement]
		(* Exit inner loop *)
		];

	(* Extend the convex hull *)
	hullconstraints=ExtendConstraints[hullconstraints,vv]
	];
	(* Exit outer loop *)
	Return[failure];
];
FindWitness[polys_List, vars_List, deg_Integer]:= FindWitness[polys, {}, vars, deg]; 


End[];


EndPackage[]
