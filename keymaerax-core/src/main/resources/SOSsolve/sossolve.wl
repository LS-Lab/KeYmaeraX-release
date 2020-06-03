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
	Return[{ns,sol}]
]


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
	
	(* Filter linearly dependent monomials *)
	prem=ReduceLin[prem, gb, vars, monOrder];
	Print["After linear filter: ",Length[prem]];
	
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
		{ns,bs} = ConvertPrimalRaw[constraints,cs,k];
		bs = ExpandSymmetric[bs,k];
		ns = Map[ExpandSymmetric[#,k]&,ns];
		If[Length[ns]===0,Return[{}]];
	
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
	{tt,res}=Timing[
		SemidefiniteOptimization[cs,
		Join[{IdentityMatrix[k]},constraints],
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


(*https://mathematica.stackexchange.com/questions/113492/how-to-generate-higher-dimensional-convex-hull*)
ConvexDependentQ[corners_, cand_] := Module[
   {w, ws},
   w = Array[ws, Length@corners];
   1 == Length@
     FindInstance[
      w.corners == cand && Total[w] == 1 && 
       And @@ Table[w[[i]] >= 0, {i, Length@w}], w]
   ];
 
ConvexReduce[data_] := Module[
   {corners, ncorners, test},
   corners = data;
   Do[
    ncorners = Delete[corners, Position[corners, data[[i]]]];
    test = ConvexDependentQ[ncorners, data[[i]]];
    If[test, corners = ncorners];
    , {i, Length@data}
    ];
   corners
   ];
   
ConvexHullCorners[data_] := Module[
   {corners, rd},
   corners = {};
   Do[
    corners = 
      Join[corners,
       Select[data, 
        Min[data[[;; , i]]] == #[[i]] || 
          Max[data[[;; , i]]] == #[[i]] &]];
    , {i, Length@data[[1]]}
    ];
   corners = DeleteDuplicates@corners;
   rd = Delete[data, First@Position[data, #] & /@ corners];
   Do[
    If[ConvexDependentQ[corners, rd[[i]]], , AppendTo[corners, rd[[i]]]]
    , {i, Length@rd}
    ];
   ConvexReduce@DeleteDuplicates@corners
   ];

FilterPolytope[mons_,vars_,polytope_,monOrder_]:=Module[{mm},
	(* Print[Map[2*CoefficientRules[#,vars,monOrder][[1]][[1]]&,mons]]; *)
	mm=Select[mons,ConvexDependentQ[polytope,2*CoefficientRules[#,vars,monOrder][[1]][[1]]]&];
	Return[mm];
]


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
	trunclim, primaltrunclim
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
	hullbound=500; (* stops using convex hull if (number of points * dimension) is above this number *)	
	
	trunclim=15; (* Controls rounding truncation when attempting to round solution 10^-0, 10^-1, ..., 10^-trunclim*) 
	primaltrunclim=15; (* Same as above but used for the final primal truncation *)
	
	(* Eliminate linear equations *)
	{polys,vars,lininst}=If[ineqs==={},
		ElimLinear[polysPre,varsPre,monOrder],
		{polysPre,varsPre,{}}
	];	(* NOTE: vars is kept in same order as input (deletions in place) *)	
	
	(* Eliminate some monomials *)
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

	(* Computing the "approximate" convex hull from the Groebner basis *)
	ms = Map[CoefficientRules[#,ivars,monOrder]&, gb];
	msco = Flatten[Map[#[[1]]&,ms,{2}],1];
	
	(* Various options *)
	hull=If[Length[ivars] <= 2, ConvexHullCorners, #[[(NDConvexHull`CHNQuickHull[#][[1]])]]&];
	If[Length[msco]>hullbound,
		Print["Too many points and dimensions, switching to bounding box. Num points: ",Length[msco]," Num vars: ",Length[ivars]];
		polytope=Join[{ConstantArray[0,Length[ivars]]},DiagonalMatrix[Max /@ Transpose[msco]]],
		polytope = hull[msco];
	];
	
	(* vv, fvv are used to extend the polytope by increasing degree by 1 TODO: check correctness *)
	vv = Map[CoefficientRules[#,ivars,monOrder][[1]][[1]]&, Join[{1},ivars]];
	fvv=Function[{a},Map[#+a&,vv]];
	
	(* Some book-keeping:
		done tracks the monomial lists that have already been done
		prevdeg *)
	done = {};	
	prevdeg=1;

	(* Outer loop: loop over the cofactor degrees *)
	For[polydeg=0, polydeg <= maxcofdeg, polydeg++,
	Print["Using polytope: ",polytope, " from cofactor degree: ",polydeg];

		(* Inner loop: loop over the monomial degrees *)
		For[deg=1, deg <= degBound, deg++,	
		Print["Degree bound: ",deg];
		
		(* All monomials up to the degree bound and filtered under the Newton polytope *)
		prem = allMonomials[ivars,deg];
		prem = FilterPolytope[prem,ivars,polytope,monOrder]; (* TODO: speed this up!! *)

		If[MemberQ[done,prem] || Length[prem]===0,
			Print["Skipping (prev max deg: ",prevdeg,")"];
			If[deg <= prevdeg, Continue[], Break[]]];
		done=Join[{prem},done];
		prevdeg=Max[{prevdeg,deg}];
		
		(* Start by solving in dual form *)
		rm = MonSolve[gb, ivars, gcoeff, prem, True, False, monOrder];
		If[rm==={}, Continue[]];
		
		{res,monbasis,constraints,cs} = rm;
		(* Attempt to round the result *)
		rres = RoundResult[Normal[res], monbasis, gtrm, gb, ivars, False, monOrder];

		(* Naive rounding failed. Trying harder. *)
		If[Length[rres]==0,
		
			(* Attempt to resolve by truncating "zeros" *)
			Print["Rounding heuristic failed, attempt resolve."];
			Block[{diag, prev, i, thresh, goodpos, rmloc, monbasisloc, constraintsloc,
				resloc, csloc, bs, ns, ys, j, yss,rr},
			
			(* Truncation based on the diagonal *)
			diag=Normal[Diagonal[res]];
			prev={};
			
			For[i=0, i <= trunclim, i++,
			
			If[i < trunclim,
			(* Truncate *)
				thresh=10^-i;
				goodpos=Position[diag,_?(#>thresh&)]//Flatten; (* Filter monomials with coefficients < threshold *)
				If[monbasis[[goodpos]]===prev, Continue[]]; (* Ignore if no new monomials are introduced *)
				Print["Truncating (and re-solve) at: ",thresh];
				prev=monbasis[[goodpos]];
				Print["Keeping monomials: ", prev];
				(* Solve in dual *)
				rmloc = MonSolve[gb,ivars,gcoeff, prev, False, False, monOrder];
				If[rmloc==={},Continue[]];
				{resloc,monbasisloc,constraintsloc,csloc}=rm;
				rres = RoundResult[Normal[resloc],monbasisloc,gtrm,gb,ivars,False, monOrder];
				If[Length[rres]==0,, Print["Dual Done."]; Break[]];
			,
			(* No truncate or (dual) resolve on last iteration *)
				If[monbasis===prev, Continue[]];
				Print["Final iteration, skipping truncation"];
				prev=monbasis;
			];
			(* Resolve in primal again *)			
			rmloc = MonSolve[gb,ivars,gcoeff, prev, False, True, monOrder];
			If[rmloc==={},Continue[]];
			{bs,ns,ys,monbasisloc,constraintsloc,csloc}=rmloc;
			For[j=1,j <= primaltrunclim,j++,
				yss = Rationalize[Round[Normal[ys],10^-j]];
				rr = bs+yss.ns;
				(*
				Print[N[Eigenvalues[rr]]];
				Print[bs // MatrixForm];
				Print[yss];
				Print[Map[MatrixForm,ns]];
				Print[Map[MatrixForm,constraintsloc]];
				Print[csloc];
				ppp=1+monbasisloc.(bs+yss[[1]]*ns[[1]]).monbasisloc;
				Print[ppp];
				Print[PolynomialReduce[ppp,gb,ivars,MonomialOrder->monOrder]];
				Print[PolynomialReduce[ppp,gb,vars,MonomialOrder->monOrder]];
				Print[ppp," ",gb," ",ivars]; *)
				rres = RoundResult[rr,monbasisloc,gtrm,gb,ivars,True, monOrder];
				If[Length[rres]==0, Continue[], Break[]]
			];
			If[Length[rres]==0, Continue[], Print["Primal Done."];Break[]];
			];
		]
		];
		If[Length[rres]==0, Continue[]];
		(* Return successfully afer cleaning it up somewhat *)
		{soscoeff,sos,seq} = rres;
		pos=Position[soscoeff, x_ /; ! TrueQ[x == 0], {1}, Heads -> False]//Flatten;
		Return[{
			gtrm,
			soscoeff[[pos]],
			sos[[pos]],
			Dot[seq,conv],
			lininst}/.replacement]
		(* Exit inner loop *)
		];

	(* Extend the convex hull *)
	msco=Flatten[Map[fvv[#]&,polytope],1]//DeleteDuplicates;
	If[Length[msco]>hullbound,
		Print["Too many points and dimensions, switching to bounding box. Num points: ",Length[msco]," Num vars: ",Length[ivars]];
		polytope=Join[{ConstantArray[0,Length[ivars]]},DiagonalMatrix[Max /@ Transpose[msco]]],
		polytope = hull[msco];
	]
	];
	(* Exit outer loop *)
	Return[failure];
];
FindWitness[polys_List, vars_List, deg_Integer]:= FindWitness[polys, {}, vars, deg]; 


End[];


EndPackage[]
