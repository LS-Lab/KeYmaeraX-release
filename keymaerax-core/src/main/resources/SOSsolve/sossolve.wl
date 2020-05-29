(* ::Package:: *)

Needs["NDConvexHull`",FileNameJoin[{Directory[],"NDConvexHull.wl"}]]


BeginPackage["sossolve`"];


FindWitness::"FindWitness[polys,vars]
Given a list of polynomials p1,...,pk over variables vars attempts to prove that they do not have a common zero"


Begin["Private`"];


monOrder = DegreeReverseLexicographic;


allMonomials[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,0,m}]]


monomialList[poly_, vars_] := Times @@ (vars^#) & /@ CoefficientRules[poly, vars,monOrder][[All, 1]]


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
ReduceBasis[monbasis_List,gcoeff_List,gb_List,vars_List,filter_]:= Module[{
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
ReduceLin[prem_,gb_,vars_]:=Module[{red,linred,mons,lin,pos,mat,postmons},
	red = Map[
		PolynomialReduce[#,gb,vars,MonomialOrder->monOrder][[2]]&,
		prem];
	linred=Map[CoefficientRules[#,vars,monOrder]&,red];
	mons =Map[#[[1]]&,Flatten[linred,1]]//DeleteDuplicates;
	lin=Map[Lookup[#,mons,0]&,linred];
	{pos,mat}=LinIndepRows[lin];
	postmons=prem[[pos]];
	postmons	
];


(* Round result *)
RoundResult[res_,monbasis_,gtrm_,gb_,vars_,skipround_]:= Module[{
	matrix, L, vals, sos, fin, power, seq, rem, maxiters,i,denom,powdenom},
	maxiters=50;
	powdenom=32;
	denom=1;
	(* use 1/1, 1/2, ..., 1/16, then double the denominator *)
	For[i=1,i<=maxiters,i++,
	power=1/denom;
	If[i < powdenom, denom=denom+1, denom=2*denom];
	(* Force matrix to be symmetric then rationalize *)
	matrix=res;
	If[Not[skipround],
		matrix=1/2*(matrix+Transpose[matrix]);
		matrix=Rationalize[Round[matrix,power]]];
	(*Print[Chop[matrix-Inverse[eigvec].DiagonalMatrix[Chop[eigval,power]].eigvec]];*)
	(*Print[Inverse[eigvec].Dot[DiagonalMatrix[eigval],eigvec]-matrix];*)
	(* matrix = L * Diag[vals] * L^T *)
	{L,vals}=LDLT[matrix];
	If[Not[AllTrue[vals, # >= 0&]],
		(*Print["LDLT failed. ",vals];*)
		If[skipround,Return[{}],Continue[]]];
	(* The polynomials in the SOS are given by *)
	sos = Dot[Transpose[L],monbasis];
	(* This is the thing that must reduce to zero *)
	fin = gtrm+Dot[vals,Map[#^2&,sos]];
	{seq,rem} = PolynomialReduce[fin,gb,vars,MonomialOrder->monOrder];
	(*Print["Rounding: ",power," SOS: ",fin," Remainder: ",rem];*)
	If[rem===0,Return[{vals,sos,seq}]];
	If[skipround,Return[{}]]
	];
	Return[{}];
]



(* Find monomials that can be eliminated *)
Pvars[polys_,vars_]:= Module[{
	newvars,linred,mons,i,row,nz,z,coeffs,newmons,mon,newvar,replacement},
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
			newmons=MapThread[Append,{newmons[[All,z]],2*coeffs}];
			repr=newvar->FromCoefficientRules[{row/2->1},newvars],
			newmons=MapThread[Append,{newmons[[All,z]],coeffs}];
			repr=newvar->mon
		];
		Print["Eliminating Monomial: ",mon," with: ",repr];
		replacement=Join[replacement,{repr}];
		newvars=Join[newvars[[z]],{newvar}];
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


(* Eliminate
linear constraints x-t =0 (x does not appear in t) or
almost-linear ones x^2-SOS=0 (x does not appear in SOS)
*)
ElimLinear[polys_, vars_] := Module[{
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
	{curpolys,(* curineq,*)Complement[vars, delvars],lininst}
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
ExpandSymmetric[ls_,k_]:=Module[{},
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
	(* Is orthogonalization required?
	ns = Orthogonalize[ns]; *)
	sol = LinearSolve[prim,cs];
	Return[{ns,sol}]
]


(* Given:
	gb - groeber basis
	vars - variables
	gmc - monomial&coefficient representation of g, where
		  g is the monomial to solve for g+SOS^2\[Equal]0 (typically g = 1)
	mons - monomials
	1) Minimizes those monomials
	2) Solves the resulting constraints
*)
MonSolve[gb_List,vars_List,gcoeff_List, mons_List, filter_, primal_]:=Module[{
	redseq,redg,
	prem, monbasis, R, coeffs, umonomials,
	constraints, cs, k, tt, res, i},
	
	prem = mons;	
	Print["No. input monomials: ",Length[prem]];
	
	(* Filter linearly dependent monomials *)
	prem=ReduceLin[prem,gb,vars];
	Print["After linear filter: ",Length[prem]];
	
	(* Degree bound too low (should be impossible) *)
	If[Length[prem]===0, Return[{}]];
	
	(* Further simplify the basis *)
	{monbasis, R, coeffs} = ReduceBasis[prem,gcoeff,gb,vars,filter];
	
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
	(* Map[Print[#//MatrixForm]&,constraints];
	Print[cs]; *)
	
	(* Finally solve the SDP *)
	k=Length[monbasis];
	Print["Total constraints: ",Length[constraints]];
	Print["Dimension: ",Length[monbasis]];
	
	(* Solving in primal *)
	If[primal,
		Block[{},
		Print["Solving in primal form"];
		{ns,bs}=ConvertPrimalRaw[constraints,cs,k];
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
FilterPolytope[mons_,vars_,polytope_]:=Module[{},
	(* Print[Map[2*CoefficientRules[#,vars,monOrder][[1]][[1]]&,mons]]; *)
	mm=Select[mons,ConvexDependentQ[polytope,2*CoefficientRules[#,vars,monOrder][[1]][[1]]]&];
	Return[mm];
]


(* Input:
polys {p_1,p_2,...} - polynomials assumed to be = 0
ineqs {g_1,g_2,...} - polynomials assumed to be \[NotEqual] 0
vars  {v_1,v_2,...} - variables
deg - degree bound
monomials - optional argument that uses that fixed list of monomials (overrides deg)
*)
FindWitness[polysPre_List, ineqs_List, varsPre_List, degBound_Integer, monomials_List : {}]:= Module [{
	polys,vars,
	failure, gb, conv, monbasis, kp, R, coeffs,
	umonomials,constraints,i,k,res,y, matrix, result,gtrm1,
	sos, soscoeff, seq,bla,vec,prem,check,redseq,redg,deg,rm,
	gtrm,gcoeff,gmc,gmons,cs,tt,pos,rres,trivseq,trivg,ivars,replacement,lininst,
	trunclim,hullbound,maxcofdeg,ms,msco,hull,vv,done,polytope,prevdeg,polydeg,
	primaltrunclim},

	maxcofdeg=20;
	trunclim=20;
	primaltrunclim=15;
	hullbound=300; (* stops using convex hull if no.points * dimension is above this number *)
	(* result type encoding of failure*)
	failure = {0,{},{},{}};
	
	(* TODO: doesn't work in ineq case for now  *)
	{polys,vars,replacement}=If[ineqs==={},
		Pvars[polysPre,varsPre],
		{polysPre,varsPre,{}}
	];

	(* TODO: this somehow needs to return a interpretable result *)
	{polys,vars,lininst}=If[ineqs==={},
		ElimLinear[polys,vars],
		{polys,vars,{}}
	];

	Print["Polynomials assumed to be zero: ",polys];
	Print["Polynomials assumed to be non-zero: ",ineqs];

	(* gtrm is a term known to be strictly positive
	   i.e., we will attempt to find gtrm+sos = 0 *)
	gtrm1 = (Apply[Times,ineqs]);
	gtrm = gtrm1^2;
	
	(* Polys already trivially imply gtrm == 0 *)
	If[Not[MemberQ[polys,0]],
	(* NOTE: there's a weird bug with PolynomialReduce when polys has 0 *)
	{trivseq,trivg} = PolynomialReduce[gtrm,polys,vars,MonomialOrder -> monOrder];
	If[trivg===0,
		Print["Assumptions contradictory"];
		Return[{gtrm,{},{}, trivseq, lininst}]]];
	
	(* Solve for the Groebner basis and its conversion matrix *)
	{gb,conv} = GroebnerBasis`BasisAndConversionMatrix[polys, vars, MonomialOrder -> monOrder];
	Print[GroebnerBasis[polys,vars,{vars[[1]]},MonomialOrder->EliminationOrder]];
	(* Check that the Groebner basis does not already trivially reduce the non-zero term *)
	{redseq,redg} = PolynomialReduce[gtrm,gb,vars,MonomialOrder -> monOrder];
	If[redg===0,
		Print["Assumptions contradictory"];
		Return[{gtrm,{},{},Dot[redseq,conv],lininst}]];

	Print["Using g: ", gtrm, " Reducing to: ",redg];
	gcoeff=CoefficientRules[redg,vars,monOrder];
	ivars=Map[Variables[#]&,Join[{redg},gb]]//Flatten//DeleteDuplicates;

	ms = Map[CoefficientRules[#,ivars,monOrder]&,gb];
	msco = Flatten[Map[#[[1]]&,ms,{2}],1];
	hull=If[Length[ivars]<=2,ConvexHullCorners,#[[(NDConvexHull`CHNQuickHull[#][[1]])]]&];
	If[Length[msco]*Length[ivars]>hullbound,
		Print["Too many points / dimensions, switching to bounding box ",Length[msco]," ",Length[ivars]];
		polytope=Join[{ConstantArray[0,Length[ivars]]},DiagonalMatrix[Max /@ Transpose[msco]]],
		polytope = hull[msco];
	];
	vv = Map[CoefficientRules[#,ivars,monOrder][[1]][[1]]&, Join[{1},ivars]];
	done = {};
	
	prevdeg=1;
	For[polydeg=0,polydeg<=maxcofdeg,polydeg++,
	Print["Using polytope: ",polytope];
	For[deg=1,deg<=degBound,deg++,
	
	Print["Degree bound: ",deg];
	
	(* All monomials up to degree bound *)
	(* Only consider those variables occuring in the groebner basis or g *)
	prem = allMonomials[ivars,deg];
	prem = FilterPolytope[prem,ivars,polytope];
	If[MemberQ[done,prem] || Length[prem]===0,
		Print["Skipping (prev max deg: ",prevdeg,")"];
		If[deg <= prevdeg, Continue[], Break[]]];
	(* TODO: it should be possible to exit the inner loop when no further monomials are possible *)
	done=Join[{prem},done];
	prevdeg=Max[{prevdeg,deg}];
	
	rm = MonSolve[gb, vars,gcoeff, prem, True, False];
	If[rm==={},Continue[]];
	{res,monbasis,constraints,cs}=rm;
	(* Print[Normal[res]//MatrixForm]; *)
	(* Round the result *)
	rres = RoundResult[Normal[res],monbasis,gtrm,gb,vars,False];

	If[Length[rres]==0,
		Print["Rounding heuristic failed, attempt resolve."];
		(* Attempt to resolve by truncating "zeros" *)
		Block[{diag,thresh,goodpos,prev, rmloc,
			resloc,monbasisloc,constraintsloc,csloc,
			bs,ns,ys,j,yss,rr
		},
		diag=Normal[Diagonal[res]];
		prev={};
		For[i=0,i <= trunclim, i++,
		If[i<trunclim,
		(* Truncate *)
			thresh=10^-i;
			goodpos=Position[diag,_?(#>thresh&)]//Flatten;
			If[monbasis[[goodpos]]===prev, Continue[]];
			Print["Truncating (and re-solve) at: ",thresh];
			prev=monbasis[[goodpos]];
			Print["Keeping monomials: ", prev];
			rmloc = MonSolve[gb,vars,gcoeff, prev, False, False];
			If[rmloc==={},Continue[]];
			{resloc,monbasisloc,constraintsloc,csloc}=rm;
			rres = RoundResult[Normal[resloc],monbasisloc,gtrm,gb,vars,False];
			If[Length[rres]==0,, Print["done."]; Break[]];
		,
		(* No truncate or (dual) resolve on last iteration *)
			If[monbasis===prev, Continue[]];
			Print["Final iteration, skipping truncation"];
			prev=monbasis;
		];
		Print["Resolving in primal"];
		rmloc = MonSolve[gb, vars,gcoeff, prev, False, True];
		If[rmloc==={},Continue[]];
		{bs,ns,ys,monbasisloc,constraintsloc,csloc}=rmloc;
		For[j=1,j<=primaltrunclim,j++,
			yss = Rationalize[Round[Normal[ys],10^-j]];
			rr = bs+yss.ns;
			rres = RoundResult[rr,monbasisloc,gtrm,gb,vars,True];
			Print["primal trunc iteration: ",j," ",rres," ",N[Eigenvalues[rr]]];
			If[Length[rres]==0, Continue[], Print["done."];Break[]]
		];
		If[Length[rres]==0, Continue[], Print["done."];Break[]];
		];
	]];
	If[Length[rres]==0,Continue[]];
	{soscoeff,sos,seq} = rres;
	pos=Position[soscoeff, x_ /; ! TrueQ[x == 0], {1}, Heads -> False]//Flatten;
	Return[{
		gtrm/.replacement,
		soscoeff[[pos]]/.replacement,
		sos[[pos]]/.replacement,
		Dot[seq,conv]/.replacement,
		lininst}]
	];
	
	fvv=Function[{a},Map[#+a&,vv]];
	msco=Flatten[Map[fvv[#]&,polytope],1]//DeleteDuplicates;
	(* TODO: Arbitrary threshold for switching into non-convex hull mode *)
	If[Length[msco]>hullbound,
		Print["Too many points / dimensions, switching to bounding box ",Length[msco]," ",Length[ivars]];
		polytope=Join[{ConstantArray[0,Length[ivars]]},DiagonalMatrix[Max /@ Transpose[msco]]],
		polytope = hull[msco];
	]];
	
	Return[failure];
];
FindWitness[polys_List, vars_List, deg_Integer]:= FindWitness[polys, {},vars, deg]; 


End[]


EndPackage[]
