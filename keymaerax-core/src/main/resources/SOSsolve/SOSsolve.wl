(* ::Package:: *)

BeginPackage["SOSsolve`"];


FindWitness::"FindWitness[polys,vars]
Given a list of polynomials p1,...,pk over variables vars attempts to prove that they do not have a common zero"


Begin["Private`"];


monOrder = DegreeReverseLexicographic;


allMonomials[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,0,m}]]


monomialList[poly_, vars_] := Times @@ (vars^#) & /@ CoefficientRules[poly, vars,monOrder][[All, 1]]


mapSymmetric[n_, f_] := Block[{f1, f2},
  f1 = LowerTriangularize[#, -1] + Transpose@LowerTriangularize[#] &@
     ConstantArray[Range@#, #] &;
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
ReduceBasis[monbasis_List,gmons_,gb_List,vars_List]:= Module[{
	mb,kp,R,coeffs,filpos,umonomials,i,lgb,tt},
	mb = monbasis;
	{tt,kp} = Timing[KroneckerProduct[mb,mb]];
	Print["Kronecker time: ",tt];	
	(* The outer product matrix of the basis *)
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
		mon = FromCoefficientRules[{umon->1},vars];
		If[MemberQ[gmons,mon], Continue[]]; (* The RHS is non-zero *)
		lk=Flatten[Map[Lookup[#,{umon},0]&,coeffs,{2}],{3}][[1]];
		If[DiagonalMatrixQ[lk],
		Block[{pos},
			pos=Position[Diagonal[lk],_?(#!=0&)];
			If[Length[pos]==1, filpos=Join[filpos,pos[[1]]]; ]
		];
		]
	]
	];
	If[Length[filpos]==0,Break[]];
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
RoundResult[res_,monbasis_,gtrm_,gb_,vars_]:= Module[{
	matrix, L, vals, sos, fin, power, seq, rem, maxiters,i
	},
	maxiters=20;
	For[i=0,i<maxiters,i++,
	power=2^-(2*i);
	(* Force matrix to be symmetric then rationalize *)
	matrix=res;
	matrix=1/2*(matrix+Transpose[matrix]);
	matrix=Rationalize[Round[matrix,power]];
	(* matrix = L * Diag[vals] * L^T *)
	{L,vals}=LDLT[matrix];
	If[Not[AllTrue[vals, # >= 0&]], Continue[]];
	(* The polynomials in the SOS are given by *)
	sos = Dot[Transpose[L],monbasis];
	(* This is the thing that must reduce to zero *)
	fin = gtrm+Dot[vals,Map[#^2&,sos]];
	{seq,rem} = PolynomialReduce[fin,gb,vars,MonomialOrder->monOrder];
	Print["Rounding: ",power," Remainder: ",rem];
	If[rem===0,Return[{vals,sos,seq}]]
	];
	Return[{}];
]



(* Input:
polys {p_1,p_2,...} - polynomials assumed to be = 0
ineqs {g_1,g_2,...} - polynomials assumed to be \[NotEqual] 0
vars  {v_1,v_2,...} - variables
deg - degree bound
*)
FindWitness[polys_List, ineqs_List, vars_List, degBound_Integer]:= Module [{
	failure, gb, conv, monbasis, kp, R, coeffs,
	umonomials,constraints,i,k,res,y, matrix, result,gtrm1,
	sos, soscoeff, seq,bla,vec,prem,check,redseq,redg,deg,
	gtrm,gcoeff,gmc,gmons,gheu,cs,tt,pos,rres},

	(* result type encoding of failure*)
	failure = {0,{},{},{}};
	
	Print["Polynomials assumed to be zero: ",polys];
	Print["Polynomials assumed to be non-zero: ",ineqs];

	(* Solve for the Groebner basis and its conversion matrix *)
	{gb,conv} = GroebnerBasis`BasisAndConversionMatrix[polys, vars, MonomialOrder -> monOrder];
	
	(* gtrm is a term known to be strictly positive
	   i.e., we will attempt to find gtrm+sos = 0 *)
	gtrm1 = (Apply[Times,ineqs]);
	gtrm = gtrm1^2;
	(* Check that the Groebner basis does not already trivially reduce the non-zero term *)
	{redseq,redg} = PolynomialReduce[gtrm,gb,vars,MonomialOrder -> monOrder];
	If[redg===0, Print["Assumptions contradictory"];Return[{gtrm,{},{},Dot[redseq,conv]}]];
	Print["Using g: ",gtrm, " Reducing to: ",redg];
	
	gcoeff=CoefficientRules[redg,vars,monOrder];
	(* monomials and coefficients appearing in g *)
	gmc = Map[FromCoefficientRules[{#[[1]]->1},vars]->#[[2]]&,gcoeff];
	gmons = Map[#[[1]]&,gmc];
	
	(* gheu = monomialList[PolynomialReduce[gtrm1,gb,vars][[2]],vars]; *)
	gheu = monomialList[gtrm1,vars]; 
	
	For[deg=1,deg<=degBound,deg++,
	
	(* All monomials up to degree bound *)
	prem = allMonomials[vars,deg];
	Print["No. input monomials: ",Length[prem]];
	
	(* Filter linearly dependent monomials *)
	prem=ReduceLin[prem,gb,vars];
	Print["After linear filter: ",Length[prem]];
	
	(* Filter all monomials that reduce ?*)
	(*prem = Select[prem, PolynomialReduce[#,gb,vars,MonomialOrder->monOrder][[2]]===#&];
	prem = Join[prem,gheu]//DeleteDuplicates;
	Print["Filter input monomials: ",Length[prem]];*)
		
	(* Degree bound too low (should be impossible with heuristics) *)
	If[Length[prem]===0, Continue[]];
	
	(*
	Map[Print[#," ",PolynomialReduce[#,gb,vars][[2]]]&,prem];*)
	
	(* Simplify the basis *)
	{monbasis, R, coeffs} = ReduceBasis[prem,gmons,gb,vars];
	
	(* umonomials = Map[#[[1]]&, Flatten[Diagonal[coeffs]]]//DeleteDuplicates; *)
	umonomials = Flatten[Map[#[[1]]&,coeffs,{3}],2]//DeleteDuplicates;
		
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
		coeff=-Lookup[gmc,mon,0];
		(*Print[lk // MatrixForm];*)
		(* constr=Tr[lk.Symbol["yy"]]==coeff; *)
		constraints=Append[constraints,lk];
		cs=Append[cs,coeff];
	]
	];
	
	If[Length[constraints]===0, Continue[]];
	
	(* Finally solve the SDP *)
	k=Length[monbasis];
	Print["Total constraints: ",Length[constraints]];
	Print["Dimension: ",Length[monbasis]];
	(* Print[monbasis]; *)

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
		Continue[]];
	
	Print["Eigenvalues: ",Eigenvalues[res[[2]]]];
	(*
	res=SemidefiniteOptimization[
		Tr[IdentityMatrix[k].(Symbol["yy"])],
		{constraints,
		VectorGreaterEqual[{Symbol["yy"], 0}, {"SemidefiniteCone", k}]},
		Element[Symbol["yy"], Matrices[k]],
		Method\[Rule]"DSDP"];
	*)
	(* Round the result *)
	rres = RoundResult[Normal[res[[2]]],monbasis,gtrm,gb,vars];
	If[Length[rres]==0,
		Print["Rounding heuristic failed"];
		Continue[]];
	{soscoeff,sos,seq} = rres;
	pos=Position[soscoeff, x_ /; ! TrueQ[x == 0], {1}, Heads -> False]//Flatten;
	Return[{gtrm,soscoeff[[pos]],sos[[pos]],Dot[seq,conv]}]
	];
	Return[failure];
]
FindWitness[polys_List, vars_List, deg_Integer]:= FindWitness[polys, {},vars, deg]; 


End[]


EndPackage[]
