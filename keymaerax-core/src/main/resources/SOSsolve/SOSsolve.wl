(* ::Package:: *)

BeginPackage["SOSsolve`"];


FindWitness::"FindWitness[polys,vars]
Given a list of polynomials p1,...,pk over variables vars attempts to prove that they do not have a common zero"


Begin["Private`"];


allMonomials[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,0,m}]]


monomialList[poly_, vars_] := Times @@ (vars^#) & /@ CoefficientRules[poly, vars][[All, 1]]


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
	mb,kp,R,coeffs,filpos,umonomials,i,lgb},
	mb = monbasis;
	kp = KroneckerProduct[mb,mb];
	(* The outer product matrix of the basis *)
	R = Map[PolynomialReduce[#,gb,vars][[2]]&,kp,{2}];
	coeffs=Map[CoefficientRules[#,vars,"DegreeReverseLexicographic"]&,R,{2}];
	While[True,
	(* The unique monomials appearing anywhere in there *)
	umonomials = Flatten[Map[#[[1]]&,coeffs,{3}],2]//DeleteDuplicates;
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


(* Input:
polys {p_1,p_2,...} - polynomials assumed to be = 0
ineqs {g_1,g_2,...} - polynomials assumed to be \[NotEqual] 0
vars  {v_1,v_2,...} - variables
deg - degree bound
*)
FindWitness[polys_List, ineqs_List, vars_List, deg_Integer]:= Module [{
	failure, gb, conv, monOrder, monbasis, kp, R, coeffs,
	umonomials,constraints,i,k,res,y, matrix, result,gtrm1,
	sos, soscoeff, seq,bla,vals,vec,prem,check,redseq,redg,gtrm,gcoeff,gmc,gmons,gheu},
	(* Some arguments that can be factored out *)
	monOrder = DegreeReverseLexicographic;

	(* result type encoding of failure*)
	failure = {0,Map[0*#&,polys]};
	
	Print["Polynomials assumed to be zero: ",polys];
	Print["Polynomials assumed to be non-zero: ",ineqs];

	(* Solve for the Groebner basis and its conversion matrix *)
	{gb,conv} = GroebnerBasis`BasisAndConversionMatrix[polys, vars, MonomialOrder -> monOrder];
	(* gtrm is a term known to be strictly positive
	   i.e., we will attempt to find gtrm+sos = 0 *)
	gtrm1 = (Apply[Times,ineqs]);
	gtrm = gtrm1^2;
	(* Check that the Groebner basis does not already trivially reduce the non-zero term *)
	{redseq,redg} = PolynomialReduce[gtrm,gb,vars];
	If[redg===0, Print["Assumptions contradictory"];Return[{gtrm,Dot[redseq,conv]}]];
	Print["Using g: ",gtrm, " Reducing to: ",redg];
	
	gcoeff=CoefficientRules[redg,vars,"DegreeReverseLexicographic"];
	(* monomials and coefficients appearing in g *)
	gmc = Map[FromCoefficientRules[{#[[1]]->1},vars]->#[[2]]&,gcoeff];
	gmons = Map[#[[1]]&,gmc];
	
	gheu = monomialList[PolynomialReduce[gtrm1,gb,vars][[2]],vars];
	
	prem = Join[gheu,allMonomials[vars,deg]];
	Print["Input monomials: ",Length[prem]];
	(* Filter all monomials that reduce ? *)
	prem = Select[prem, PolynomialReduce[#,gb,vars][[2]]===#&];
	(* Degree bound too low *)
	If[Length[prem]===0,Return[failure]];
	
	Print["Filter input monomials: ",Length[prem]];
	(* Map[Print[#," ",PolynomialReduce[#,gb,vars][[2]]]&,prem]; *)
	
	(* Simplify the basis *)
	{monbasis, R, coeffs} = ReduceBasis[prem,gmons,gb,vars];
	umonomials = Flatten[Map[#[[1]]&,coeffs,{3}],2]//DeleteDuplicates;
	
	Print["Solving for constraints "];
	(* Compute the constraints *)
	constraints={};
	(* For each unique monomial, we add a constraint *)
	For[i=1,i <= Length[umonomials],i++,
	Block[{lk,mon,umon,coeff,constr},
		umon = umonomials[[i]];
		mon = FromCoefficientRules[{umon->1},vars];
		lk=Flatten[Map[Lookup[#,{umon},0]&,coeffs,{2}],{3}][[1]];
		coeff=-Lookup[gmc,mon,0];
		(*Print[lk // MatrixForm];*)
		constr=Tr[lk.Symbol["yy"]]==coeff;
		constraints=Append[constraints,constr];
	]
	];
	
	If[Length[constraints]===0, Return[failure]];
	
	(* Finally solve the SDP *)
	k=Length[monbasis];
	Print["Total constraints: ",Length[constraints]];
	Print["Dimension: ",Length[monbasis]];
	(* Print[monbasis]; *)

	res=SemidefiniteOptimization[Tr[IdentityMatrix[k].(Symbol["yy"])], {constraints, VectorGreaterEqual[{Symbol["yy"], 0}, {"SemidefiniteCone", k}]}, Element[Symbol["yy"], Matrices[k]],MaxIterations->1000];

	If[MemberQ[res[[1]][[2]],Indeterminate,{2}],Return[failure]];
	(* Round the result *)
	matrix=res[[1]][[2]];
	matrix=1/2*(matrix+Transpose[matrix]);
	matrix=Rationalize[matrix,0.01];
	{vec,vals}=LDLT[matrix];
	(*Print[{vals,vec}];*)
	(* The polynomials in the SOS are given by *)
	sos = Dot[vec,monbasis];
	(* Each with (positive) coefficient *)
	soscoeff = vals;
	result = gtrm+Dot[soscoeff,Map[#^2&,sos]];
	{seq,bla} = PolynomialReduce[result,gb,vars];
	check = FullSimplify[Dot[Dot[seq, conv], polys] - result];
	If[Not[check === 0], Return[failure]];
	Return[{result,Dot[seq,conv]}]
]
FindWitness[polys_List, vars_List, deg_Integer]:= FindWitness[polys, {},vars, deg]; 


End[]


EndPackage[]
