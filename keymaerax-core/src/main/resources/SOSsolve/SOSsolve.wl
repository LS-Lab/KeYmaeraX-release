(* ::Package:: *)

BeginPackage["SOSsolve`"];


FindWitness::"FindWitness[polys,vars]
Given a list of polynomials p1,...,pk over variables vars attempts to prove that they do not have a common zero"


Begin["Private`"];


monomialList[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,0,m}]]


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
ReduceBasis[monbasis_List,gb_List,vars_List]:= Module[{
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
		If[mon===1, Continue[]]; (* The RHS is -1 *)
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


FindWitness[polys_List, vars_List, deg_Integer]:= Module [{
	failure, gb, conv, monOrder, monbasis, kp, R, coeffs,
	umonomials,constraints,i,k,res,y, matrix, result,
	sos, soscoeff, seq,bla,vals,vec,prem,check},
	(* Some arguments that can be factored out *)
	monOrder = DegreeReverseLexicographic;

	(* result type encoding of failure*)
	failure = {0,Map[0*#&,polys]};

	(* Solve for the Groebner basis and its conversion matrix *)
	{gb,conv} = GroebnerBasis`BasisAndConversionMatrix[polys, vars, MonomialOrder -> monOrder];
	
	prem = monomialList[vars,deg];
	Print["Input monomials: ",Length[prem]];
	(* Filter all monomials that reduce ? *)
	prem = Select[prem,PolynomialReduce[#,gb,vars][[2]]===#&];
	Print["Filter input monomials: ",Length[prem]];
	(* Map[Print[#," ",PolynomialReduce[#,gb,vars][[2]]]&,prem]; *)
	
	(* Simplify the basis *)
	{monbasis, R, coeffs} = ReduceBasis[prem,gb,vars];
	(* make special case less special for the rest of the code... *)
	{monbasis, R, coeffs} = If[Length[monbasis] === 0, {{1}, {{0}}, {{{}}}}, {monbasis, R, coeffs}];
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
		coeff=If[mon===1,-1,0];
		constr=Tr[lk.Symbol["yy"]]==coeff;
		constraints=Append[constraints,constr];
	]
	];

	(* Finally solve the SDP *)
	k=Length[monbasis];
	Print["Total constraints: ",Length[constraints]];
	Print["Dimension: ",Length[monbasis]];
	(* Print[monbasis]; *)

	res=SemidefiniteOptimization[Tr[IdentityMatrix[k].(Symbol["yy"])], {constraints, VectorGreaterEqual[{Symbol["yy"], 0}, {"SemidefiniteCone", k}]}, Element[Symbol["yy"], Matrices[k]]];

	If[MemberQ[res[[1]][[2]],Indeterminate,{2}],Return[failure]];
	(* Round the result *)
	matrix=res[[1]][[2]];
	matrix=1/2*(matrix+Transpose[matrix]);
	matrix=Rationalize[matrix,0.01];
	Print[matrix // MatrixForm];
	{vec,vals}=LDLT[matrix];
	(*Print[{vals,vec}];*)
	(* The polynomials in the SOS are given by *)
	sos = Dot[vec,monbasis];
	(* Each with (positive) coefficient *)
	soscoeff = vals;
	result = 1+Dot[soscoeff,Map[#^2&,sos]];
	{seq,bla} = PolynomialReduce[result,gb,vars];
	check = FullSimplify[Dot[Dot[seq, conv], polys] - result];
	If[Not[check === 0], Return[failure]];
	Return[{result,Dot[seq,conv]}]
]


End[]


EndPackage[]
