(* ::Package:: *)

BeginPackage["SOSsolve`"];


FindWitness::"FindWitness[polys,vars]
Given a list of polynomials p1,...,pk over variables vars attempts to prove that they do not have a common zero"


Begin["Private`"];


monomialList[vars_List,m_Integer?NonNegative]:=Flatten[Inner[#2^#1&,#,vars,Times]&/@Table[FrobeniusSolve[ConstantArray[1,Length[vars]],k],{k,0,m}]]


(* Deletes monomials that cannot possibly in the basis *)
ReduceBasis[monbasis_List,gb_List,vars_List]:= Module[{
	mb,kp,R,coeffs,filpos,umonomials,i},
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
	gb, conv, monOrder, monbasis, kp, R, coeffs,
	umonomials,constraints,i,k,res,y, matrix, result,
	sos, soscoeff, seq,bla,vals,vec},
	(* Some arguments that can be factored out *)
	monOrder = DegreeReverseLexicographic;
	(*deg = 3; (* Degree bound *)*)
	
	(* Solve for the Groebner basis and its conversion matrix *)
	{gb,conv} = GroebnerBasis`BasisAndConversionMatrix[polys, vars, MonomialOrder -> monOrder];
	
	(* Simplify the basis *)
	{monbasis, R, coeffs} = ReduceBasis[monomialList[vars,deg],gb,vars];
	umonomials = Flatten[Map[#[[1]]&,coeffs,{3}],2]//DeleteDuplicates;
	
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
	res=SemidefiniteOptimization[Tr[IdentityMatrix[k].(Symbol["yy"])], {constraints, (Symbol["yy"])\!\(\*UnderscriptBox[\(\[VectorGreaterEqual]\), 
TemplateBox[{"k"},
"SemidefiniteConeList"]]\) 0}, (Symbol["yy"]) \[Element] Matrices[k]];
	If[MemberQ[res[[1]][[2]],Indeterminate,{2}],Return[{0,Map[0*#&,polys]}]];
	(* Round the result *)
	matrix=Rationalize[res[[1]][[2]],0.01];
	{vals,vec}=Eigensystem[matrix];
	(* The polynomials in the SOS are given by *)
	sos = Dot[vec,monbasis];
	(* Each with (positive) coefficient *)
	soscoeff = vals;
	result = 1+Dot[soscoeff,Map[#^2&,sos]];
	{seq,bla} = PolynomialReduce[result,gb,vars];
	Return[{result,Dot[seq,conv]}]
]


End[]


EndPackage[]