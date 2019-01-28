(* ::Package:: *)

BeginPackage[ "BarrierCertificate`"]


HandelmanRepEps::usage="
HandelmanRepEps[B_, vars_List, deg_Integer, constraints_List, eps_]
Linear relaxation of polynomial positivity on a set defined by 'constraints' "

BTemplate::usage="BTemplate[deg_Integer?NonNegative,vars_List]
Creates template polynomial of bounded degree with symbolic coefficients"


BoundingBox::usage="BoundingBox[set_,vars_List] Computes a hyperbox in R^|vars| which bounds a given set."


Begin[ "Private`" ]


BoundingBox[set_,vars_List]:=Catch[Module[{BoundingInterval},
BoundingInterval[var_]:={MinValue[{var, set},vars,Reals], MaxValue[{var, set},vars,Reals]};
Throw[Map[BoundingInterval, vars]]
]]


BTemplate[deg_Integer?NonNegative,vars_List]:=Catch[Module[
{monBas,templateCoeffs,template},
(* Compute the monomial basis in 'vars' up to degree 'deg' *)
monBas=Map[#/CoefficientRules[#][[1]][[2]]&,MonomialList[ (Plus @@ Join[vars,{1}])^deg , vars, "DegreeLexicographic"]];
(* Create a template polynomial with symbolic coefficients *)
templateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[monBas]}];
template=Evaluate[templateCoeffs.monBas];
Throw[template]
]]


HandelmanRepEps[V_, vars_List, deg_Integer, constraints_List, eps_] := Catch[Module[
(* Declare local module variables *)
{monExponents, lowerEval, upperEval, Bhandel, fjs, fjalphaproduct, lambdas, lambdaB, lambdaPos, prob, B},

monExponents = First /@ CoefficientRules[(Plus @@ vars + 1)^deg, vars]; 
lowerEval = Thread[vars -> Min /@ constraints]; 
upperEval = Thread[vars -> Max /@ constraints]; 
fjs = Tuples[Thread[{vars - (vars /. lowerEval), (vars /. upperEval) - vars}]]; 
fjalphaproduct = Function[fjproduct, (Times @@ Thread[fjproduct^#1] & ) /@ monExponents]; 
Bhandel = DeleteDuplicates[Flatten[fjalphaproduct /@ fjs]];
B=Bhandel//DeleteDuplicates;
lambdas = Table[Unique["\[Lambda]"], {i, Length[B]}]; 
lambdaB = (#1 == 0 & ) /@ Last /@ CoefficientRules[V - (lambdas.B) -eps, vars]; 
lambdaPos = (#1 >= 0 & ) /@ lambdas;
prob = Join[lambdaB, lambdaPos]; 
Throw[prob]
]]


End[]


EndPackage[]
