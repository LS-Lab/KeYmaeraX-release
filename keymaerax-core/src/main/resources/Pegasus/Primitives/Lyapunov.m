(* ::Package:: *)

Needs["Primitives`",FileNameJoin[{Directory[],"Primitives","Primitives.m"}]]
Needs["MATLink`"]


BeginPackage["Lyapunov`"];


(* This should be at a higher level than primitives, probably... *)
GenCLF::usage="GenCLF[systems_List] tries to solve for a CLF of the given systems";
GenMLF::usage="GenMLF[systems_List, transitions_List] tries to solve for an MLF of the given systems";


Begin["`Private`"];


DEFAULTPRECISION = 10;
DEFAULTROUND=6;


(* Return all monomials of a given polynomial wrt the variables *)
monomialList[poly_, vars_] := Times @@ (vars^#) & /@ CoefficientRules[poly, vars][[All, 1]]


(* A very basic Mathematica to Matlab expression converter *)
MmaToMatlab[list_List]:="["<>StringRiffle[Map[MmaToMatlab, list],"; "]<>"]"
MmaToMatlab[Power[trm_,exp_]]:=MmaToMatlab[trm]<>"^("<>MmaToMatlab[exp]<>")"
MmaToMatlab[Times[product_]]:= "("<>StringRiffle[MmaToMatlab /@ (List @@ product), "*"]<>")"
MmaToMatlab[product_Plus]:= "("<>StringRiffle[MmaToMatlab /@ (List @@ product), "+"]<>")"
MmaToMatlab[rat_Rational]:=InputForm[N[rat, DEFAULTPRECISION], NumberMarks->False]//ToString
MmaToMatlab[atom_?AtomQ]:=ToString[atom//InputForm]

(* Relational symbols *)
MmaToMatlab[Greater[lhs_,rhs_]]:=MmaToMatlab[lhs]<>">"<>MmaToMatlab[rhs] 
MmaToMatlab[GreaterEqual[lhs_,rhs_]]:=MmaToMatlab[lhs]<>">="<>MmaToMatlab[rhs] 
MmaToMatlab[Equal[lhs_,rhs_]]:=MmaToMatlab[lhs]<>"=="<>MmaToMatlab[rhs] 
MmaToMatlab[LessEqual[lhs_,rhs_]]:=MmaToMatlab[lhs]<>"<="<>MmaToMatlab[rhs] 
MmaToMatlab[Less[lhs_,rhs_]]:=MmaToMatlab[lhs]<>"<"<>MmaToMatlab[rhs] 

(* Logical connectives *)
MmaToMatlab[implication_Implies]:="("<>MmaToMatlab[implication//LogicalExpand]<>")"
MmaToMatlab[conjunction_And]:="("<>StringRiffle[MmaToMatlab /@ List @@ conjunction, " & "]<>")"
MmaToMatlab[disjunction_Or]:="("<>StringRiffle[MmaToMatlab /@ List @@ disjunction, " | "]<>")"
MmaToMatlab[Not[negation_]]:="~("<>MmaToMatlab[negation]<>")"

MmaToMatlab[True]:="true"
MmaToMatlab[False]:="false"


ConjunctiveIneqSetQ[S_]:=Module[{},
((TrueQ[Head[S]===GreaterEqual || Head[S]===LessEqual] || Head[S]===Greater || Head[S]===Less || Head[S]===Equal) &&
	AllTrue[Map[PolynomialQ[#,vars] &, Level[S,{1}]], TrueQ]) ||
(TrueQ[Head[S]===And] && AllTrue[Map[ConjunctiveIneqSetQ[#] &, Level[S,{1}]], TrueQ])
]


(* Checks that set is a conjunction and extracts polynomials TODO: this should "relax" equalities p=0 by bloating them to -eps \[LessEqual] p \[LessEqual] eps rather than p\[GreaterEqual]0 && p\[LessEqual]0 which are ill-behaved *)
ExtractPolys[set_]:=Module[{S=Primitives`DNFNormalizeGtGeq[set],lst},
	If[ConjunctiveIneqSetQ[S],
	  lst= S/.{And->List, GreaterEqual[lhs_,0]:> lhs, Greater[lhs_,0]:> lhs};
	  If[TrueQ[Head[S]==And],
	    lst,
	    {lst}
	  ],
		{}
	]
]

RoundPolys[p_,vars_]:=Module[{cr},
	cr = CoefficientRules[p,vars];
	If[Length[cr] > 0,
		MapAt[Function[x,Rationalize[Round[x,1/10^DEFAULTROUND]]],cr,{All,2}]~FromCoefficientRules~vars
	,{}]
]


GenCLF[systems_List, opts:OptionsPattern[]]:=Catch[Module[
{allvars,vfs,vfsstr,domains,normdom,dim,origsubs,i,fieldstr,domainsstr,domstr,locstr,constrstr,script,res,lines,B,sosprog,link},

Print["Attempting to generate a CLF with SOS Programming"];

allvars = Map[#[[2]]&,systems] // Flatten // DeleteDuplicates;
vfs=Map[#[[1]]&,systems];
domains=Map[ExtractPolys[#[[3]]]&,systems];
dim=Length[allvars];

(*Print["Domains: ",domains];*)

(* Open a link to Matlab *)
link=MATLink`OpenMATLAB[];

vfsstr=Map[MmaToMatlab[#]&,vfs];
fieldstr= "";
For[i=1,i<=Length[vfsstr],i++,
	fieldstr=fieldstr<>"field"<>MmaToMatlab[i]<>"="<>vfsstr[[i]]<>";\n"];

domainsstr=Map[MmaToMatlab[#]&,domains];
domstr= "";
For[i=1,i<=Length[domainsstr],i++,
	domstr=domstr<>"dom"<>MmaToMatlab[i]<>"="<>domainsstr[[i]]<>";\n"];

locstr="
    % Constraints for ODE $
    dB$ = 0*vars(1);
    for i = 1:length(vars)
      dB$ = dB$+diff(B,vars(i))*field$(i);
    end

    expr$ = -dB$;
    % expr$ = -dB$-epslb;

    if ~isempty(dom$)
        dsum=0;
        for i=1:length(dom$)
          [prog,DP${i}] = sossosvar(prog,monvec);
          dsum = dsum + DP${i}*dom$(i);
        end

        prog = sosineq(prog, expr$ -dsum);
    else
        prog = sosineq(prog, expr$);
    end
	";
	
constrstr="";
For[i=1,i<=Length[vfsstr],i++,
	constrstr=constrstr<>StringReplace[locstr,{"$"->MmaToMatlab[i]}]
];


sosprog="
% CLF

clear;
% Inputs from Mathematica
% Variables
pvar "<>StringRiffle[Map[MmaToMatlab, allvars], " "]<>" dummy;
vars = "<>MmaToMatlab[allvars]<>";

% Work around a bug in SOSTOOLS/Sedumi    
varsd = vars;
varsd(end+1)=dummy;

% Problem specification
% The vector fields and domains
"<>fieldstr<>"\n"<>domstr<>"

minDeg = 1;
maxDeg = 2;
eps=0.000001;
minfeas=0.1;

for d = minDeg : maxDeg
	deg = 2*d;
    monvec = vertcat(monomials(vars,1:1:deg));

	% Work around a bug in SOSTOOLS/Sedumi    
    monvecd = monvec;
    monvecd(end+1) = dummy;

    epslb = 0*vars(1);
    for i = 1:length(vars)
        for j = 1:deg/2
            epslb = epslb + eps*vars(i)^(2*j);
        end
    end

    prog = sosprogram(varsd);

    % Template for the CLF B
    [prog,B] = sospolyvar(prog,monvecd);

    % Constraint B >= 0
    prog = sosineq(prog, B-epslb);
	"<>constrstr<>"
    opt.params.fid = 0;
    prog = sossolve(prog,opt);
    feasibility = prog.solinfo.info.feasratio;
    if feasibility >= minfeas
           Bres = sosgetsol(prog,B)
           return;
    end
end
Bres = 0;
";

sosprog=StringReplace[sosprog,{"`"->"backtick","$"->"dollar"}];
script=MATLink`MScript["CLF",sosprog, "Overwrite" -> True];
Print[sosprog];
res=MATLink`MEvaluate@script;
lines=Map[StringReplace[StringDelete[First[#],"\n" | "\r" |" "|"="],{"e-"->"*10^-", "backtick"->"`"}]&,StringCases[StringSplit[res,"Bres"][[2;;-1]],"="~~___]];
B=N[lines//ToExpression//Expand, DEFAULTPRECISION];
B=Map[RoundPolys[#,allvars]&,B];
If[B=={}, Print["No feasible solution found by SOS programming."];Return[{}]];
Return[B];
]]


GenMLF[systems_List, transitions_List,opts:OptionsPattern[]]:=Catch[Module[
{sosprog,link,allvars,vfs,vfsstr,domains,normdom,dim,
origsubs,i,fieldstr,domainsstr,domstr,locstr,constrstr,script,res,lines,B,mlfstr,solstr,tind,
tempstr,guardstr,},

Print["Attempting to generate MLFs with SOS Programming"];

allvars = Map[#[[2]]&,systems] // Flatten // DeleteDuplicates;
vfs=Map[#[[1]]&,systems];
domains=Map[ExtractPolys[#[[3]]]&,systems];
dim=Length[allvars];

Print["Domains: ",domains];
tind=Map[{#[[1]],#[[2]],ExtractPolys[#[[3]]]}&,transitions];
Print["Transitions: ",tind];

(* Open a link to Matlab *)
link=MATLink`OpenMATLAB[];

vfsstr=Map[MmaToMatlab[#]&,vfs];
fieldstr= "";
For[i=1,i<=Length[vfsstr],i++,
	fieldstr=fieldstr<>"field"<>MmaToMatlab[i]<>"="<>vfsstr[[i]]<>";\n"];

domainsstr=Map[MmaToMatlab[#]&,domains];
domstr= "";
For[i=1,i<=Length[domainsstr],i++,
	domstr=domstr<>"dom"<>MmaToMatlab[i]<>"="<>domainsstr[[i]]<>";\n"];

tempstr="
	% Guard constraint $1 to $2
	G$1to$2 = $3;
	expr$1to$2 = B$1-B$2;

	if ~isempty(G$1to$2)
	    % SOSes for each barrier in domain
        dsum=0;
	    for i=1:length(G$1to$2)
	      [prog,DP$1to$2{i}] = sossosvar(prog,monvec);
          dsum = dsum + DP$1to$2{i}*G$1to$2(i);
	    end
	    prog = sosineq(prog, expr$1to$2 - dsum);
	else
	    prog = sosineq(prog, expr$1to$2);
    end
	";

locstr="
    % Constraints for ODE $
    dB$ = 0*vars(1);
    for i = 1:length(vars)
      dB$ = dB$+diff(B$,vars(i))*field$(i);
    end

    expr$ = -dB$;
    % expr$ = -dB$-epslb;

    if ~isempty(dom$)
        for i=1:length(dom$)
          dsum=0;
          [prog,DP${i}] = sossosvar(prog,monvec);
          dsum = dsum + DP${i}*dom$(i);
        end

        prog = sosineq(prog, expr$ -dsum);
    else
        prog = sosineq(prog, expr$);
    end
	";
	
constrstr="";
For[i=1,i<=Length[vfsstr],i++,
	constrstr=constrstr<>StringReplace[locstr,{"$"->MmaToMatlab[i]}]
];
	
guardstr="";
For[i=1,i<=Length[transitions],i++,
	guardstr=guardstr
	<>StringReplace[tempstr,{"$1"->MmaToMatlab[tind[[i]][[1]]],"$2"->MmaToMatlab[tind[[i]][[2]]],"$3"->MmaToMatlab[tind[[i]][[3]]]}]
];

mlfstr="";
For[i=1,i<=Length[vfsstr],i++,
	mlfstr=mlfstr<>"
	[prog,B"<>MmaToMatlab[i]<>"] = sospolyvar(prog,monvecd);
	prog = sosineq(prog, B"<>MmaToMatlab[i]<>"-epslb);"];

solstr="";
For[i=1,i<=Length[vfsstr],i++,
	solstr=solstr<>"
		Bres = sosgetsol(prog,B"<>MmaToMatlab[i]<>")"];
			
sosprog="
% MLF

clear;
% Inputs from Mathematica
% Variables
pvar "<>StringRiffle[Map[MmaToMatlab, allvars], " "]<>";
pvar dummy;
vars = "<>MmaToMatlab[allvars]<>";

% Work around a bug in SOSTOOLS/Sedumi    
varsd = vars;
varsd(end+1)=dummy;

% Problem specification
% The vector fields and domains
"<>fieldstr<>"\n"<>domstr<>"

minDeg = 1;
maxDeg = 2;
eps=0.00001;
minfeas=0.1;

for d = minDeg : maxDeg
	deg = 2*d;
    monvec = vertcat(monomials(vars,1:1:deg));

	% Work around a bug in SOSTOOLS/Sedumi    
    monvecd = monvec;
    monvecd(end+1) = dummy;

    epslb = 0*vars(1);
    for i = 1:length(vars)
        for j = 1:deg/2
            epslb = epslb + eps*vars(i)^(2*j);
        end
    end

    prog = sosprogram(varsd);

    % Template for the MLF B"<>mlfstr<>"

	"<>constrstr<>guardstr<>"
    opt.params.fid = 0;
    prog = sossolve(prog,opt);
    feasibility = prog.solinfo.info.feasratio;
    if feasibility >= minfeas"<>solstr<>"
       return;
    end
end
Bres = 0;
";

sosprog=StringReplace[sosprog,{"`"->"backtick","$"->"dollar"}];
Print[sosprog];
script=MATLink`MScript["MLF",sosprog, "Overwrite" -> True];
res=MATLink`MEvaluate@script;
lines=Map[StringReplace[StringDelete[First[#],"\n" | "\r" |" "|"="],{"e-"->"*10^-", "backtick"->"`"}]&,StringCases[StringSplit[res,"Bres"][[2;;-1]],___~~"="~~___]];
B=N[lines//ToExpression//Expand, DEFAULTPRECISION];
B=Map[RoundPolys[#,allvars]&,B];
If[B=={}, Print["No feasible solution found by SOS programming."];Return[{}]];
Return[B]
]]


End[];
EndPackage[];
