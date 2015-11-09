Differential Dynamic Logic
==========================

Grammar of Concrete Syntax
--------------------------

The grammar for the concrete syntax of differential dynamic logic is given below in order of ascending precedence, i.e. operators towards the beginning of the grammar bind stronger than later operators. Unary operators bind stronger than binary operators, which is why unary operators come later. Except that unary - binds like binary -.  Also ; binds stronger than ++ and & stronger than | stronger than both -> and <->. That is precedence is the following order with stronger precedence listed first and equal precedence delimited by `,`

    '   ^   *,/   -   +,-
    '  =,!=,>,>=,<,<=
    ' \forall,\exists,[],<>
        !   &    |   ->,<-   <->
        *   ;    ++
    ,
All arithmetic operators except `^` are left-associative.
All logical and program operators except `<-` and `<->` are right-associative.

==Terms==

    T ::= x | x' | num | ∙ | f(T) | f() | T^T | T*T | T/T | -T | T+T | T-T | (T)' | (T) 

Operators are left-associative, i.e. x-y-z is (x-y)-z.
Except that `T^T` is right-associative, i.e. x^4^2 is x^(4^2)

==Formulas==

    F ::= T=T | T!=T | T>=T | T>T | T<=T | T<T | p(T) | p() | C{F} | ⎵
        | !F | \forall x F | \exists x F | [P]F | <P>F 
        | F&F | F|F | F->F | F<->F | true | false | (F)' | (F)

Operators are right-associative, i.e. p()->q()->r() is p()->(q()->r()).
Except that `<->` is non-associative.

==Programs==

    P ::= a; | x:=T; | x':=T; | ?F; | {D&F} | {P}* | P P | P++P | {P}

Operators are right-associative.
Even the invisible `;` in P P is right-associative, i.e. x:=1;x:=2;x:=3; is x:=1;{x:=2;x:=3;}

==Differential Programs==

    D ::= c | x'=T | D,D

Operators are right-associative, i.e. x'=1,y'=2,z'=3 is x'=1,{y'=2,z'=3}

==Types==

It is considered an error to use the same name with different types in different places, such as in `x() -> [x:=x(x);]x()>x(x,x())`



Contrast to Theory
------------------

The grammar of the concrete syntax for programs is to be contrasted with the abstract dL grammar in theory:

    P ::= a | x:=T | x':=T | ?F | D&F | P* | P;P | P++P | (P)

with the visible `;` in P;P right-associative (and `++` being still right-associative) yet without `;` terminating atomic programs. In theory there's also no distinction between { } parentheses for programs and ( ) parentheses for terms and formulas.


References
----------

1. André Platzer. 
[A uniform substitution calculus for differential dynamic logic](http://dx.doi.org/10.1007/978-3-319-21401-6_32). 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
Extended version at [arXiv 1503.01981](http://arxiv.org/abs/1503.01981)

2. André Platzer.
[Logics of dynamical systems](http://dx.doi.org/10.1109/LICS.2012.13).
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

3. André Platzer.
[Differential dynamic logic for hybrid systems](http://dx.doi.org/10.1007/s10817-008-9103-8).
Journal of Automated Reasoning, 41(2), pages 143-189, 2008.

4. André Platzer.
[Logical Analysis of Hybrid Systems: Proving Theorems for Complex Dynamics](http://dx.doi.org/10.1007/978-3-642-14509-4).
Springer, 2010. 426 p. ISBN 978-3-642-14508-7. 