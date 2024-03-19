=Differential Dynamic Logic=

==Grammar of Concrete Syntax==

The grammar for the concrete syntax of differential dynamic logic is given below in order of ascending precedence, i.e. operators towards the beginning of the grammar bind stronger than later operators. Unary operators bind stronger than binary operators, which is why unary operators come later. Except that unary `-` binds like binary `-`.  Also ; binds stronger than `++` and `&` stronger than `|` stronger than both `->` and `<->`. That is precedence is the following order with stronger precedence listed first and equal precedence delimited by `,`

    '   ^   *,/   -   +,-
       =,!=,>,>=,<,<=
    ' \forall,\exists,[],<>
        !   &    |   ->,<-   <->
        *   ;    ++

All arithmetic operators except `^` and pairs are left-associative.
All logical and program operators except `<-` and `<->` are right-associative.

===Terms===

    T ::= x | x' | num | ∙ | f(T) | f() | T^T | T*T | T/T | -T | T+T | T-T | (T)' | (T,T) | (T) 

Arithmetic operators are left-associative, i.e., `x-y-z` is `(x-y)-z`.
Except that `T^T` and pairs are right-associative, i.e., `x^4^2` is `x^(4^2)`.

===Formulas===

    F ::= T=T | T!=T | T>=T | T>T | T<=T | T<T | p(T) | p() | C{F} | ⎵
        | !F | \forall x F | \exists x F | [P]F | <P>F 
        | F&F | F|F | F->F | F<->F | true | false | (F)' | (F)

Logical operators are right-associative, i.e., `p()->q()->r()` is `p()->(q()->r())`.
Except that `<->` is non-associative and `<-` is left-associative.

===Programs===

    P ::= a; | x:=T; | x':=T; | ?F; | {D&F} | {P}* | P P | P++P | {P} | if (F) {P} else {P} | if (F) {P}

Operators are right-associative, i.e., `x:=1;++x:=2;++x:=3;` is `x:=1;++{x:=2;++x:=3;}`.
Even the invisible `;` in `P P` is right-associative, i.e. `x:=1;x:=2;x:=3;` is `x:=1;{x:=2;x:=3;}`

===Differential Programs===

    D ::= c | x'=T | D,D

Program operators are right-associative, i.e., x'=1,y'=2,z'=3 is x'=1,{y'=2,z'=3}

===Types===

It is considered an error to use the same name with different types in different places, such as in `x() -> [x:=x(x);]x()>x(x,x())`.
It is considered an error to use divisions `e/d` without a nonzero divisor `d`.


==Contrast to Theory==

The grammar of the concrete syntax for programs is to be contrasted with the abstract dL grammar in theory:

    P ::= a | x:=T | x':=T | ?F | D&F | P* | P;P | P++P | (P)

with the visible `;` in `P;P` right-associative (and `++` being still right-associative) yet without `;` terminating atomic programs. In theory there's also no distinction between `{ }` parentheses for programs and `( )` parentheses for terms and formulas.


==LL-Grammar==

The above grammars use precedences. The transformation to an LL-grammar introduces auxiliary nonterminal symbols (Terms T are split into S for summands, F for factors, P for powers) to represent operator precedence and associativity.

If unary minus were to bind strong (which incorrectly reads `-2^4` as `(-2)^4)`, the LL grammar would simply be:

    T ::= T+S | T-S | S
    S ::= S*F | S/F | F
    F ::= P^F | P
    P ::= -P | x | x' | num | f(T,...,T) | (T)' | (T)

If unary minus binds strong but weaker than `^` (where `-2^4` is `-(2^4)` but reads negation `-x*y` incorrectly as the nonmonomial `(-x)*y` and different from the subtraction `0-x*y` which is `0-(x*y)`), then this reads unary `-` multiplicatively like `(-1)*`, and the LL grammar would be:

    T ::= T+S | T-S | S
    S ::= S*F | S/F | -F | F
    F ::= P^F | P^-F | P
    P ::= x | x' | num | f(T,...,T) | (T)' | (T)

To make unary minus bind like binary subtraction (reading `-x*y` correctly as negated monomial `-(x*y)` and reading it like subtraction `0-x*y` as `0-(x*y)` and reading `-2*x` consistently as `-(2*x)` instead of `(-2)*x`), then this reads unary `-` additively like `0-`, and the LL grammar is:

    T ::= T+S | T-S | -S | S
    S ::= S*F | S*-F | S/F | S/-F | F
    F ::= P^F | P^-F | P
    P ::= x | x' | num | f(T,...,T) | (T)' | (T)

=References=

1. André Platzer.
[A complete uniform substitution calculus for differential dynamic logic](https://doi.org/10.1007/s10817-016-9385-1).
Journal of Automated Reasoning, 59(2), pages 219-265, 2017.

2. André Platzer.
[Logics of dynamical systems](https://doi.org/10.1109/LICS.2012.13).
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

3. André Platzer.
[Logical Foundations of Cyber-Physical Systems](https://doi.org/10.1007/978-3-319-63588-0).
Springer, 2018. 659 pages. ISBN 978-3-319-63587-3.

4. André Platzer.
[Differential dynamic logic for hybrid systems](https://doi.org/10.1007/s10817-008-9103-8).
Journal of Automated Reasoning, 41(2), pages 143-189, 2008.

5. André Platzer.
[Logical Analysis of Hybrid Systems: Proving Theorems for Complex Dynamics](https://doi.org/10.1007/978-3-642-14509-4).
Springer, 2010. 426 pages. ISBN 978-3-642-14508-7.
