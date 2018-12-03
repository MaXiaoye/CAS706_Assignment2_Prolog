# CAS706_Assignment2_Prolog

Assignment 2
Lambda-calculus interpreter. To be done in the languages as discussed in class. 
Use the following informal description for your term language:

    var :== any string
    int :== any integer
    bool :== 'true' | 'false'
    op1 :== - | not
    op2 :== + | * | and | or | == | < | <=
    term :== var | int | bool | Apply term term | Abs var term |
        let var = term in term | op1 term | op2 term term |
        if term then term else term fi
The above represents an AST, and should be implemented as some kind of data type, and not parsed.
You should first write down the evaluation rules for your language. Since the language is untyped, your evaluator can get *stuck* - make sure to handle this properly!

Furthermore, you should include (automated) test cases for your interpreter - make sure to test higher-order functions as well as cases that get stuck and cases that work but would be rejected in a typed language. I want you to implement the (abstract) language above - you may ''rearrange'' the definitions in any equivalent way you want if it eases the implementation. In fact, the grammar above is given in a particularly "bad" way, as there are no syntactic differences between booleans and integers, even though that could be done. This is mainly done to make it even easier to write terms that do not reduce to values.

Note that beta-reduction is tricky: you have to be wary of variable capture. Direct substitution is one solution, but it is quite inefficient. Better is to use environments (explicit or implicit), or even HOAS (higher-order abstract syntax).

You can find some sample code at the textbook's web site. Unfortunately, it uses direct substitution! You can Google for "environment passing". The explanations around this interpreter in perl seem good. This is also known as deferred substition, and searching for that finds yet another interpreter with nice explanations as to what is going on.

Example: (\a.\b. b a) b should reduce to (\x. x b) (where x is a fresh variable), and NOT to (\b. b b). You should also try (\x. x y) (\x. y x) as well as (\x.\y. x y) (\x. y x) and make sure y is not captured.

-------------------------------------------------------
Actually I haven’t been familiar with Prolog style. 
I implement environment passing, high-order functions for both boolean and arithmetic expression.
Re-consult interpreter.pl and input following test cases,where R is output:
/*test cases:*/

/*let x=5 in x-1*/
122 ?- interpE([let,x,5,[-,x,1]],R).
R = 4 .

/*(\x. (x and true))false*/
123 ?- interpE([apply2,[lam,x,[and,x,true]],false],R).
R = false .

/* (\x.(x-3))2 */
124 ?- interpE([apply2,[lam,x,[-,x,3]],2],R).
R = -1 .

/* ((\x.(x+1))) (\x.(x+1))1 */
125 ?- interpE([apply2,[lam,x,[+,x,1]],[apply2,[lam,x,[+,x,1]],1]],R).
R = 3 .

/* ((\x.\y.(x+y))3)2 */
126 ?- interpE([apply2,[apply2,[lam,x,[lam,y,[+,x,y]]],3],2],R).
R = 5 .
