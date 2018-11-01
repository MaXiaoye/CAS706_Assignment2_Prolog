
/*arithmetic*/
calc1([Op,Exp1,Exp2],R) :- Op = '+',
					 R is (Exp1+Exp2).
calc1([Op,Exp1,Exp2],R) :- Op = '-',
					 R is (Exp1-Exp2).
calc1([Op,Exp1,Exp2],R) :- Op = '*',
					 R is (Exp1*Exp2).
calc1([Op,Exp1,Exp2],R) :- Op = '/',
					 R is (Exp1/Exp2).

/*bool*/
bool(true).
bool(false).
boolExp([T,X,Y]) :- T = 'and';T = 'or';T='not'.

/*Not*/
minus([T,X],R) :- T = 'not',
				X = true,
				R = false.
				
minus([T,X],R) :- T = 'not',
				X = false,
				R = true.			

/*And,Or*/
and([T,X,Y],R) :- T = 'and',
				X = true,
				Y = true,
				R = true.
				
and([T,X,Y],R) :- T = 'and',
				X = false,
				R = false.
				
and([T,X,Y],R) :- T = 'and',
				Y = false,
				R = false.
												
or([T,X,Y],R) :- T = 'or', 
				X = true,
				R = true.
or([T,X,Y],R) :- T = 'or', 
				Y = true,
				R = true.
or([T,X,Y],R) :- T = 'or', 
				X = false,
				Y = false,
				R = false.				

/*Equal*/
equal([X,Y],R) :- X == Y,
				R = true.

equal([X,Y],R) :- X \== Y,
				R = false.
				
/*Less than*/
lt([X,Y],R) :- X < Y,
			R = true.
lt([X,Y],R) :- X >= Y,
			R = false.

/*Less than or equal*/
lte([X,Y],R) :- X =< Y,
			R = true.
			
lte([X,Y],R) :- X > Y,
			R = false.
			
/*if then else*/
if([X,Y,Z],R) :- X = true,
				R = Y.
if([X,Y,Z],R) :- X = false,
				R = Z.

/*let*/
let([T,Exp1,Exp2,Exp3]) :- T = 'let',
						vari(Exp1),				
						expt(Exp3).
			
/*Body of lambda*/																
expt([Op,_,_]) :- Op = '+'.
expt([Op,_,_]) :- Op = '-'.
expt([Op,_,_]) :- Op = '*'.
expt([Op,_,_]) :- Op = '/'.
expt([T,X,Y]) :- boolExp([T,X,Y]).
expt([X,Y,Z]) :- lambda([X,Y,Z]).

/*Assume x,y,z are variables*/
vari(X) :- X == x.
vari(X) :- X == y.
vari(X) :- X == z.

/*Assume integers and 'a' 'b' 'c' are values.*/
val(X) :- integer(X).
val(X) :- X == a.
val(X) :- X == b.
val(X) :- X == c.

/* Boolean */
bool(X) :- X == true.
bool(X) :- X == false.

/*definition of lambda*/
/*lambda([l,x,[+,x,1]])*/
/*lambda([l,x,[l,y,[+,x,y]]])*/
lambda([X,Var,Body]) :- X = 'lam', 
					vari(Var),
					expt(Body).					

/*Store Var and Val in List as [Var1,Val1,Var2,Val2] such that value stays next to variable.*/
/*Find Var firstly then return next element which is the value.*/
lookup(Key,Env,Value) :- find(Key,Env,Rest),
						findHead(Rest,Value).

/*Find Var and return the rest list which is all elements in the right of Var's location*/
find(Key,[Key|Rest],Rest).
find(Key,[DisregardHead|Tail],Rest) :- find(Key,Tail,Rest).

/*Take rest list as input and return the head element which is the value.*/
findHead([Next|Rest],Next).  																

/*Extend env by just appending Var and Val.*/
extendEnv(X,V,Env,R) :- append(Env,[X,V],R).


/*Eval function*/
/*deal with Var, return its value.*/						
interp(Exp,Env,R) :- vari(Exp),
					lookup(Exp,Env,R).
/*deal with Val,just return the value.*/
interp(Exp,Env,R) :- val(Exp),
					R = Exp.
interp(Exp,Env,R) :- bool(Exp),
					R = Exp.
/*deal with lambda, return a closure containing lambda and env.*/					
interp(Exp,Env,R) :- lambda(Exp),
					R = [Exp,Env].

/*deal with let.*/					
interp([T,Exp1,Exp2,Exp3],Env,R) :- let([T,Exp1,Exp2,Exp3]),
								interp(Exp2,[],R1),
								extendEnv(Exp1,R1,Env,EnvN),
								interp(Exp3,EnvN,R).
					
/*recusively deal with arithmetic and bool expression.*/
interp([Op,A1,A2],Env,R) :- interp(A1,Env,R1),
							interp(A2,Env,R2),
							calc1([Op,R1,R2],R).

/*deal with bool expression*/
interp([T,Exp1,Exp2],Env,R) :- boolExp([T,Exp1,Exp2]),
								interp(Exp1,Env,R1),
								interp(Exp2,Env,R2),
								or([T,R1,R2],R).
interp([T,Exp1,Exp2],Env,R) :- boolExp([T,Exp1,Exp2]),
								interp(Exp1,Env,R1),
								interp(Exp2,Env,R2),
								and([T,R1,R2],R).
									
interp([T,Exp1],Env,R) :- interp(Exp1,Env,R1), 
						minus([T,R1],R).

/*recusively deal with applicaion (Apply2) and store Val=Value in env.*/
interp([apply1,Exp1,Exp2],Env,R) :- interp(Exp1,Env,R1),
									interp(Exp2,Env,R2),
									string_concat(R1,' ',R3),
									string_concat(R3,R2,R).
																
interp([apply2,Exp1,Exp2],Env,R) :- interp(Exp1,Env,R1),
								R1 = [[lam,Var,Body],Env1],
								interp(Exp2,[],R2),
								extendEnv(Var,R2,Env1,Env2),
								interp(Body,Env2,R).
/*User interface, create an empty env as initial env*/
interpE(Exp,R) :- interp(Exp,[],R1),
				R1 = [[lam,Var,Body],Env1],
				interp(Body,Env1,R2),
				string_concat('lam ',Var,R3),
				string_concat(R3,R2,R).
				
interpE(Exp,R) :- interp(Exp,[],R).								

/*test cases:*/

/*let x=5 in x-1*/
/*interpE([let,x,5,[-,x,1]],R).*/

/*(\x. (x and true))false*/
/*interpE([apply2,[lam,x,[and,x,true]],false],R).*/

/* (\x.(x-3))2 */
/*interpE([apply2,[lam,x,[-,x,3]],2],R).*/

/* ((\x.(x+1))) (\x.(x+1))1 */
/*interpE([apply2,[lam,x,[+,x,1]],[apply2,[lam,x,[+,x,1]],1]],R).*/

/* ((\x.\y.(x+y))3)2 */
/*interpE([apply2,[apply2,[lam,x,[lam,y,[+,x,y]]],3],2],R).*/ 					 												