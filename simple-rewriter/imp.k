// Copyright (c) 2016 Nobreach Inc. All Rights Reserved.

// This is a slighly simplified version of the standard IMP language from the K tutorials, 
// with a less fancy syntax (easier to manually translate into Prolog).
// More features can be easily added later. 

// syntax (K will generate a parser for this)
module IMP-SYNTAX
	// todo: remove [strict] tags and write explicit heating/cooling rules instead
	// (as done already for variable assignment).

	// arithmetic expressions
	
	syntax Var   ::= "var" "(" Id ")"

	syntax AExp  ::= Int 
		       | Var
                       | "mul" "(" AExp "," AExp ")"
	// statements
  	syntax Stmt  ::= "assign" "(" Var "," AExp ")"
                       | "if" "(" AExp "," Stmt "," Stmt ")"    [strict(1)]
                       | "seq" "(" Stmt "," Stmt ")"              

// Note: the [strict] tags cause K to auto generate "heating" and "cooling" rules, 
// but nothing prevent us to writing them manually. I'll provide a demonstration of that. 

endmodule

// semantics
module IMP
	imports IMP-SYNTAX
	
	// numbers are considered "answers"
  	syntax KResult ::= Int
	
	// configuration consists of a program (AST) and a state, i.e. a map State: Id -> Int 
	// (but notice that K doesn't force that, you can put anything in a map actually). 
  	configuration 
	<T>
		<k> $PGM:Stmt </k>	// pgm to be computed is a statement
                <state> .Map </state>
 	</T>
	
	// variable lookup
	rule 	<k> var(X:Id) => I ...</k> 
		<state>... X |-> I ...</state>

	// multiplication (heating LHS)
	rule	mul(E1,E2) => E1 ~> mul(HOLE,E2)			when notBool(isKResult(E1))

	// multiplication (cooling LHS)
	rule	(I:Int ~> mul(HOLE,E2)) => mul(I,E2)

	// multiplication (heating RHS) 
	rule	mul(E1,E2) => E2 ~> mul(E1,HOLE)			when notBool(isKResult(E2))

	// multiplication (cooling RHS) 
	rule	(I:Int ~> mul(E1,HOLE)) => mul(E1,I)

	// multiplication
  	rule 	mul(I1,I2) => I1 *Int I2  
	
	// assignment (heating)
	rule	assign(var(X),E:AExp) => E ~> assign(var(X),HOLE)	when notBool(isKResult(E))

	// assignment (cooling)
	rule	(I:Int ~> assign(var(X),HOLE)) => assign(var(X),I)

	// assignment (existing variable)
  	rule 	<k> assign(var(X), I:Int) => . ...</k> 
		<state>... X |-> (_ => I) ...</state>

	// assignment (fresh variable)
  	rule 	<k> assign(var(X),I:Int) => . ...</k>
		<state> State:Map => State[X <- I] </state>
		when notBool(X in keys(State))
	// sequence
  	rule 	seq(S1:Stmt,S2:Stmt) => S1 ~> S2  [structural]
	// if (true case i.e arg is not zero, C-like)
  	rule 	if(N:Int,S,_) => S	when (N =/=Int 0)
  	// if (false case, i.e. arg is zero)
  	rule 	if(0,_,S) => S

endmodule
