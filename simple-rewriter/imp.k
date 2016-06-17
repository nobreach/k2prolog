// Copyright (c) 2016 Nobreach Inc. All Rights Reserved.

// This is a slighly simplified version of the standard IMP language from the K tutorials, 
// with a less fancy syntax (easier to manually translate into Prolog).
// More features can be easily added later. 

// syntax (K will generate a parser for this)
module IMP-SYNTAX
	// arithmetic expressions
	syntax AExp  ::= Int 
		       | "var" "(" Id ")"
                       | "mul" "(" AExp "," AExp ")"            [strict]
                       | "add" "(" AExp "," AExp ")"            [strict]
	// statements
  	syntax Stmt  ::= "assign" "(" Id "," AExp ")"   	[strict(2)]
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
	// multiplication
  	rule 	mul(I1,I2) => I1 *Int I2  
	// addition
  	rule 	add(I1,I2) => I1 +Int I2
	// assignment (existing variable)
  	rule 	<k> assign(X, I:Int) => . ...</k> 
		<state>... X |-> (_ => I) ...</state>
	// assignment (fresh variable)
  	rule 	<k> assign(X,I:Int) => . ...</k>
		<state> State:Map => State[X <- I] </state>
		when notBool(X in keys(State))
	// sequence
  	rule 	seq(S1:Stmt,S2:Stmt) => S1 ~> S2  [structural]
	// if (true case i.e arg is not zero, C-like)
  	rule 	if(N:Int,S,_) => S	when (N =/=Int 0)
  	// if (false case, i.e. arg is zero)
  	rule 	if(0,_,S) => S

endmodule
