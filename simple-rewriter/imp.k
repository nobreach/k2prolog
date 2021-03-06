// Copyright (c) 2016 Nobreach Inc. All Rights Reserved.

/*  This file is part of k2Prolog.

    k2Prolog is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    k2Prolog is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with k2Prolog.  If not, see <http://www.gnu.org/licenses/>. 
*/

// This is a slighly simplified version of the standard IMP language from the K tutorials, 
// with a less fancy syntax (easier to manually translate into Prolog).
// More features can be easily added later. 

// syntax (K will generate a parser for this)
module IMP-SYNTAX

	// arithmetic expressions
	syntax Var   ::= "var" "(" Id ")"

	syntax AExp  ::= Int 
		       | Var
                       | "mul" "(" AExp "," AExp ")"
		       | "add" "(" AExp "," AExp ")"
	// statements
  	syntax Stmt  ::= "assign" "(" Var "," AExp ")"
                       | "if" "(" AExp "," Stmt "," Stmt ")"
		       | "while" "(" AExp "," Stmt ")"
                       | "seq" "(" Stmt "," Stmt ")"              
		       | "skip"
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

	// addition (heating LHS)
	rule	add(E1,E2) => E1 ~> add(HOLE,E2)			when notBool(isKResult(E1))

	// addition (cooling LHS)
	rule	(I:Int ~> add(HOLE,E2)) => add(I,E2)

	// addition (heating RHS) 
	rule	add(E1,E2) => E2 ~> add(E1,HOLE)			when notBool(isKResult(E2))

	// addition (cooling RHS) 
	rule	(I:Int ~> add(E1,HOLE)) => add(E1,I)

	// addition
  	rule 	add(I1,I2) => I1 +Int I2  

	
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

	// if (heating)
	rule 	if(E,Stmt1,Stmt2) => E ~> if(HOLE,Stmt1,Stmt2)		when notBool(isKResult(E))

	// if (cooling)
	rule	(I:Int ~> if(HOLE,Stmt1,Stmt2)) => if(I,Stmt1,Stmt2)	

	// if (true)
  	rule 	if(N:Int,S,_) => S	when (N =/=Int 0)

  	// if (false)
  	rule 	if(0,_,S) => S

	// skip
	rule	skip => .

	// while
	rule 	while (E,S) => if(E,seq(S,while(E,S)),skip)

endmodule
