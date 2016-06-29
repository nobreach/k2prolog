/* Copyright (c) 2016 Nobreach Inc. All Rights Reserved. */

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


/* -------------------------- Example runs  ---------------------------- */
/* Specialise the following goals! 
/* ----------------------------------------------------------------------*/

/*
test1(X) :- rewrite(conf(k([seq(assign(var(x),5),while(var(x),assign(var(x),add(var(x),-1))))]), state([])),X).
test2(X) :- rewrite(conf(k([assign(var(x),5)]), state([])),X).
*/

test1(Y) :- 
	X = conf(k([seq(assign(var(x),5),while(var(x),assign(var(x),add(var(x),-1))))]), state([])),
	rewrite(X,Y).

test2(Y) :- 
	X = conf(k([assign(var(x),5)]), state([])),
	rewrite(X,Y).

/* This is the only one that works for now! Just replace 'rewrite(dynamic,dynamic)' with 'dynamic(static,dynamic)' in
    imp.pl.ann, once generated. Then run 'make test' again */

test3(Y) :- 
	X = conf(k([skip]),state([])),
	rewrite(X,Y).

/* ... add more ...  */

/* -------------------- The rewriter ("K executor") -------------------- */
/* This is supposed to be language independent (but it's probably not yet
 * for this simple example. The goal is to make it so! */
/* ----------------------------------------------------------------------*/

/* --- rewrite predicate ---*/

/* rewrite(in:Configuration,out:Configuration): performs rewriting until the k cell is empty */
rewrite(conf(k([]),state(E)),conf(k([]),state(E))). /* k cell is empty, all done! */

rewrite(Cin,Cout) :- 
        rule(l(Cin),r(C)),
        rewrite(C,Cout).

/* --- builtin types/operations machinery --- */

/* The stuff here should perform the usual K operations such as reading/writing 
   values from maps, lists, sets, bags etc. Again, for this simple example this 
   is a little bit ad-hoc, but the idea will be to have a "library" of such operations
   which can be used for any K definition. All K backends must do this: Java backend maps 
   those K builltin operations to Java lists/sets etc., Maude backend maps them to Maude
   machinery etc. */

/* mapContainsKey(in:Map,in:Key) : succeeds if pair(K,_) is contained in the input map */
mapContainsKey([pair(K,_)|_],K).
mapContainsKey([_|T],K) :- mapContainsKey(T,K).

/* mapGetValueFromKey(in:Env,in:Var,out:Value): reads the value of a var from the environment */
mapGetValueFromKey([pair(K,V)|_],K,V).
mapGetValueFromKey([_|T],K,V) :- mapGetValueFromKey(T,K,V).

/* mapInsertNewKeyValuePair(in:Map,in:KeyValuePair,out:Map): insert a new key-value pair into a map */
mapInsertNewKeyValuePair(Map,KeyValuePair,[KeyValuePair|Map]). 

/* mapUpdateValueOfKey(in:Map,in:Key,in:Value,out:Map): updates the value of a key-value pair */
mapUpdateValueOfKey([pair(X,_)|T],X,V,[pair(X,V)|T]).
mapUpdateValueOfKey([_|T],X,V,UpdatedMap) :- mapUpdateValueOfKey(T,X,V,UpdatedMap).

/* todo: what else is needed? sets, bags etc... */
/* todo: use SICStus libraries? */

/* -------------------- The IMP K language definition, in Prolog -------------------- */
/* Here is a manual translation of the K definition of IMP into prolog syntax. 
   Rules are in the form rule(l(...),r(...)) for left and right hand side (but can be 
   revised, this is just a quick experiment). Configurations are in the form 
   conf(cell1(...), ..., celln(...)). Cell are supposed to contains, like in K, either
   a list, or a map, a set, bag etc. This simple example only shows list (in the k cell, 
   containing the program) and a map (the state cell). */
   
/* ----------------------------------------------------------------------*/

/* variable lookup */
rule(
  l(conf(
    k([var(X)|K]),
    state(E))),
  r(
    conf(
      k([V|K]),
      state(E)))) :- mapGetValueFromKey(E,X,V).

/* multiplication (heating LHS) */
rule(
  l(conf(
    k([mul(E1,E2)|K]),
    state(E))),
  r(
    conf(
      k([E1,mul(hole,E2)|K]),
      state(E)))) :- \+number(E1).

/* multiplication (cooling LHS) */
rule(
  l(conf(
    k([V,mul(hole,E2)|K]),
    state(E))),
  r(
    conf(
      k([mul(V,E2)|K]),
      state(E)))) :- number(V).

/* multiplication (heating RHS) */
rule(
  l(conf(
    k([mul(E1,E2)|K]),
    state(E))),
  r(
    conf(
      k([E2,mul(E1,hole)|K]),
      state(E)))) :- \+number(E2).
                                     
/* multiplication (cooling RHS) */
rule(
  l(conf(
    k([V,mul(E1,hole)|K]),
    state(E))),
  r(
    conf(
      k([mul(E1,V)|K]),
      state(E)))) :- number(V).

/* multiplication */
rule(
  l(conf(
    k([mul(V1,V2)|K]),
    state(E))),
  r(
    conf(
      k([V|K]),
      state(E)))) :- number(V1), number(V2),  V is V1 * V2.




/* addition (heating LHS) */
rule(
  l(conf(
    k([add(E1,E2)|K]),
    state(E))),
  r(
    conf(
      k([E1,add(hole,E2)|K]),
      state(E)))) :- \+number(E1).

/* addition (cooling LHS) */
rule(
  l(conf(
    k([V,add(hole,E2)|K]),
    state(E))),
  r(
    conf(
      k([add(V,E2)|K]),
      state(E)))) :- number(V).

/* addition (heating RHS) */
rule(
  l(conf(
    k([add(E1,E2)|K]),
    state(E))),
  r(
    conf(
      k([E2,add(E1,hole)|K]),
      state(E)))) :- \+number(E2).
                                     
/* addition (cooling RHS) */
rule(
  l(conf(
    k([V,add(E1,hole)|K]),
    state(E))),
  r(
    conf(
      k([add(E1,V)|K]),
      state(E)))) :- number(V).

/* addition */
rule(
  l(conf(
    k([add(V1,V2)|K]),
    state(E))),
  r(
    conf(
      k([V|K]),
      state(E)))) :- number(V1), number(V2),  V is V1 + V2.









/* assign (heating) */
rule(
  l(conf(
    k([assign(var(X),Exp)|K]),
    state(E))),
  r(
    conf(
      k([Exp,assign(var(X),hole)|K]),
      state(E)))) :- \+number(Exp).

/* assign (cooling) */
rule(
  l(conf(
    k([V,assign(var(X),hole)|K]),
    state(E))),
  r(
    conf(
      k([assign(var(X),V)|K]),
      state(E)))) :- number(V).

/* assign (existing variable) */
rule(
  l(conf(
    k([assign(var(X),V)|K]),
    state(E))),
  r(
    conf(
      k(K),
      state(E1)))) :- number(V), mapContainsKey(E,X), mapUpdateValueOfKey(E,X,V,E1).

/* assign (new variable) */
rule(
  l(conf(
    k([assign(var(X),V)|K]),
    state(E))),
  r(
    conf(
      k(K),
      state(E1)))) :- number(V), \+mapContainsKey(E,X), mapInsertNewKeyValuePair(E,pair(X,V),E1).

/* seq */ 
rule(
  l(conf(
    k([seq(Stmt1,Stmt2)|K]),
    state(E))),
  r(
    conf(
      k([Stmt1,Stmt2|K]),
      state(E)))).

/* if (heating) */
rule(
  l(conf(
    k([if(Exp,Stmt1,Stmt2)|K]),
    state(E))),
  r(
    conf(
      k([Exp,if(hole,Stmt1,Stmt2)|K]),
      state(E)))) :- \+number(Exp).

/* if (cooling) */
rule(
  l(conf(
    k([V,if(hole,Stmt1,Stmt2)|K]),
    state(E))),
  r(
    conf(
      k([if(V,Stmt1,Stmt2)|K]),
      state(E)))) :- number(V).

/* if (true) */
rule(
  l(conf(
    k([if(V,Stmt,_)|K]),
    state(E))),
  r(
    conf(
      k([Stmt|K]),
      state(E)))) :- number(V), V \= 0.

/* if (false) */
rule(
  l(conf(
    k([if(V,_,Stmt)|K]),
    state(E))),
  r(
    conf(
      k([Stmt|K]),
      state(E)))) :- number(V), V = 0.

/* skip */
rule(
  l(conf(
    k([skip|K]),
    state(E))),
  r(
    conf(
      k(K),
      state(E)))).

/* while */
rule(
  l(conf(
    k([while(Exp,Stmt)|K]),
    state(E))),
  r(
    conf(
      k([if(Exp,seq(Stmt,while(Exp,Stmt)),skip)|K]),
      state(E)))).


