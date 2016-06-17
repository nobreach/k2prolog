/* Copyright (c) 2016 Nobreach Inc. All Rights Reserved. */

/* -------------------- The rewriter ("K executor") -------------------- */
/* This is supposed to be language independent (but it's probably not yet
 *  for this simple example. The goal is to make it so! */
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
   machinery etc. 

   Question: I suppose SICStus has excellent libraries for lists/maps etc. Shall we use that? 
   Will LOGEN be happy? 

   For now, a couple of handmade (and probably buggy) ones. */

/* readEnv(in:Env,in:Var,out:Value): reads the value of a var from the environment */
readEnv([],_,bot).
readEnv([pair(X,V)|_],X,V).
readEnv([_|Env],X,V) :- readEnv(Env,X,V).

/* updateEnv(-Env,-Pair,+Env): updates an environment */

updateEnv(E,Pair,[Pair|E]). /* dummy */

/* fixme! 
updateEnv([pair(X,_) | T],pair(X,V),[pair(X,V) | T]).
updateEnv([AnotherPair | T],Pair,[AnotherPair | Env]) :- 
        AnotherPair \= Pair, 
        updateEnv(T,Pair,Env).
updateEnv([],Elem,[Elem]).
*/


/* -------------------- The IMP K language definition, in Prolog -------------------- */
/* Here is a manual translation of the K definition of IMP into prolog syntax. 
   Rules are in the form rule(l(...),r(...)) for left and right hand side (but can be 
   revised, this is just a quick experiment). Configurations are in the form 
   conf(cell1(...), ..., celln(...)). Cell are supposed to contains, like in K, either
   a list, or a map, a set, bag etc. This simple example only shows list (in the k cell, 
   containing the program) and a map (the state cell). 

   Ideally, this part should come mechanically, either by parsing a standard K definition
   ourselves or by using the K-Prolog kompile backend in order to output something
   similar for us. 

   For execution, the program to be executed must be injected, as in K, into the k 
   cell, as it's only element (the k cell is a list!). 
   This should be done automatically (but is done manually here.  
   
   EXAMPLES
   
   - program 1:
        assign(x,3)
   
   - query: 
        rewrite(conf(k([assign(x,6)]), state([]) ),X).
   
   -result: 
        X = conf(k([]),state([pair(x,6)])) 
        
   (k cell is empty, i.e. pgm has been executed, and state maps x to 6!) 
        
   - program 2:
        seq(
          assign(x,3),
          assign(z,2)
        )
        
   - query: 
        rewrite(conf(k([seq(assign(x,6),assign(z,2))]),state([])),X).
   
   - result:
         X = conf(k([]),state([pair(z,2),pair(x,6)]))
         
   (same as above. notice the sequencing of 2 instructions) */
/* ----------------------------------------------------------------------*/

/* variable lookup */
rule(
  l(conf(
    k([var(X)|K]),
    state(E))),
  r(
    conf(
      k([V|K]),
      state(E)))) :- readEnv(E,X,V).

/* multiplication */
rule(
  l(conf(
    k([mul(X,Y)|K]),
    state(E))),
  r(
    conf(
      k([V|K]),
      state(E)))) :- V is X * Y.

/* addition */
rule(
  l(conf(
    k([add(X,Y)|K]),
    state(E))),
  r(
    conf(
      k([V|K]),
      state(E)))) :- V is X + Y.

/* assign */
rule(
  l(conf(
    k([assign(X,V)|K]),
    state(E))),
  r(
    conf(
      k(K),
      state(E1)))) :- updateEnv(E,pair(X,V),E1).

/* seq */ 
rule(
  l(conf(
    k([seq(Stmt1,Stmt2)|K]),
    state(E))),
  r(
    conf(
      k([Stmt1,Stmt2|K]),
      state(E)))).

/* if (TODO) */
/* heating/cooling rules (TODO) */