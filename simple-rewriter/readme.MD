This is a first, very simple attempt in writing down a K definition is Prolog syntax (by trying to preserve the shape of the rules) 
and executing it in prolog. 

The original K definition is included for comparison (and kept in synch with the prolog one).

The prolog file contains both the "K executor" part and the language definition to be executed ("IMP"). This should clearly be spltted later on. 
The "K executor" basically consists of two things 
* the "rewrite" predicate, which tell prolog to keep looking for rules to apply until done or stuck (like in K) 
* prolog implementations of the K data types and their operations: maps, lists, bags sets etc.  

I (Daniele) will provide more detailed explanations here, but for now please see the prolog file, which is heavily commented! 
# Examples

## Simple assignment

Just assign a numeric value to a variable

### Intended program

`x := 3;`

### AST (the syntax we actually use)

`assign(x,3)`

### Query

`rewrite(conf(k([assign(var(x),6)]), state([]) ),X).`

### Result

`X = conf(k([]),state([pair(x,6)]))`

## Assignment of complex expression

This requires evaluation of subexpressions using K's heating & cooling mechanism. 

### Intended program

`x := 6 * 6;`

### AST (the syntax we actually use)

`assign(x,mul(6,6))`

### Query

`rewrite(conf(k([assign(var(x),mul(6,6))]), state([]) ),X).`

### Result

## Sequencing

As the name says...

### Intended program

`x := 3;
 z := 2;`

### AST (the syntax we actually use)

` seq(
          assign(x,3),
          assign(z,2)
        )`

### Query

`rewrite(conf(k([seq(assign(var(x),6),assign(var(z),2))]),state([])),X).`

### Result

` X = conf(k([]),state([pair(z,2),pair(x,6)]))`

# Making it nicer

Once we hape a program `P`, we want to actually build the query 

`rewrite(conf(k([P]),state([])),X).`

This is of course assuming we want to start from an empty state (which is almost never the case in "real" language definitions including KPHP). But that's a start! 

What about having `P` in a file which can be loaded? 

# TODO
## language example
* add remaining "heating" and "cooling" rules (keep in synch K and prolog!) 
* add rules for conditional (including heating/cooling)

## K executor
* separate executor, language definition and program to be executed (see above)
* make the executor more language agnostic (polish, cleanup, generalise) 
* implement property K builtin data types (maps, lists, sets etc.). Use SICStus libraries?!

## automatic translation of K defs?
* we don't want to do it manually :) 
