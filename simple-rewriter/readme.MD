This is a first attempt in writing down a K definition in Prolog syntax (by trying to preserve the shape of the rules) 
and executing it in prolog. Execution in prolog is done by a couple of extra predicates (the executor).

# K definition of the IMP language

The original K definition is in the file `imp.k`, for comparison. I'll keep it in synch with the prolog translation.
It can be compiled in K with `kompile imp.k`; given a program, say `hello-world.imp`, this can be executed with `krun hello-world.imp`.

# The Prolog translation of the K rules

The prolog file contains both the "K executor" part and the language definition to be executed ("IMP"). This should clearly be spltted later on. 

The original K rules for IMP are manually translated into prolog in a straigtforward way, but they are more verbose. 
Actually, this resembles the translation to Maude that K itself used to do; basically, the stuff that is kept implicit in the fancy K syntax is made explicit (more on this later id needed).
Apart from this, the rules are basically the same.

# The "K executor" written in prolog

The executor consists of two parts 
* the `rewrite` predicate, which tell prolog to keep looking for rules to apply until done (i.e. the k cell is empty) or stuck (nb: now is shows a result only if the computation succeds i.e. if the k cell remains empty. If it gets stuck prolog just says "no". Should fix this.) 
* prolog implementations of the K data types and their operations: maps, lists, bags sets etc. I have written a couple of predicates for now, but what about using SICStus library for that?

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

`X = conf(k([]),state([pair(x,36)]))`

## Sequencing

As the name says...

### Intended program

```
x := 3;
z := 2;
```

### AST (the syntax we actually use)

```
seq(
 assign(x,3),
 assign(z,2))
```
### Query

`rewrite(conf(k([seq(assign(var(x),6),assign(var(z),2))]),state([])),X).`

### Result

` X = conf(k([]),state([pair(z,2),pair(x,6)]))`

## Nested arithmetic expressions

Testing heating/cooling rules for multiplication 

### Intended program

`x = 6 * (3 * (2 * 3));`

### AST (the syntax we actually use)

`assign(var(x),mul(6,mul(3,mul(2,3)))`

### Query

`rewrite(conf(k([assign(var(x),mul(6,mul(3,mul(2,3))))]), state([])),X).`

### Result

`X = conf(k([]),state([pair(x,108)]))`

## Conditionals ("if")

Since we only have numbers in IMP, conditional here is like in C, i.e. "0" is false and "not 0" is true.  

### Intended program

```
if (3 * 2) then 
  x := 1; 
else 
  x = 8;
```

### AST (the syntax we actually use)

```
if(
  mul(3,2),   
  assign(var(x),1),   
  assign(var(x),8))
```

### Query

`rewrite(conf(k([if(mul(3,2),assign(var(x),1),assign(var(x),8))]), state([])),X).`

### Result

`X = conf(k([]),state([pair(x,1)]))`

## Variable lookup


### Intended program

```
x := 5; 
y := x;
```

### AST (the syntax we actually use)

```
seq(
  assign(
    var(x),5),
    assign(
      var(y),
      var(x)))
```

### Query

`rewrite(conf(k([seq(assign(var(x),5),assign(var(y),var(x)))]), state([])),X).`

### Result

`X = conf(k([]),state([pair(y,5),pair(x,5)]))`

## While loop

Last example for now.

### Intended program
```
x := 5; 
while (x) do 
    x := x - 1;
```

### AST (the syntax we actually use)

```
seq(  
  assign(var(x),5),  
  while(
    var(x),
    assign(var(x),add(var(x),-1))))
```

### Query

`rewrite(conf(k([seq(assign(var(x),5),while(var(x),assign(var(x),add(var(x),-1))))]),state([]) ),X).`

### Result

`X = conf(k([]),state([pair(x,0)]))`




# Making it nicer

Once we hape a program `P`, we want to actually build the query 

`rewrite(conf(k([P]),state([])),X).`

This is of course assuming we want to start from an empty state (which is almost never the case in "real" language definitions including KPHP). But that's a start! 

What about having `P` in a file which can be loaded? 

# Next

## K executor
* separate executor, language definition and program to be executed (see above)
* make the executor more language agnostic (polish, cleanup, generalise) 
* implement more K builtin data types (maps, lists, sets etc.). Use SICStus libraries?!

## automatic translation of K defs?
* we don't want to do it manually :) 
