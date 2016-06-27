# k2prolog

 Given a K semantics for a language L together with an L-program P, we aim to execute P, according to the semantics of L, using an executor/engine written in Prolog.
 
 We still have to properly understand in which format we want our prolog executor to accept K definitions, but ideally we'd like to keep the format of the rules as close as possible to their original K counterpart.
 Would be nice to use the K tools to output the desired format of the rules. We could develop in K, and use its debugging features etc. before "exporting" to Prolog. 
 
 For now, [here is an experiment](https://github.com/nobreach/k2prolog/tree/master/simple-rewriter) in manually translating the K definition of IMP into Prolog terms, together with a very very simple executor in Prolog.
 
 Our final goal is translation of program P from L to Prolog, which we aim to achieve via partial evaluation
* specialising the "K executor written in Prolog" w.r.t. a specific the K definition will give us an equivalent semantics/interpreter written in Prolog. 
* Specialising this w.r.t. a program will produce an equivalent version of the program written in Prolog. 

Note, however, that the "Prolog backend" may be integrated in the K tool as well (without all of the partial evaluation stuff). 

Here's a (probably out-of date diagram):

![k2prolog](k2prolog.png)
