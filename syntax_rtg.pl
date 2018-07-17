% please ?- pack_install(rtg).
:- use_module(library(rtg)).
:- op(1200,xfx,⊦), op(650,xfy,[==>,=>]).

% fol

syntax(maplist(_)). syntax(call(_)).
[T]         ::= maplist(T).
ident       ::= atom.
term        ::= ident
              | [ident]->term
              | term*[term].
formula     ::= ident*[term]
              | top
              | bottom
              | and(formula,formula)
              | or(formula,formula)
              | formula==>formula
              | forall(ident,formula)
              | exist(ident,formula).
predicate   ::= [ident]=>predicate
              | formula.
typeForm(T) ::= prop
              | call(T)
              | ident*[typeForm(T)]
              | typeForm(T)->typeForm(T).
syntax(identT). identT(T) :- T \= prop,ident(T).
type        ::= typeForm(identT).

% lk
syntax(integer).
rule        ::= i | cut(formula)
              | andL1 | andL2 | andR
              | orL | orR1 | orR2
              | impL | impR | bottomL | topR
              | forallL(term) | forallR(ident)
              | existL(ident) | existR(term)
              | wL | wR | cL | cR
              | pL(integer) | pR(integer).
% claire

thmIndex    ::= atom.
pair        ::= ident:predicate.
pairs       ::= [pair].
ipairs      ::= (ident,pairs).
argument    ::= []
              | p([predicate])
              | t([term])
              | n(ident:type)
              | i([ipairs]).
command     ::= apply([rule])
              | use(thmIndex,pairs)
              | inst(ident,predicate)
              | noApply(rule)
              | ident*argument.
decl        ::= theorem(thmIndex,formula,proof([command]))
              | axiom(thmIndex,formula)
              | import(atom)
              | printProof
              | constant(ident,type)
              | plFile(atom)
              | ident*[argument].
laire       ::= [decl].

dependFile1(import(File)) :- check(File).
dependFile1(_).
dependFile(Ds) :- maplist(dependFile1,Ds).

check(File):-
  catch((
    read_file_to_terms(File,Ds,[]),
    (laire(Ds),format('syntax ok ~w\n',[File]),dependFile(Ds);writeln('syntax error'),halt(1))
  ),Err,(writeln(Err),halt(2))).

:- current_prolog_flag(argv,[File|_]), check(File).
:- halt.
