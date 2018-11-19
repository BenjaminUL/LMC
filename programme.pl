:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).



% Predicat occur_check : return true if a variable V is contained in T.

% T n'est pas une fonction (T est soit une variable soit une constante):
occur_check(V,T) :- V == T, !.

% T est un fonction:
occur_check(V,T) :- compound(T),functor(T,_,A),occur_check_base(V,T,A).

% T est un fonction avec une arité de 1:
occur_check_base(V,T,N) :- arg(1,T,X),!,occur_check(V,X).

% T est un fonction avec un arité supérieur à 1:
occur_check_base(V,T,N) :- arg(N,T,X),occur_check(V,X);A1 is (A-1),occur_check_base(V,T,A1).




% Predicat regle: il verifie qu'une regle passée en deuxieme parametre peut s'appliquer sur une expression passée en premier paramètre.

% Listes de regles:

regle((_ ?= T),rename) :- var(T),!.

regle((_ ?= T),simplify) :- atomic(T),!.

regle((T ?= _),orient) :- nonvar(T),!.

regle((X ?= T),check) :- X \== T,occur_check(X,T),!.









