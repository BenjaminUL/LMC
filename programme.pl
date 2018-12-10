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

% Question 1

% Predicat occur_check : return true if a variable V is contained in T.

% T n'est pas une fonction (T est soit une variable soit une constante):
occur_check(V,T) :- V == T, !.

% T est un fonction:
occur_check(V,T) :- compound(T),functor(T,_,A),occur_check_base(V,T,A).

% T est un fonction avec une arité de 1:
occur_check_base(V,T,1) :- arg(1,T,X),!,occur_check(V,X).

% T est un fonction avec un arité supérieur à 1:
occur_check_base(V,T,N) :- arg(N,T,X),occur_check(V,X);N1 is (N-1),occur_check_base(V,T,N1).

% Predicat regle: il verifie qu'une regle passée en deuxieme parametre peut s'appliquer sur une expression passée en premier paramètre.

% Listes des predicats regles:

regle((_ ?= T),rename) :- var(T),!.

regle((_ ?= T),simplify) :- atomic(T),!.

regle((X ?= T),check) :- X \== T, var(X), occur_check(X,T),!.

regle((X ?= T),expand) :- var(X), compound(T), not(occur_check(X,T)), !.

regle((X ?= T),decompose) :- compound(X), compound(T), functor(X,A1,N1), functor(T,A2,N2),A1==A2,N1==N2,!.

regle((X ?= T),clash) :- compound(X), compound(T), functor(X,A1,_), functor(T,A2,_), A1 \== A2, !.

regle((X ?= T),clash) :- compound(X), compound(T), functor(X,_,N1), functor(T,_,N2), N1 \== N2, !.

regle((T ?= _),orient) :- nonvar(T),!.


% prédicat qui vont servir pour creer les prédicats réduits

append(X,[],X).
append(Y,[X|P],[X|Q]) :- append(Y,P,Q).

% ajout du prédicat substitution pour les prédicats réduits
% on remplace premier parametre par deuxieme parametre dans équation du troisieme parametre
% et on met le resultat dans le quatrieme parametre

substitution(_,_,[],[]) :- !.

substitution(X,T,[A ?= B|P],[A2 ?= B2|P2]) :- substitution_terme(X,T,A,A2),substitution_terme(X,T,B,B2),substitution(X,T,P,P2).

substitution_terme(X,T,A,T):- A == X,not(compound(A)),!.

substitution_terme(X,_,A,A):- A \== X,not(compound(A)),!.

substitution_terme(X,T,A,Q):- functor(A,_,N),compound(A),substitution_funct(X,T,A,N,Q),!.

% Liste predicats pour subsitution dans une fonction

substitution_funct(X,T,A,1,Q):- functor(A,F,N),arg(1,A,B),substitution_terme(X,T,B,V),functor(Q,F,N),arg(1,Q,V),!.

substitution_funct(X,T,A,N,Q):- functor(A,F,M),arg(N,A,B),substitution_terme(X,T,B,V),functor(Q,F,M),arg(N,Q,V),N2 is (N-1),substitution_funct(X,T,A,N2,Q),!.

% Predicat suivant creer pour ne pas faire de boucle

substitution_autre(_,_,[],[]):- !.

substitution_autre(X,T,[A=B|P],[A2=B2|P2]):- substitution_terme(X,T,A,A2),substitution_terme(X,T,B,B2),substitution_autre(X,T,P,P2).

arg_list((X ?= T),1,L1,[A ?= B|L1]) :- arg(1,X,A),arg(1,T,B),!.

arg_list((X ?= T),N,L1,L2) :- N2 is (N-1),arg(N,X,A),arg(N,T,B),arg_list(X ?= T,N2,[A ?= B|L1],L2).


% fin predicats pour reduit, donc predicats reduit

% Liste des prédicats réduits:

reduit(decompose,(X ?= Y),P1;Q,P2;Q):- echo(system :[X = Y|P1]),echo('\n'),echo(decompose :(X = Y)),echo('\n'),functor(X,_,A),arg_list(X ?= Y,A,[],L),append(P1,L,P2),!.

reduit(rename,(X ?= Y),P1;Q1,P2;[X=Y|Q2]):- echo(system :[X = Y|P1]),echo('\n'),echo(rename :(X = Y)),echo('\n'),substitution(X,Y,P1,P2),substitution_autre(X,Y,Q1,Q2),!.

reduit(simplify,(X ?= Y),P1;Q1,P2;[X=Y|Q2]):- echo(system :[X = Y|P1]),echo('\n'),echo(simplify :(X = Y)),echo('\n'),substitution(X,Y,P1,P2),substitution_autre(X,Y,Q1,Q2),!.

reduit(expand,(X ?= Y),P1;Q1,P2;[X=Y|Q2]):- echo(system :[X = Y|P1]),echo('\n'),echo(expand :(X = Y)),echo('\n'),substitution(X,Y,P1,P2),substitution_autre(X,Y,Q1,Q2),!.

reduit(orient,(X ?= Y),P;Q,[X ?= Y|P];Q):- echo(system :[X = Y|P]),echo('\n'),echo(orient :(X = Y)),echo('\n'),!.

reduit(check,(X ?= Y),P;Q,P;Q):- echo(system :[X = Y|P]),echo('\n'),echo(check :(X = Y)),echo('\n'),write('\n No'),fail,!.

reduit(clash,(X ?= Y),P;Q,P;Q):- echo(system :[X = Y|P]),echo('\n'),echo(clash :(X = Y)),echo('\n'),write('\n No'),fail,!.


 % Question 2

% Echelle de poids indiqué :
poids(clash,5).
poids(check,5).
poids(rename,4).
poids(simplify,4).
poids(orient,3).
poids(decompose,2).
poids(expand,1).

% commencer a écrire prédicats suivants

% Predicat pour forcer affichage a la fin des variables X, Y et Z par exemple
symb([]).
symb([X = X|T]) :- symb(T).

println([]):- echo('\n'), !.
println([X=T|P]):-  echo(X = T),echo('\n'),println(P).

unifie2([],Q):- echo('\n'),println(Q),write('Yes'),!.
unifie2([X|P],Q):- regle(X,R),reduit(R,X,P;Q,P2;Q2),unifie2(P2,Q2).

% predicats pour choix pondere, a instancier regle de poids, et element a retirer

retirerElement(_,[],[]):- !.
retirerElement(X,[T|R],Val):- X == T, Val = R, !.
retirerElement(X,[T|R],Val):- X \== T, retirerElement(X,R,Val).

ordrePoids([X],R,X):- regle(X,R), !.
ordrePoids([X,T|P],R,E):- regle(X,R1),poids(R1,P1),regle(T,R2),poids(R2,P2),P1 =< P2, !,ordrePoids([T|P],R,E).
ordrePoids([X,T|P],R,E):- regle(X,R1),poids(R1,P1),regle(T,R2),poids(R2,P2),P1 >= P2, !,ordrePoids([X|P],R,E).

% predicats des choix d application

choix_premier([],_,_,_):- !.
choix_premier([E|P],Q,E,R):- regle(E,R),reduit(R,E,P;Q,P2;Q2),unifie2(P2,Q2).

choix_pondere([],Q,_,_):- echo('\n'),affiche(Q),write('Systeme non unifiable'),!.
choix_pondere(P1,Q,E,R):- ordrePoids(P1,R,E),retirerElement(E,P1,P2),reduit(R,E,P2;Q,P3;Q3),choix_pondere(P3,Q3,_,_).

unifie(P,premier):- choix_premier(P,_,_,_).
unifie(P,pondere):- choix_pondere(P,_,_,_).
unifie(P):- choix_premier(P,_,_,_).

% Question 3

trace_unif(P,Strategie):- set_echo,unifie(P,Strategie),clr_echo,!.
unif(P,Strategie):- clr_echo,unifie(P,Strategie),clr_echo, !.

% amelioration affichage

instruction(P,Strategie,oui) :- trace_unif(P,Strategie), !.
instruction(P,Strategie,non) :- unif(P,Strategie), !.

option(oui):- demarrer.
option(non):- fail, !.

fin:- write('\n \t Souhaitez-vous continuer a utiliser le programme? Entrer oui ou non \n'),write(' \t Choix:'),read(Choix),option(Choix), !.

demarrer:- write('\n Ecrire le systeme que vous souhaitez unifier: \n'), write(' \t Systeme equation:'), read(Sys),write('\n Differents choix de strategie: laquelle desirez-vous utiliser ? Entrez premier ou pondere \n'),write('\t Strategie:'),read(Strat),write('\n Souhaitez-vous faire apparaitre dans le terminal la trace ? Entrer oui ou non \n'),write('\t Choix:'),read(Choix),write('\n'),instruction(Sys,Strat,Choix),fin, !.

sujet:- write('\t Ce programme repose sur l\'Algorithme d\'unification de Martelli-Montanari \n \n Nb: N\'oubliez pas d\'ajouter un point a chaque entre \n'),demarrer, !.
