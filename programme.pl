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

regle((X ?= T),check) :- X \== T, var(X), occur_check(X,T),!.

regle((X ?= T),expand) :- var(X), compound(T), not(occur_check(X,T)), !.

regle((X ?= T),decompose) :- compound(X), compound(T), functor(X,A1,N1), functor(X,AX,NX), A1 == AX, N1 == NX, !.

regle((X ?= T),clash) :- compound(X), compound(T), functor(X,_,A1), functor(T,_,A2), A1 \== A2, !.

regle((X ?= T),clash) :- compound(X), compound(T), functor(X,A1,_), functor(T,A2,_), A1 \== A2, !.

% prédicat qui vont servir pour créer les prédicats réduits

concat([],X,X).
concat([X|P],Y,[X|Q]) :- concat(P,Y,Q).

% Liste des prédicats réduits:

reduit(check,_,_,_) :- echo(system : [X ?= Y|P]),echo('\n'),echo(check : (X ?= Y)),echo('\n'),write('Système non unifiable'),fail,!.

reduit(orient,[X ?= T], P;S, [T ?= X|P];S) :- echo(system : [X ?= T|P]), echo('\n'), echo(orient : (X ?= T)), echo('\n'), !.

reduit(clash,_,_,_) :- echo(system : [X ?= T|P]),echo('\n'),echo(clash : (X ?= T)),echo('\n'),write('Système non unifiable'),fail, !.


% a partir de là, pas tester

% ajout du prédicat substitution pour les prédicats réduits suivants
% on remplace premier parametre par deuxieme parametre dans équation du troisieme parametre
% et on met le resultat dans le quatrieme parametre

substitution(_,_,[],[]) :- !.

substitution(X,T,[A ?= B|P],[A2 ?= B2|P2]) :- substitution_terme(X,T,A,A2),substitution_terme(X,T,B,B2),substitution(X,T,P,P2)

substitution_terme(X,T,A,T) :- A == X, not(compound(A)), !.

substitution_terme(X,_,A,A) :- A \== X,not(compound(A)), !.

substitution_terme(X,T,A,Q) :- compound(A), functor(A,_,At),substitution_autre(X,T,A,At,Q), !.

% substitution_autre pour substitution fonction

substitution_autre(X,T,A,1,Q):- functor(A,F,At),arg(1,A,VX),substitution_terme(X,T,VX,R),arg(1,Q,R),functor(Q,F,At), !.

substitution_autre(X,T,A,N,Q):- functor(A,F,At),arg(N,A,VX),substitution_terme(X,T,VX,R),arg(N,Q,R),functor(Q,F,At), N2 is (N-1),substitution_autre(X,T,A,N2,Q), !.

% arg_list

arg_list(1,(X ?= T),L1,L2):- L2=[VX ?= VT | L1],arg(1,X,VX),arg(1,T,VT), !.

arg_list(N,(X ?= T),L1,L2):- N2 is (N-1),arg(N,X,VX),arg(N,T,VT),arg_list(N2,X ?= T,[VX ?= VY |L1],L2).


% fin predicats pour reduit, donc suite predicats reduit


reduit(rename,(X ?= T), P;S , A;[X = T|B]):- echo(system :[X ?= T|P]),echo('\n'),echo(rename: (X ?= T)),echo('\n'),substitution(X,T,P,A),substitution(X,T,S,B), !.

reduit(simplify,(X ?= T), P;S, A;[X = T|B]):- echo(system :[X ?= T|P]),echo('\n'),echo(simplify: (X ?= T)),echo('\n'),substitution(X,T,P,A),substitution(X,T,S,B), !.

reduit(expand,(X ?= T), P;S, A;[X = T|B]):- echo(system :[X ?= T|P]),echo('\n'),echo(rename: (X ?= T)),echo('\n'),substitution(X,T,P,A),substitution(X,T,S,B), !.

reduit(decompose,(X ?= T), P;S, Q;S):- echo(system :[X = T|P]),echo('\n'),echo(decompose: (X ?= T)),echo('\n'), functor(X,_,A), arg_list(A,X ?= T,[],L2), concat(L2,P,Q), !.

 % Question 2

% Echelle de poids indiqué :
poids(clash,5).
poids(check,5).
poids(rename,4).
poids(simplify,4).
poids(orient,3).
poids(decompose,2).
poids(expand,1).


choix_premier([],_,_,_):- !.
choix_premier([E|P],Q,E,R):- regle(E,R),reduit(R,E,P;Q,P2;Q2),unifie2(P2,Q2).

% commencer a écrire prédicats suivants

choix_pondere():-!.
choix_pondere():-.

unifie2():-!.
unifie2():-.

