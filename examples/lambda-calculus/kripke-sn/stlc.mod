module stlc.

of (abs A M) (arr A B) :-
  pi x \ of x A => of (M x) B.
of (app M N) B :-
  of M (arr A B), of N A.

cp (abs A M) (abs A MC) :-
  pi x \ cp x x => cp (M x) (MC x).
cp (app M N) (app MC NC) :-
  cp M MC, cp N NC.