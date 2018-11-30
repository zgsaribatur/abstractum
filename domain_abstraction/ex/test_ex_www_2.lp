c(X) :- not d(X), dom(X).
d(X) :- not c(X), X<5, dom(X).
b(X,Y) :- a(X),d(Y), X=Y, dom(X), dom(Y).
e(X) :- c(X), a(Y), X<=Y, dom(X), dom(Y).
a(1).a(3).
dom(1..5). 
