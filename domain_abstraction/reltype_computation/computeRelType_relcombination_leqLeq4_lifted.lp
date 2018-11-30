
domAbs(ABS,A) :- dom(ABS,X),mapTo(ABS,X,A).


%A1<=A2,A3<=A4
%leqLeq(ABS,A1,A2,A3,A4,exists) :- X1<=X2,X3<=X4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).
%leqLeq(ABS,A1,A2,A3,A4,neg_exists) :- X1>X2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).
%leqLeq(ABS,A1,A2,A3,A4,neg_exists) :- X3>X4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).

%rel(ABS,leqLeq,A1,A2,A3,A4,i) :- not leqLeq(ABS,A1,A2,A3,A4,neg_exists), A1<=A2,A3<=A4, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3), domAbs(ABS,A4).
%rel(ABS,leqLeq,A1,A2,A3,A4,ii) :- not leqLeq(ABS,A1,A2,A3,A4,exists), A1>A2, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3), domAbs(ABS,A4).
%rel(ABS,leqLeq,A1,A2,A3,A4,ii) :- not leqLeq(ABS,A1,A2,A3,A4,exists), A3>A4, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3), domAbs(ABS,A4).
%rel(ABS,leqLeq,A1,A2,A3,A4,iii) :- leqLeq(ABS,A1,A2,A3,A4,neg_exists), A1<=A2,A3<=A4, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3), domAbs(ABS,A4).
%rel(ABS,leqLeq,A1,A2,A3,A4,iv) :- leqLeq(ABS,A1,A2,A3,A4,exists), A1>A2, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3), domAbs(ABS,A4).
%rel(ABS,leqLeq,A1,A2,A3,A4,iv) :- leqLeq(ABS,A1,A2,A3,A4,exists), A3>A4, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3), domAbs(ABS,A4).


#show rel/5.
#show rel/6.
#show rel/7.

