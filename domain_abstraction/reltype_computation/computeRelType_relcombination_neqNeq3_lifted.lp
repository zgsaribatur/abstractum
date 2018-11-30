
domAbs(ABS,A) :- dom(ABS,X),mapTo(ABS,X,A).

%A1!=A2,A2!=A3
neqNeq(ABS,A1,A2,A3,exists) :- X1!=X2,X2!=X3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).
neqNeq(ABS,A1,A2,A3,neg_exists) :- X1=X2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).
neqNeq(ABS,A1,A2,A3,neg_exists) :- X2=X3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).

rel(ABS,neqNeq,A1,A2,A3,i) :- not neqNeq(ABS,A1,A2,A3,neg_exists), A1!=A2,A2!=A3, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3).
rel(ABS,neqNeq,A1,A2,A3,ii) :- not neqNeq(ABS,A1,A2,A3,exists), A1=A2, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3).
rel(ABS,neqNeq,A1,A2,A3,ii) :- not neqNeq(ABS,A1,A2,A3,exists), A2=A3, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3).
rel(ABS,neqNeq,A1,A2,A3,iii) :- neqNeq(ABS,A1,A2,A3,neg_exists), A1!=A2,A2!=A3, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3).
rel(ABS,neqNeq,A1,A2,A3,iv) :- neqNeq(ABS,A1,A2,A3,exists), A1=A2, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3).
rel(ABS,neqNeq,A1,A2,A3,iv) :- neqNeq(ABS,A1,A2,A3,exists), A2=A3, domAbs(ABS,A1), domAbs(ABS,A2), domAbs(ABS,A3).


#show rel/5.
#show rel/6.
#show rel/7.
