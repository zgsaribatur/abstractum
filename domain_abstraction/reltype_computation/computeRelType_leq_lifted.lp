%%

domAbs(ABS,A) :- dom(ABS,X),mapTo(ABS,X,A).

%relation : leq (<=)
leq(ABS,A1,A2,exists) :- X1<=X2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2).
leq(ABS,A1,A2,neg_exists) :- X1>X2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2).

rel(ABS,leq,A1,A2,i) :- not leq(ABS,A1,A2,neg_exists), A1<=A2, domAbs(ABS,A1), domAbs(ABS,A2).
rel(ABS,leq,A1,A2,ii) :- not leq(ABS,A1,A2,exists), A1>A2, domAbs(ABS,A1), domAbs(ABS,A2).
rel(ABS,leq,A1,A2,iii) :- leq(ABS,A1,A2,neg_exists), A1<=A2, domAbs(ABS,A1), domAbs(ABS,A2).
rel(ABS,leq,A1,A2,iv) :- leq(ABS,A1,A2,exists), A1>A2, domAbs(ABS,A1), domAbs(ABS,A2).



#show rel/5.


isCluster(ABS,A) :- dom(ABS,X), dom(ABS,X1), X!=X1, mapTo(ABS,X,A), mapTo(ABS,X1,A).
isUnique(ABS,A) :- not isCluster(ABS,A), domAbs(ABS,A).


#show isCluster/2.
#show isUnique/2.
#show mapTo/3.

