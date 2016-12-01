reesClassic= (i,a)->(
     --i an ideal. a must be a nzd in i
     m:=syz gens i;
     R:=ring i;
     S:=(coefficientRing R)[X_0..X_(numgens R-1),Y_0..Y_(numgens i-1), 
	  Degrees=>toList (numgens R:{1,0})|apply(numgens i, p->flatten{degree i_p,1})];
     M:=(f=map(S,R,matrix{{S_0..S_(numgens R-1)}})) m;
     K:=ideal(matrix{{Y_0..Y_(numgens i -1)}}*M);
     saturate(K,f a)
     )

--dot product function
dot = (X,Y) -> sum apply(#X, j-> X#j*Y#j);

weightedBetti = method()
weightedBetti (BettiTally,List) := (B,W) -> (
--takes a BettiTally (output of betti resolution) and rewrites it in such a way that when
--displayed its degrees correspond to the weighted some of dgrees given by the coeffs in W.
     new BettiTally from apply(pairs B, i-> (
	       (key,bettivalue) := i;
	       (key#0, prepend(dot(W,key#2),key#2)),
	       bettivalue)))

weightedRegularity=method()
weightedRegularity(BettiTally,List):=(B,W) ->(
--takes a BettiTally (output of betti resolution) and computes regularity
--with respect to the total degree given
--by dotting the degree vector with W.
     max  apply(pairs B, i-> (
	       key := first i;
	       dot(W,key#2)-key#0)
))

regPowersData=(I, d)->(
     --tests the powers up to degree d, returns first place after which
     --the slope and excess computed in the d-th place hold
rr:=apply(d, i-> regularity(I^i));
slope := (last rr)//(d-1);
excess = (last rr)%(d-1);
stabilization  = 1+last  positions (apply(d-1, i->rr_i =!= (slope*i+excess)), v->v);
(stabilization, slope, excess)
)

     
///
--the degrees are set wrong in vers 0.93
reesAlgebra = method()
reesAlgebra Ideal := (I) -> (
     R := ring I;
     n := numgens R;
     j := syz gens I;
     m := numgens I;
     S := tensor(R,(coefficientRing R)[Y_0..Y_(m-1), Degrees=>apply(numgens I, i->degree(I_i))], MonomialOrder => GRevLex);
     symm := ideal((substitute(matrix{{S_n..S_(n+m-1)}},S))*substitute(j,S));
     saturate(symm, substitute(I_0, S)))
///
end
restart
load "rees-new.m2"
kk=ZZ/101
RU=kk[x,y]
i=(ideal vars RU)^2
RI=reesClassic(i, i_0)
betti res RI
peek betti res RI
weightedBetti(betti res RI, {0,1})
weightedRegularity(betti res RI, {0,1})


kk=ZZ/101
R=kk[a..e]
I=monomialCurveIdeal(R, {1,2,3,5})
RI=reesClassic (I, I_0)
regularities=apply(8, i-> regularity(I^i))
length regularities
slope = (last regularities)//((length regularities)-1)
excess = (last regularities)%((length regularities)-1)
stabilization  = 1+last  positions (apply(length regularities-1, i->regularities_i =!= (slope*i+excess)), v->v)





i=2
regularities_i=!=slope*i+excess
regularities
C
D
weightedBetti(betti res RI, {0,1})
weightedRegularity(betti res RI, {0,1})

I=monomialCurveIdeal(R, {1,2,3,6})
RI=reesAlgebra(I)
a = last (C=apply(8, i-> regularity(I^i)//i))
b = last (D=apply(8, i-> regularity(I^i)-a*i))
C
D
weightedBetti(betti res RI, {0,1})
weightedRegularity(betti res RI, {0,1})
i7 : betti res RI

            0 1 2 3 4
o7 = total: 1 5 2 5 2
         0: 1 . . . .
         1: . 5 1 . .
         2: . . 1 5 1
         3: . . . . 1

o7 : BettiTally

i8 : peek oo

o8 = BettiTally{(0, {0, 0}) => 1 }
                (1, {2, 2}) => 5
                (2, {3, 4}) => 1
                (2, {4, 2}) => 1
                (2, {4, 4}) => 10
                (3, {5, 4}) => 5
                (3, {5, 6}) => 5
                (4, {6, 8}) => 1
                (4, {7, 6}) => 1


--------------




S =  ZZ/101[a, b, c, d, e, Y_0, Y_1, Y_2, Y_3, Y_4, Degrees => 
  {{1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 0}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}}]


RI = ideal (b*Y_2-c*Y_3+d*Y_4,a*Y_2-b*Y_3+c*Y_4,c*Y_0-d*Y_1+e*Y_3,b*Y_0-c*Y_1+
      d*Y_2+e*Y_4,a*Y_0-b*Y_1+d*Y_3)

betti res RI
weightedBetti (betti res RI, {0,1})
