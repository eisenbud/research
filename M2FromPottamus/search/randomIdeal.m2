--programs to form a random ideal of one sort or another.
--S is a ring, d a pos int, L a list of pos ints,
--randomMonomial(d,S)
--randomMonomialIdeal(L,S)
--randomBinomialIdeal(L,S)
--regSeq(L,S) -- for the ideal generated by powers of the variables.

--CAVEAT
--might want to make a routine that gives a reliable number of independent random monomials

randomMonomial = (d,S)->(
     m := basis(d,S);
     m_(0,random rank source m))

randomMonomialIdeal=(L,S)->(
     --L=list of degrees of the generators
     ideal apply(L, d -> randomMonomial(d,S))
     )

randomBinomialIdeal=(L,S)->(
     --L=list of degrees of the generators
     ideal apply(L, d->randomMonomial(d,S)-randomMonomial(d,S))
     )

randomSparseIdeal = (B,r,n) -> (
     -- B is a list of monomials
     -- r is the size of each poly
     -- n is the number of polys
     -- returns an ideal
     S := ring B#0;
     ideal apply(n, j -> 
       sum apply(r, i -> random coefficientRing S * B#(random(#B))))
     )

iRandomFromSupport1=(L,B)->sum(#L,
	  r->randomSparseIdeal(B,r+1,L_r))
--L_0=number monomials
--L_1=binomials...
--B a list of monomials

iRandomFromSupport=L->sum(#L,
	  r->randomSparseIdeal(L_r_1,L_r_0,1))
--L is a list of pairs, (num monomials, support list)

randomBinomials = (B,n) -> (
     -- B is a list of monomials
     -- n is the number of binomials
     -- returns an ideal
     S := ring B#0;
     ideal apply(n, j -> B#(random(#B)) - B#(random(#B)))
     )

regSeq=(L,S)->(
     --forms an ideal generated by powers of the variables.
     --L=list of NN. uses the initial subsequence of L as degrees of variables
     ideal for m to min(#L,rank source vars S)-1 list S_m^(L_m))

randomIdeal = (B, L) -> (
     -- B is a matrix of monomials
     -- L is a list of degrees
     ideal(B * random(source B, (ring B)^(-L)))
     )

looper = (rep,bound, L1, L2) -> (
     for i from 1 to rep do (
	  if i % 1000 == 0 then << "." << flush;
	  J := randomMonomialIdeal(L1,S) + randomBinomialIdeal(L2,S);
	  m := regularity coker gens J;
	  if m >= bound
	  then << "reg " << m << " " << toString J << endl;
	  )
     )

looper1 = (rep,bound) -> (
     for i from 1 to rep do (
	  J := randomIdeal(B,L);
	  m := regularity coker gens J;
	  if m >= bound
	  then << "reg " << m << " " << toString J << endl;
	  )
     )

looper3 = (rep,bound,B,r,n) -> (
     -- r is the number of monomials per poly
     -- n is the number of polys
     for i from 1 to rep do (
	  if i % 1000 == 0 then << "." << flush;
	  J := randomSparseIdeal(B,r,n);
	  m := regularity J;
	  if m >= bound
	  then << "reg " << m << " " << toString J << endl;
	  )
     )

loopprojdim = (rep,bound,B,r,n) -> (
     -- r is the number of monomials per poly
     -- n is the number of polys
     for i from 1 to rep do (
	  if i % 1000 == 0 then << "." << flush;
	  J := randomSparseIdeal(B,r,n);
	  m := pdim coker gens J;
	  if m >= bound
	  then << "pdim " << m << " " << toString J << endl;
	  )
     )

loopprojdim2 = (rep,bound,B,r,n) -> (
     H = new MutableHashTable;
     -- r is the number of monomials per poly
     -- n is the number of polys
     for i from 1 to rep do (
	  if i % 1000 == 0 then << "." << flush;
	  J := randomSparseIdeal(B,r,n);
	  b := betti res J;
	  m := pdim coker gens J;
	  if H#?(m,b) then H#(m,b)=H#(m,b)+1 else H#(m,b)=1;
	  if m >= bound
	  then << "pdim " << m << " " << toString J << endl;
	  )
     )

-- Checking for weak lefschetz
--XXX
expectedHF = (d,S) -> (
     I := ideal apply(gens S, x -> x^d) + ideal sum gens S;
     --I := ideal apply(gens S, x -> x^d) + ideal random(S^1, S^{-1});     
     poincare coker gens I
     )


checkWeakLefschetz = (B,r,n) -> (
     S := ring B#0;
     d := first degree B#0;
     I := randomSparseIdeal(B,r,n);
     I = ideal(matrix {apply(gens S, x -> x^d)} + gens I);
     f := sum gens S;
     hf := poincare (coker gens (I + ideal f));
     if hf != expected then (
	  if codim I == numgens S then (
	       LL := GF(27,Variable=>w);
	       T := LL[gens S];
	       I = (map(T,S)) I;
	       J := I + ideal random(T^1, T^{-1});
	       if hf != poincare coker gens J then
    	         << toString J << endl
	    )
	  )
     )

end

load "randomIdeal.m2"

kk=ZZ/101
S=kk[a,b,c]
L={2,4,5}
L1={2,4}
L2={2,4,5,6}
regSeq(L,S)
regSeq(L1,S)
regSeq(L2,S)

randomBinomialIdeal(L,S)
tally apply(100, i->randomMonomial(4,S))--

load "bettibounds.m2"
S=kk[a,b,c,d]
L={4,4,4,4}
for i from 1 to 10 do print  betti res (
     regSeq({4,4,4,4},S)+randomMonomialIdeal(toList(35:4),S))
toList (5:4)


S=kk[vars(1..7)]
vars S
time res randomMonomialIdeal(toList(35:7),S)
--NOTE: making it of type monomialIdeal doesn't help at all.

------- Banff October 15, 2006 ---------------
restart
load "randomIdeal.m2"

kk=ZZ/5
S=kk[a,b,c]
L={4,4,4}
B = matrix"ab,ac,bc"
time looper(30000,8)

kk=ZZ/2
S=kk[a,b,c,d]
I = ideal"a4,b4,c3a-d3b"
betti res I
L={4,4,4}
time looper(3,8,{4},{4,4})
time looper(30000,10,{4,4},{4})
betti res ideal (a*b^3+b^4,b*c^2*d+c^2*d^2,b*c^3+a^3*d)

restart
load "randomIdeal.m2"

kk=ZZ/2
S=kk[a,b,c,d]
B = flatten entries gens(ideal basis(2,S) * ideal"a3,b3,c3,d3")
randomSparseIdeal(B,3,4)
scan(13, i -> random 1000)
looper3(100000,18,B,3,3)
looper3(100000,18,B,2,4)

ideal (a^5,b*c^4+a^2*d^3+a*d^4,b^5)
ideal (a^5,a*b^4+b^5,a*c^4+b*d^4)
-- ideal(a^5,b^5,c^4*a+d^4*b) -- Giulio's example

kk = ZZ/3
S=kk[vars(0..14)]
B = flatten entries super basis(3,ideal(a,b));
loopprojdim(100000,5,B,3,3)
loopprojdim2(10000,5,B,3,3)
time loopprojdim2(100000,5,B,3,3)

kk = ZZ/3
S=kk[vars(0..14)]
B = flatten entries super basis(3,ideal(a,b));
time loopprojdim2(100000,5,B,5,3)

kk = ZZ/3
S=kk[a..e]
B = flatten entries super basis(3,ideal(a,b));
time loopprojdim2(100000,5,B,2,3) -- 2 cod 5 examples, 31 different betti diagrams
-- ideal (-a*b*d-a*c*e,a*c*d+b*c*e,-b*d*e)
-- ideal (-a*b^2,-b*c*d-a*c*e,a^2*c+b^2*d)


kk = ZZ/3
S=kk[a..f]
B = flatten entries super basis(3,ideal(a,b));
time loopprojdim2(100000,5,B,2,3) -- 31 different betti diagrams
-- ideal (a^2*c+b*c^2,a*b*c+a^2*f,b*c*d+a*b*f)
-- ideal (-b*c*d-a*c*f,-b^2*c-a*f^2,-b*f^2)
time for i from 1 to 100000 do random 30
time loopprojdim2(100000,5,B,2,3) -- 
-- ideal (-b*c*f-a*e*f,-a*b*e-a*c*f,-b*c*e)
-- ideal (a*b^2+b^2*f,-a*c*e-b*c*f,a^2*c-b^2*f)
-- ideal (-a*b^2,b^2*c+a^2*e,b*c*e+a*e*f)
-- ideal (a*c*e-b*d*e,a*c*d-a*b*e,-a*c*d-b*c*d)

-- ideal (-a*d*e,b*c*d-a*c*e,a*b*d-b*c*e)
-- ideal (-a*b*d+b*e*f,-b*d*f+a*e*f,a*d*e)
-- ideal (a*b^2+a^2*e,b*d*e+a*e*f,b^2*d)

time for i from 1 to 100006 do random 30
time loopprojdim2(100000,5,B,2,3) -- 

-- ideal (a^2*c+b^2*e,-a*c^2+b*c*d,b^3)
-- ideal (a*f^2,b*c*e-a*c*f,b^2*c-b*f^2)
-- ideal (a*b*d,b*d*f-a*e*f,-a*d*e-b*e*f)

-- ideal (b*d*e+a*e*f,-a*b*e+a*d*f,b*d*f)
-- ideal (a^2*c+b*c^2,a*b*c-a^2*f,-b*c*e-a*b*f)

-- quartics -------------------------------------

--------- 
restart
load "randomIdeal.m2"
kk = ZZ/101
S = kk[a..d]
expected = expectedHF(5,S)
prims = select(1..10000, i -> isPrime i)
select(prims, p -> expected != expectedHF(5,ZZ/p[a..d]))
S = ZZ/3[a..d]
B = flatten entries basis(5, S)
for i from 0 to 100000 do (if i % 1000 == 0 then << "." << flush; checkWeakLefschetz(B,2,4))
I = ideal (a^5-2*a*d^4,b^5,3*c^5-2*a*d^4,d^5)
J = I + ideal random(S^1,S^{-1})
poincare coker gens J
expected == oo

LL = GF(49,Variable=>w)
T = LL[a..d]
I = (map(T,S)) I
J = I + ideal random(T^1, T^{-1})
poincare coker gens J


--------Craig's World
restart
load "randomIdeal.m2"
kk = ZZ/3
S = kk[a..d]
--i=ideal"ac,ad,bc,bd"

multLength= i->(
     R:=ring i;
     degree(R^1/(i+ideal random(R^1,R^{dim i:-1}))))


maxTwists=(F,n)->apply(1..n, i->first max degrees F_i)
minTwists=(F,n)->apply(1..n, i->first min degrees F_i)

craig1= i ->(
     c:=codim i;
     F:= res (i, LengthLimit => c+1);
     b:=product toList minTwists(F,c);
     B:=product toList maxTwists(F,c);
     multL:=c!*multLength i;
     <<(codim i,b,c!*degree i, multL,B)<<endl;
     if b>multL or multL>B then print toString i;
     )
craig2= i ->(
     c:=codim i;
     F:= res (i, LengthLimit => c+1);
--     b:=product toList minTwists(F,c);
     B:=product toList maxTwists(F,c);
     multL:=c!*multLength i;
--     <<(c,degree i, multL,B)<<endl;
     if multL>B then print toString i;
     )


f=()->(iRandomFromSupport1({4:2},
          first entries basis(4,S))+
     iRandomFromSupport1({4:3},
          first entries basis(3,S)))
     

time for i from 0 to 10000 do(
     if i%1000==0 then <<"."<<flush;
     craig2(f()))



craig1 i
--codim,lowerBound, codim!degree, codim!length, upperBound:
(2, 15, 2, 12, 18)
i=trim ideal (-17*c^2*d,-45*c^2*d,3*a^2*d,44*b^3-36*c*d^2,32*b^2*d-33*b*d^2,34*a*b*c-30*b^2*c)
(2, 15, 6, 12, 18)
i=trim ideal (43*c^3,19*a^2*c,24*a^2*c,31*b*c*d,48*a*b^2,-17*b*c*d)
betti res i
see i
codim i
see primaryDecomposition i
see ass i

randomSparseIdeal = (B,r,n) -> (
     -- B is a list of monomials
     -- r is the size of each poly
     -- n is the number of polys
     -- returns an ideal


----------------
restart
load "randomIdeal.m2"
iRandomFromSupport=L->trim sum(#L,
	  r->randomSparseIdeal((L_r)_1,(L_r)_0,1))
--L is a list of pairs, (num monomials, support list)

kk = ZZ/3
S = kk[a..e]
B=d->flatten entries super basis(d,ideal(a,b))
L= splice {0:(1,B(5)), 2:(2,B(10))};
see L;
f=()->iRandomFromSupport L+ideal(a^10,b^10)
--setRandomSeed 111000111001

time M=for i from 1 to 10000 list((
          F:=res f();
     r:=(regularity F)+1;
     f1=(first max degrees F_2)-1;
--     if r<29 or r==f1 then continue;
     (r,r*1.0/f1,f1,betti F,toString ideal F.dd_1 ))
)     ;
max M
M1=select(M,i->i#0>36);
M2=select(M1, i->i#0!=i#2);
#M2
M3=select( M2, j->j#1>1.2);
see M3
max M3
max apply(M2, j->j#1)

tally M    

P=flatten for i from 1 to 9 list(
flatten for j from 1 to 9 list(
res ideal(a^10,b^10,a^i*c^(10-i)-b^j*d^(10-j))));
tally (P/(F->(1+regularity F)*1.0/(-1+first max degrees F_2)))
G=first select(P, 
     (F->(1+regularity F)*1.0/(-1+first max degrees F_2)>1.4)
)
G.dd_1
betti G


---------
kk = ZZ/3
S = kk[a..e]
B=d->flatten entries basis(d,S)
L= splice {0:(1,B(5)), 1:(2,B(10))};
see L;
f=()->iRandomFromSupport L+ideal(a^10,b^10,c^10)
--setRandomSeed 111000111001