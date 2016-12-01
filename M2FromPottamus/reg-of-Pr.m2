reduce= i->(
  C:=codim i;
  T:=kk[vars (0..C-1)];
  F:=map(T,ring i,random(T^1,T^{rank source vars ring i:-1}));
F i)

test = i->(
--print 
(L1:=bettiBounds i);
--print 
(L2:=bettiBounds reduce i);
print (L1_{0..#L2-1}-L2);
)

end

load "reg-of-Pr.m2"
restart
S=kk[a,b,c]
m6=gens ((ideal vars S)^6)

A=matrix{{a*b^2*c^3, a^3*b*c^2, a^2*b^3*c}}
i = ideal (m6 % A)
betti res i

f=(a^2+b^2+c^2)^2
toDual
i= ideal fromDual matrix{{f}}
betti res i
j= i: a^2+b^2+c^2
h=i:j
(gens i)% (gens (j*h))

---
n=3
d=5
m=2*n
--m=5
S=kk[vars (0..n-1)]
i=ideal random(S^1,S^{m:-d});
powers=(ideal (vars S))^[d]
j=ideal random(S^1,S^{n:-d}) + powers;
--time for s from 1 to 5 do 
--(print betti res i^s;
--print  betti res j^s
)
--betti res i^6  
--for i from 4 to 20 list binomial(2*i-1,5)-binomial(2*i^2-4*i+2,2)

--so for degree 11, for the first time, we might expect 6 generic forms of degree 11 to become a
--power of m as soon as m*(vars)^[11]. (the 18th power!)

--What's the fastest way of testing for a power of m?
--We just need to compute a minimal system of generators, and compare the numbers!

--time rank source gens trim i^s
--time rank source gens gb(i^s, DegreeLimit=> d*s)

s=1
while binomial(5+s,5)<binomial(2+d*s,2) do s=s+1
s
--time rank source gens trim i^s
time rank source gens trim j^s
binomial(2+d*s, 2)

rank source compress (gens ((ideal vars S)^(d*s)) % (i^s))

time for s from 1 to 5 do 
print rank source compress (gens ((ideal vars S)^(d*s)) % (i^s))
)

s=1

while (R= (rank source compress (gens ((ideal vars S)^(d*s)) % (i^s))))=!=0 do (print ; s=s+1)

(print R; s=s+1)
     

print R; s=s+1 )
--n             3          2
--d             4          
--power         1 2 3 4 5
--linear steps  0 0 1 2 3

pro=product(0..n-1, i-> S_i)
skel=ideal compress (gens((ideal vars S)^d) % matrix{{pro}})
betti res (skel^2)
--(skel^2 has linear res)

-----------------
restart
n=3
S=kk[vars (0..n-1)] -- a, b, ...
d=4
j=ideal random(S^1, S^{2:-d});
--i=ideal(a^d,b^d, c^d, a^(d-1)*b) +j; --reg of image is 7
--i=ideal(a^d,b^d,a^(d-1)*b, a^(d-1)*c) +j; -- reg of ideal of image is 12, map is NOT embedding
--i=ideal(a^d,b^d,a^(d-1)*b, a^(d-2)*b^2) +j; -- reg of ideal of image is 8, map is NOT embedding
--i=ideal(a^d,b^d,c^d, a^(d-1)*b) +j; -- reg of ideal of image is 7, map is NOT embedding
--i=ideal random(S^1, S^{6:-d}); -- reg of ideal of image is 6, map is an embedding, first power equal is 5th. 
i= (i1=minors(3,random(S^{4:-d}, S^{2:-d-1,-2*d+2})))+j; -- for d=4 reg of ideal of image is 11, first power equal is 10th.
--i1=(ideal vars S)*ideal(a^(d-1)+b^(d-1)+c^(d-1))

--i1=(ideal vars S)*ideal(random(S^1,S^{-d+1}));
--i2=ideal(random(S^1,S^{-d}));
--i=i1+i2+j; -- reg of ideal of image is 12

powers=(ideal (vars S))^[d]
i=ideal random(S^1,S^{n:-d}) + powers;

betti res i
T=kk[u,v,w,x,y,z]
F=map(S,T,gens i);
time I=kernel F;
--degree I
time betti (FF=res (I,LengthLimit => 1))
FF=res (I,LengthLimit => 2)
e= regularity FF -- regularity of the homog coord ring
binomial(2+d*e,2)
hilbertFunction(e, T^1/I)

--rank source gens (itemp = trim i^11)


time i11=i^11;
time j11=(ideal vars S)^11;
time m=contract(transpose gens j11, gens i11)

contract (transpose vars S, vars S)

----
o16 = total: 1 25 60 58 28 6
          0: 1  .  .  .  . .
          1: .  .  .  .  . .
          2: .  .  .  .  . .
          3: . 15 24 10  . .
          4: .  .  .  .  . .
          5: .  .  .  .  . .
          6: .  9 33 45 27 6
          7: .  .  .  .  . .
          8: .  .  .  .  . .
          9: .  .  .  .  . .
         10: .  .  .  .  . .
         11: .  1  3  3  1 .


-----
restart
n=5
m=2
S=kk[vars(0..n-1)]

i=intersect((ideal vars S)^[m], (ideal vars S)^(2*m-1));
betti res ((ideal vars S)^[m])

betti res i
betti res i^2
betti res i^3

restart
S=kk[vars(0..2)]
i=ideal(fromDual random(S^1,S^{-7}))
m3=(ideal vars S)^3
j=m3*i;
betti res i
L=ideal random(S^1,S^{-1});
betti res (L+j)
betti res j

restart


S=kk[vars(0..5)]
for p1 from 2 to 20 do 
for p2 from p1+1 to 21 do(i=monomialCurveIdeal(S,{1,p1,p2, 25,27});
print (p1,p2,test i))
)
S=kk[a,b,c,x]
i=ideal(a*c-b^2, b*c,c^2, x*a*c, x*a*b, x*a^2)
codim i
betti res i

S=kk[x,y,z,t]
ideal(t^2*x^3+t^2*y^3+t*x*y^2*z+z^4*x,
     3*t^2*x^2+t*y^2*z,
     t*x*y^2+4*z^3*x,
     3*t^2*y^2+2*t*x*y*z)

ising=gens (ideal(x,y,z))^2
f=ising*random(S^6, S^{1:-5});
betti (i=ideal f+ ideal diff(matrix{{x,y,z}},f))
betti res i
bettiBounds i
bettiBounds reduce i

test i

U=kk[a,b,c,x,y,z]
i=ideal(x*a,x*b+y*a,z*a+y*b+x*z,z*b+y*c, z*c)
betti res i
T=kk[x,y,z]
F=map(T,U,random(T^1,T^{6:-1}));
betti res F i

restart
S=kk[x_0..x_5]
T=kk[a,b,c]
F=map(T,S,matrix{{c^13, a^12*c, b^8*c^5, a*b^7*c^5, a^5*b*c^7, a^9*b^4}})
i=mingens kernel F
betti i
j=submatrix(i, {0}, {0..11})
betti j
betti res coker j
test ideal j



i=trim monomialCurveIdeal(S,{1,6,14, 25,27});
test i
betti i
mingens i

j=submatrix(gens i, {0}, {1..10})
betti j
betti res coker j
test ideal j

kk=ZZ/2
S=kk[a..f]
i=ideal(a*b*d,b*c*d, c*d*e, a*c*e, a*b*e, b*f*e, b*c*f, a*f*c, a*f*d, d*e*f)
betti res i
test (i^2)
betti res i^2
betti res reduce i
test i
res reduce i^2

kk=ZZ/32003
S=kk[vars(0..8)]
m=genericSymmetricMatrix(S,a,3)
i=minors(2,m)
test i^2
betti res i^2

-----

load "reg-of-Pr.m2"

S=kk[vars(0..3)]
i=ideal fromDual random(S^1, S^{ -10});
betti res i
j=intersect(ideal(a,b,c), ideal(b,c,d))
k=intersect(i,j);
betti res k
test k
use S
betti res(i1=(ideal(a)+i))
bettiBounds i
bettiBounds i1

restart
gbTrace 1
n=6
S=kk[vars(0..n-1)]
i=(ideal vars S)^[4]
--i1=i+ideal(random(S^1,S^{1:-1}))
--bettiBounds i
--bettiBounds i1
--point=ideal random(S^1, S^{n-1:-1});
point=ideal(a,b,c,d,e)
j= intersect(i,point);
--j1=j+ideal(random(S^1,S^{1:-1}));
T:=kk[vars (0..n-3)];
F:=map(T,ring i,(vars T|random(T^1,T^{2:-1}));
jbar=F j;
res(jbar, LengthLimit=>3, DegreeLimit=>10)
betti oo
betti res j
bettiBounds j



bettiBounds j1





kk=ZZ/
S=kk[vars(0..3)]
i=(ideal vars S)^[3]
s=sum(0..3, i->S_i)
j=i+ideal(s^3)
bettiBounds j
bettiBounds i
betti res i
betti res j

point=ideal random (S^1,S^{3:-1});
k=i+point
bettiBounds k
bettiBounds (k+ideal(s^3))


restart
S=kk[a..g]
i=ideal(a^3,b^3,c^3,d^3,e^3,f^3, g^3, f*(c*e-g^2), d^2*(a-e))
j=ideal(a^3,c^3,d^3,e^3,f^3, g^3, f*(c*e-g^2), d^2*(a-e))
betti res i
betti res i^2
betti res j
betti res j^2

