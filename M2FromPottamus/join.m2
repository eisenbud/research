--join of two ideals
joinIdeal=(i,j)->(
     --join of two ideals over the same homogeneous polynomial ring S.
     --moves the ideals into S**S, in the two factors; takes the
     --kernel of the map taking the variables of S into the sums
     --of the variables from the two factors ("diagonal embedding")
     S:=ring i;
     kkk:=coefficientRing S;
     n:=rank source vars S;
     T:=kkk[X_0..X_(n-1),Y_0..Y_(n-1)];
     sub1:=map(T,S,matrix{{X_0..X_(n-1)}});
     sub2:=map(T,S,matrix{{Y_0..Y_(n-1)}});
     IJ:=sub1(i)+sub2(j);
     R:=T/IJ;
     sums:=map(R^1,R^{n:-1},(u,v)->X_v+Y_v);
     sub3:=map(R,S,sums);
     ideal mingens kernel sub3
     )

secantIdeal= i->joinIdeal(i,i)
end 

restart
load "join.m2"

--Case of 5 points in PP^3
S=kk[a,b,c,d]
i=intersect(ideal(a,b,c),ideal(b,c,d),ideal(c,d,a),ideal(d,a,b), ideal(a-b,b-c,c-d))
betti res i
isec=secantIdeal(i)

--secant variety is the union of 10 lines, an
--ACM curve of degree 10, p_a=11.
degree isec
dim isec
betti (FF= res isec)

--case of elliptic quintic in PP^4
S=kk[a..e]
f1=e
f2=0
f3=a+b+c+d+e
m1=matrix{
     {0,0,a,b,c},
     {0,0,b,c,d},
     {0,0,0,f1,f2},
     {0,0,0,0,f3},
     {0,0,0,0,0}
     }
m=m1-transpose m1
i=pfaffians(4,m)
betti res i
betti gens(si=secantIdeal i)

betti res top(i^2)
betti res (i^2)

ti3=top(i^3)
ti3=oo;
betti res ti3

---
--in P^6 the secant locus is everything;
--and the third symbolic power has no quintic generator,
--even in the following fairly degenerate example

S=kk[a..f]
f1=e
f2=0
f3=f
m1=matrix{
     {0,0,a,b,c},
     {0,0,b,c,d},
     {0,0,0,f1,f2},
     {0,0,0,0,f3},
     {0,0,0,0,0}
     }
m=m1-transpose m1
i=pfaffians(4,m)
betti res i
betti gens(si=secantIdeal i)

betti res top(i^2)
betti res (i^2)

ti3=top(i^3)
ti3=oo;
betti res ti3

-------------
--with Huneke and Ulrich

restart
load "join.m2"

S=kk[a,b,c]
f=a^4+b^4+c^4-a^2*b^2-a^2*c^2-b*c^3
i=gor f
betti res i
betti res (j=secantIdeal i)

------------

S=kk[a,b,c]
i=ideal fromDual(matrix{{a^2+b^2+c^2}})
--i=ideal(random(S^1,S^{3:-2}))
betti res i
betti (FF=res (i2=secantIdeal i) )
betti(GG=res (i3=secantIdeal i2) )
betti(GG=res (i4=secantIdeal i3) )

gor = f->(
i:=ideal fromDual(matrix{{f}}))

gor a^2
betti res secantIdeal(gor (a^4+b^4+c^4-a^2*b*c+b^2*c^2+a^3*c))
betti res gor (a^4+b^4+c^4-a^2*b*c+b^2*c^2+a^3*c)

betti res gor (f=a^4+c^4-a^2*b*c+b^2*c^2+a^3*c)
betti res secantIdeal gor f

betti res gor (f=a^6+a^3*b^3+b^6)
betti res (i2=secantIdeal gor f)
betti res secantIdeal i2

v=ideal(a^6,b^6,c^6)
i=quotient(v,a^4+b^4+c^4-a^2*b*c)
betti res i -- it's Gorenstein
betti res (i2=secantIdeal i) -- socle in 3 degrees
degree i
degree i2

T=kk[a,b,c,x,y,z]
f1=map(T,S)
f2=map(T,S,matrix{{x,y,z}})
I=(f1 i)+(f2 i)
quotient(I,a+b+c+x+y+z)

-----------------
kk=QQ
T=kk[a,b,x,y]
--S=kk[a,b]
v1=ideal(a,b)
v2=ideal(x,y)
j=v1^2 * v2^2
ff=map(T,T,matrix{{a-x,b-y,a-x,b-y}})
k=ff j;
contract(transpose gens j,gens k)
det oo
m=matrix{
     {a^4*x^4, a^3*b*x^3*y, a^2*b^2*x^2*y^2, a*b^3*x*y^3, b^4*y^4}}


map(T,S,(matrix{{a-x,b-y}})
-----------------
kk=ZZ/2
S=kk[a,b]
i=ideal(a^2,b^2)
--i=ideal random(S^1,S^{-2,-2})
j= secantIdeal i
betti res i
betti res j
----------------
kk=ZZ/101
S=kk[a,b]

i=ideal random(S^1,S^{-9,-4})
betti res i
betti res (j=secantIdeal i)

S=kk[a,b]
i0=ideal random(S^1,S^{-9})
i=i0+ideal(a^4)
betti res i
betti res (j=secantIdeal i)


betti res secantIdeal j
i0=ideal(a^2,b)
k=joinIdeal(ideal(a^2,b), ideal(random(S^1,S^{-2,-4})))
hf(0..5,S^1/k)
betti res k
betti res(kk=joinIdeal(ideal(a^2,b), k))

i=ideal fromDual matrix{{a^3+b^3, a^5+b^5}}
i=ideal toDual matrix{{a^3, b^5}}
help toDual
betti res joinIdeal(i0,i)
i1=intersect(ideal fromDual matrix{{a^3+b^3, a^5+b^5}}, ideal fromDual matrix{{a^3+b^3, a^5+b^5}})
ideal fromDual matrix{{a^3+b^3}}
ideal fromDual matrix{{a^5+b^5}}


