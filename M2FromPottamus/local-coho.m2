restart
-- Mircea's example of an unmixed ideal
-- for which injectivity fails.
kk=ZZ/32003
R=kk[x,y,z,w]
i1=ideal(x, y)
i2=ideal(x^2,z)
i3=ideal(y,w)
i=intersect(i1,i2,i3)
--ideal (y*z, x*z*w, x^2*w, x^2*y)
I=i^2
g=map(coker gens i,coker gens I)
j=i^[2]
f=map(coker gens i,coker gens j)
prune ker Ext^1(f,R)
prune ker Ext^2(f,R)
prune ker Ext^3(f,R) -- not zero! = k(-5)
prune ker Ext^4(f,R)
prune ker Ext^3(g,R) -- not zero! = k(-5)
-----------------------
kk=ZZ/32003
R=kk[x,y,z,w,t]
i=monomialCurve(R,{1,3,4})
--i=monomialCurve(R,{2,4,7,8})
j=i^2
f=map(coker gens i,coker gens j)
prune ker Ext^1(f,R)
prune ker Ext^2(f,R)
prune ker Ext^3(f,R) 
prune ker Ext^4(f,R)
betti i
betti gens gb i
peek gb i
L=leadTerm i
rL =  gens radical ideal L -- z,y
m1=(gens ((ideal rL)^[3]))//L
j1 = ideal ((gens i)*m1)
gens gb j1
m2=(gens ((ideal rL)^[6]))//L
j2 = ideal ((gens i)*m2)
betti res j2
gens gb j2
leadTerm gens gb j2
-- they are both GB's! And regular sequences! 
-- But they are NOT the ideals we want. 
-- for example radical j1 is NOT i.
f=map(coker gens j2,coker gens j1)
prune ker Ext^1(f,R)
prune ker Ext^2(f,R) -- not zero
prune ker Ext^3(f,R)
prune ker Ext^4(f,R)

-----------------------
--The injectivity question for monomial curves in P3
L={1,3,4}
injfrob=(L,d)->(
    kk:=ZZ/32003;
    R:=kk[vars (0..#L)];
    i=gens monomialCurve(R,L);
    i1:=frob(i,d);
    i2:=frob(i,d+1);
    f:=map(coker i1,coker i2);
   {prune ker Ext^3(f,R),
    Ext^3(f,R)}
     )
inj=(L,d)->(
    kk:=ZZ/32003;
    R:=kk[vars (0..#L)];
    i=monomialCurve(R,L);
    i1:=i^d;
    i2:=i^(d+1);
    f:=map(coker gens i1,coker gens i2);
{prune ker Ext^3(f,R),
    Ext^3(f,R)}
     )
-- test K=injfrob({1,2,3},1)
-- test K=injfrob({1,2,3},2) this is of length 6, codim 3. We've chosen
-- a subscheme of length 6 by the way we chose the equations!! Probably
--3 times one fixed point plus three times the other. Indeed:
--annihilator K
--ideal (a*d, c  - b*d, b*c, b  - a*c)

injfrob({1,3,4},1)
--This is k(5). No surprise there, really, as 
--H^3_i(R)=0 but Ext^3(R/i, R)\neq 0
injfrob({1,3,4},2)
--degree 10

inj({1,2,3},2) -- already the square has a kernel, is not CM.
inj({1,2,3},1)
-----
Does the real frobenius have a kernel in char p?? 
(it must sooner or later, as the coho dim of the ideal is 0! --
     in fact, in char p it's stci.)
injfrob1=(char, L,d)->(
    kk:=ZZ/char;
    R:=kk[vars (0..#L)];
    i=gens monomialCurve(R,L);
    i1:=frob(i,char^d);
    i2:=frob(i,char^(d+1));
    f:=map(coker i1,coker i2);
    prune ker Ext^3(f,R)
     )
injfrob1(2,{1,3,4},1)
--It seems that all the frobenius maps are equal to 0! 
--Of course this is another (?) proof that the 3rd local
--coho of R is 0 (and thus the coho dim is just 2).
--------
kk=ZZ/2
R=kk[vars (0..#L)]
i=gens monomialCurve(R,L)
i:=idealfrob(i,char^d)

f:=map(coker i1,coker i2);
prune ker Ext^3(f,R)

injFrobIdeal=(i,e,d)->(
    i1:=frob(gens i,d);
    i2:=frob(gens i,d+1);
    f:=map(coker i1,coker i2);
    Ef=Ext^e(f, R);
print"";
     print Ef;
     print prune source Ef;
     print prune kernel Ef;
--   {prune ker Ef,prune source Ef,Ef }
     )
kk=ZZ/32003
R=kk[a,b,c,d]
i=intersect(ideal(a,b),ideal(b,c),ideal(c,d))
injFrobIdeal(i,2,1)


help print


