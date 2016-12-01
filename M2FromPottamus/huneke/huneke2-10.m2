kk=ZZ/32003
R=kk[a,b,c,d,MonomialOrder=>Lex]
i=random(R^1, R^{-3,-3})

--i=ideal(a^2+b^2+c^2+d^2, a*b-c*d)
gi=gens gb i
L=leadTerm gi
res coker L
E=Ext^3(coker L,R^1)
decompose ideal L

R2=kk[s,t,u]
R4=kk[x_0..x_4]
f=map(R2,R4,matrix{{s^2,t^2,u^2-s*t,s*u,t*u}})
i=kernel f
betti res i
substitute(i, {x_1=>0})
--------------
restart
kk=ZZ/32003
test = L ->(
i=monomialCurve(S,L);
--betti res i;
n=numgens source vars S;
--ch=map(S,S,random(S^1,S^(toList(n:-1))));
ch=map(S,S,random(S^1,S^{-1,-1})|(vars(S))_{0..n-3});
j=leadTerm ch i;
betti res coker j
--leadTerm ch i
)
S=kk[a,b,c,d,e,MonomialOrder=>Eliminate 1]
test{1,3,11}
codim Ext^3(coker j, S^1)
j

restart
--S=kk[a,b,c,d,e,f,MonomialOrder=>Lex] --Eliminate 1]
S=kk[a,b,c,d,e,f,MonomialOrder=>Eliminate 1]
n=numgens source vars S
R=kk[a,b,c]
f=map(R,S,matrix{{a^3,a^2*b,a*b*c,c^3,a*c^2,b^3}})
i=kernel f     
use S
m=genericSymmetricMatrix(S,a,3)
i=minors(2,m)
--ch=map(S,S,random(S^1,S^(toList(numgens source vars S:-1))));
ch=map(S,S,random(S^1,S^{-1})|(vars(S))_{0..n-2})
j=leadTerm ch i
betti res coker j
codim Ext^5(coker j, S)
annihilator Ext^5(coker j, S)
codim Ext^4(coker j, S)
annihilator Ext^4(coker j, S)

--
restart
S=kk[vars(0..6),MonomialOrder=>Eliminate 4] --Lex]
f1=a^3+b^3+c^3+d^3+e^3+f^3+g^3
f2=a*b*c+d*e*f
f3= a*b^2+g^2*d
i=ideal(f1,f2,f3)
--codim i
j=leadTerm i
betti res coker j
codim Ext^4(coker j, S)
i4=annihilator Ext^4(coker j, S)
decompose i4
codim Ext^5(coker j, S)
i5=annihilator Ext^5(coker j, S)
decompose i5

--------------------
S=kk[x_1..x_8,MonomialOrder=>Lex]
i=ideal(x_2*x_1*x_7-x_6*x_3,x_3*x_1*x_7-x_2^2,x_7*x_1*x_7-x_5*x_8)
gi=gens gb i
I=ideal gi
show I
leadTerm I
codim i

-------------------------------
restart
S=kk[x_1..x_8,MonomialOrder=>Lex]
R=kk[a..d]
i=ideal vars R
m=((gens i^3)_{0..3,6..7,9})|((gens i^3)_{4}+(gens i^3)_{5})
f=map(R,S,m)
j=kernel f

ass  leadTerm gens j
-------------------------------

R=kk[a,b,c,d,e,u,v,w,x,t,MonomialOrder=>Eliminate 1]
i1=ideal(a*u+b*t, b*v+c*t, c+t)
i2=ideal(d*w+e*t, e*x+c*t, c-t)
i=intersect(i1,i2)
p=a*b*c*d*e*t*u*v*w*x
i == i:p
mingens i
scan(ass ideal leadTerm gens gb i, print)
-- all the vars are nzd mod i BUT its initial ideal does
-- not satisfy the Hosten-Thomas chain thm (in the given order).


------------------------------------------------------
--but we no longer have a counterexample (it seems) if
-- we change the order:
R=kk[t,a,b,c,d,e,u,v,w,x,MonomialOrder=>Eliminate 1]
i1=ideal(a*u+b*t, b*v+c*t, c+t)
i2=ideal(d*w+e*t, e*x+c*t, c-t)
i=intersect(i1,i2)
p=a*b*c*d*e*t*u*v*w*x
i == i:p
mingens i
scan(ass ideal leadTerm gens gb i, print)
-------------------------
------------------------
-------------------------------
--,MonomialOrder=>Eliminate 6] ----,MonomialOrder=>Lex]
restart
load "/home/de/m2/monom.m2"
R=kk[a,b,c,d,e,s,t]
i1=ideal(a*s+b*t, b*s+c*t, c+t)
i2=ideal(d*s+e*t, e*s+c*t, c-t)
i=intersect(i1,i2)
i=saturate(i,s)
show i
mingens i
scan(ass ideal leadTerm gens gb i, print)
j=transpose gens gb i
transpose leadTerm gens gb i
-- all the vars are nzd mod i BUT its initial ideal does
-- not satisfy the Hosten-Thomas chain thm (in the given order).
scan( ass gin mingens i,print)
-- same in gin

--------------------------------------
restart
load "/home/de/m2/monom.m2"
R=kk[a,b,c,d,e,s,t,MonomialOrder=>Lex]
i1=ideal(a*s+b*t, b*s+c*t, c+t)
i2=ideal(d*s+e*t, e*s+c*t, c-t)
i=intersect(i1,i2)
i=saturate(i,s)
show i
mingens i
F=map(R,R,matrix{{a,b,c,d,e,1_R,t}})
--set s=1 and then take the assoc primes of the initial ideal:
scan(ass ideal F(leadTerm gens gb i), print)
-- all the vars are nzd mod i BUT its initial ideal does
-- not satisfy the Hosten-Thomas chain thm (in the given order).
j=transpose gens gb i
transpose leadTerm gens gb i
scan( ass gin mingens i,print)
-- same in gin






