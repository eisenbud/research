--Example of a prime ideal that does not satisfy the chain condition
--with respect to a suitable set of variables, order.
load "monom.m2"
restart
kk=ZZ/32003
--R=kk[x,y,z,t,a,b,c] --For revLex
R=kk[z,t,y,x,a,b,c, MonomialOrder=>Lex]
i=ideal(x*z - a^2, y*z - b^2, t*z - c^2)
test=x*y*z*t*a*b*c
i1=i:test --equal to i, so this is lattice
--As a toric ideal:
B=matrix{{1,0,1,0,-2,0,0},{0,1,1,0,0,-2,0},{0,0,1,1,0,0,-2}}
A=transpose gens ker B
--since B has a 3x3 identity minor, the lattice is saturated, the
--ideal is toric.
dim(R/i) --4; a complete intersection.
dim singularLocus (R/i) --3 Not normal!
ini=ideal leadTerm gens gb i
ass ini
--F=map(R,R,matrix{{x,y,z,z-t,a,b,c}}) -- use this map with the revlex ordering
F=map(R,R,matrix{{z,z-t,y,x,a,b,c}}) --use this map with the lex ordering
--F=map(R,R,matrix{{x,y,z,t,a,b,c}})
j=F i
inj=ideal leadTerm gens gb j
ass inj -- does NOT satisfy chain condition in revLex, but DOES in Lex
F=map(R,R,matrix{{x,y,z,z-t,a,b,c}})
G=map(R,R,random(R^1,R^{7:-1}))
gini=ideal leadTerm  gens gb G i
ass gini --- just (x,y,z)
imodabc=ideal(x*z , y*z, t*z )
ass imodabc

------Generalize! (Serkan 8/17/99)
--complete intersection of dimension n+2, codim n+1.
--primes of the initial ideal in the changed variables are all the same
--codim (n+1) but one, which has codim 2n+1.
-- presumably the same trick as above would give lex examples.
restart
kk=ZZ/32003
n=4
a=a
R=kk[x_0..x_(n-1),y,t,a_0..a_n] --For revLex
i=ideal((matrix table(1,n,(i,j)->(x_j)*y-(a_j)^2))|matrix{{y*t-(a_n)^2}})
--dim singularLocus (R/i) -- singular in codim 1, along the plane (a_0,..,a_n,y).
ini=ideal leadTerm gens gb i
ass ini
F=map(R,R,matrix{{x_0..x_(n-1),y,y-t,a_0..a_n}})
j=F i
inj=ideal leadTerm gens gb j
L=ass inj; -- does NOT satisfy chain condition in revLex, but DOES in Lex
# L
print L_0
scan(# L, i->print L_i)
