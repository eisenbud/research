--The ring T/(x^a, y^b, z^c, x+y+z) = S/(x^a, y^b, (x+y)^c).
--WLOG a,b <= c <= a+b-1 --- else the problem reduces to a ci.
--1. There's a relation (*y^(c-a+1), **, x+?) of degree c+1.
--2. It follows from the row degrees that the other relation 
--has degree a+b-1.  The general degree formula for a det ideal
--is ab-(a+b-c-1). The H funct is given from the resolution.

S=kk[x,y]
a=3;
b=3;
c=3;
g=(x+y)^c%gb(ideal (x^a, y^b))
i=matrix{{x^a, y^b, g}}
(F=res coker i).dd_1
(F=res coker i).dd_2
betti F

T=kk[u,v,w]
j=(ideal(u^a,v^b,w^c)):(ideal(u+v+w))
res prune(T^1/j)
