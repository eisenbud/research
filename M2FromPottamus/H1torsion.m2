restart
kk=ZZ/101
S=kk[x,y,z]
i1=ideal(x^3,y^3)
i2= (ideal vars S)^4
i=intersect(i1, i2)
koszul(1,gens i)
koszul(2, gens i)
h1=prune homology(koszul(1,gens i), koszul(2, gens i))
betti res h1
hilbertFunction(toList (1..10),h1)
toList(1..10)
help hilbertFunction
apply(10, i->hilbertFunction(i,h1))
j=saturate i
apply(10, e->hilbertFunction(e,(module j)/module (i)))
(module j)/
i*module (j)
