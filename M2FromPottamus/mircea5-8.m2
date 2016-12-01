--The map from Ext of an unmixed monomial ideal to the local cohom
--need not be mono!

kk=ZZ/101
R=kk[x,y,z,w]
i1=ideal(x,y)
i2=ideal(x^2,z)
i3=ideal(y,w)
i=intersect(i1,i2,i3)
R^1/i
f=map(R^1/i,R^1/i^[2])
prune ker Ext^3(f,R) -- NONZERO
