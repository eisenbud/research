--examples where the sort of polarization family Sorin and Klaus suggest
--is not flat

S=kk[x,z,y_1..y_3]
i1=intersect(
     ideal(x,y_1),ideal(x,y_2),ideal(y_2,z))
i2=intersect(
     ideal(x,y_1),ideal(x,y_2),ideal(y_3,z))
betti res i2
betti res i1

i1=intersect(
     ideal(x,y_1),ideal(y_1,z))
i2=intersect(
     ideal(x,y_1),ideal(y_2,z))
betti res i2
betti res i1
