kk=ZZ/32003
S=kk[a..f]
m=matrix{{a,b,c},
     	 {b,d,e}}
i1=minors(2,m)+ideal(f)    
i2=ideal(a,b,d)
betti (F=res (I1=intersect(i1, i2)))
I1
i3=ideal(a,b,c)
betti (F=res (I2=intersect(i1, i3)))
I2
degree(i1+i2)
dimension