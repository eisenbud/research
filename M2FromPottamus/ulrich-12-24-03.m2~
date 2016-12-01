restart
kk=ZZ/32003
S=kk[a,b,c]
koszul(3, vars S)
koszul(3, gens(ideal(a^2,a*b,b^2)))
i=ideal(a^3, b^4)

linPres = I-> truncate(max flatten flatten degrees syz gens i-1, i)

j=linPres I

help HH
H1= j->prune HH(koszul(1, gens j),koszul(2, gens j))
H2= j->prune HH(koszul(2, gens j),koszul(3, gens j))

R=kk[a,b,c]
koszul(3,gens ideal(a^2,a*b,b^2))

m=ideal(a,b)
M1=H1 (m^4)
M2=H2 (m^4)

hilbertFunction(9,M2)
hilbertFunction(5,M1)
hilbertFunction(1,R^1/(m^4))

