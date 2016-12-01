restart
kk=ZZ/32003
n=2
S=kk[vars(0..n-1)]
i=trim ideal((vars S)^[2] | random(S^1,S^{-2}))

i = ideal"a2,b2,c2,d2,e2,ab+cd+ae+be"
H=Hom(i,S^1/i)
degree H
report gens i
