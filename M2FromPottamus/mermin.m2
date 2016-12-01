kk=ZZ/101
S=kk[a,b,c,d,e]
i=ideal"a2,b2,c2,d2,e2,ab,ac,ad,ae,bc,bde"
betti res i
hf(0..5,S^1/i)


S=kk[a,b,c,d,Degrees=>{{1,1,0,0,0},{1,0,1,0,0},{1,0,0,1,0},{1,0,0,0,1}},MonomialOrder => Lex]
i= (ideal vars S)^3
betti (FF=res i)
FF.dd_3
help leadTerm
leadTerm FF.dd_3
for t from 1 to 4 do print  mingens minors(1,leadTerm FF.dd_t)for t from 1 to 4 do print  mingens minors(1,leadTerm FF.dd_t)


restart
load "randomIdeal.m2"
S=kk[a,b,c,d,
     Degrees=>{{1,1,0,0,0},{1,0,1,0,0},{1,0,0,1,0},{1,0,0,0,1}},
     MonomialOrder => {Position =>Up,Lex}]
--i=ideal"bd2, bcd, ac2, a4d"
i=ideal"a4d,bd2, bcd, ac2"
i=ideal mingens i
leadTerm i
FF=res coker gens i
for t from 1 to 4 do print  mingens minors(1,leadTerm gb FF.dd_t)
FF.dd_1
FF.dd_2
viewHelp leadTerm
leadTerm gb image FF.dd_2
viewHelp sort
sort (gens i, MonomialOrder => Descending)
--sort (gens i, DegreeOrder => Descending) this does NOT give the right thing.
d2=syz sort (gens i, MonomialOrder => Descending)
sort(d2, MonomialOrder => Descending)
sort (d2, DegreeOrder => Descending)
d3=syz sort (d2, DegreeOrder => Descending)
leadTerm d2
leadTerm d3

