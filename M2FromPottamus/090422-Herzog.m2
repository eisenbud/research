restart
load "randomIdeal.m2"
S=kk[a,b,c,d,
     Degrees=>{{1,1,0,0,0},{1,0,1,0,0},{1,0,0,1,0},{1,0,0,0,1}},
     MonomialOrder => {Position =>Up,Lex=>4}]
viewHelp MonomialOrder
--i=ideal"bd2, bcd, ac2, a4d"
i=ideal"a4d,bd2, bcd, ac2"
i =ideal sort (gens i, MonomialOrder => Descending)
i=ideal mingens i
leadTerm i
FF=res coker gens i
for t from 1 to 4 do print  mingens minors(1,leadTerm gb FF.dd_t)
viewHelp res
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

