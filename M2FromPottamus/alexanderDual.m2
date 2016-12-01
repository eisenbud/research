kk = ZZ/101
S = kk[a,b,c,d]
loadPackage "randomIdeal"
loadPackage "MonomialIdeals"
viewHelp randomMonomialIdeal 
i = ideal"a3,b3,c3,d3,ab,b2c,cd2"
j = ideal"a3,b3,c3,d3"
betti res i
betti res (j:i)

matrix"a2
restart
S = kk[vars(0..14)]
M=genericMatrix(S,S_0,3,5)
betti res coker leadTerm gens gb minors(3,M)

