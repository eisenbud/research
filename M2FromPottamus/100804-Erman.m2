loadPackage "BoijSoederberg"

pureBetti{0,1,3,5}
pureBetti{0,1,3,6}

pureBetti{0,2,4,5}
viewHelp BoijSoederberg
restart
S=kk[x,y,z]
M=coker random(S^11,S^{15:-1,10:-2})
betti res M
E = S^11/(ideal(x^3,y^3,z^3))
f=map(E,S^{11:-4}, random(S^11,S^{11:-4}))
res image f
betti oo



