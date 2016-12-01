S=kk[a,b,c]
i=(n,d)->(
     --n generic forms of degree d
     ideal(random(S^1,S^{n:-d})))
betti res (i(3,2))^2
