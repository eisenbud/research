restart
kk= QQ[i]/(ideal i)^2
S = kk[a,rx, ix]
x = rx+i*ix

restart
kk= QQ
S = kk[a,x]
f = (x+(1/2))^2+x*(x+1)*(x-a)-(1/4)
decompose ideal f
primaryDecomposition ideal f
