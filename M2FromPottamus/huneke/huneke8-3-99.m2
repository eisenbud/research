R=kk[x,y,r,s]
i=ideal(x*r+y*s, x*y,x^2*r,y^2*s)
S=R/i
X=map(S^1,S^{-1},{{x}})
betti (XX=res coker X)
XX.dd
