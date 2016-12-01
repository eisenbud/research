S=kk[a..f]
i=ideal(b*c,c*e,c*f, a*f, b*f, d*b)
betti res i
E=kk[a..f, SkewCommutative =>true]
ie=substitute(i,E)
annihilator ie
j=substitute(oo, S)
F=res j
F.dd_2
F.dd_1


S=kk[a..f]
i=ideal(a*d,b*d,a*c, e*f,e*d,f*b,f*a)
betti res i
E=kk[a..f, SkewCommutative =>true]
ie=substitute(i,E)
annihilator ie
j=substitute(oo, S)
F=res j
F.dd_2
F.dd_1
