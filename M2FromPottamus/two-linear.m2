kk=ZZ/32003
S=kk[a..f]
i=
intersect(ideal(a,b),
     ideal(b,c),
     ideal(c,d),
     ideal(d,e),
     ideal(e,f))
betti res i

i=intersect(ideal(a,b),
     ideal(b,c),
     ideal(c,d),
          ideal(d,e))
betti(F= res i)
codim i
F.dd_1
