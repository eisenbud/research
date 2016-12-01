S=kk[a,b,c]

--experiments as the one below show that the the (cubic part) of
--the annihilator of a cubic form has linear resolution 
--if and only if the form is squarefree (reduced). For monomials
--one can see that this is the same as having square =m^6.


i=truncate(3, ideal fromDual map(S^1, S^{-3},matrix{{a*b^2}}))
betti res i

--which of these ideals contains a 7 generator Gorenstein ideal?
fromDual matrix{{a*b^2}}
fromDual matrix{{a*b*c}}


S = kk[x,y]
betti fromDual matrix{{x^2}}
betti fromDual matrix{{(x+y)^2}}
