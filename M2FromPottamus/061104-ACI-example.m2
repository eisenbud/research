restart
i=ideal"ac,ad,bc,bd"
ass i

i=(ideal"a,b")^3+ideal (a*c^2,c^3)
j=ideal((gens i)*random(source gens i, S^{4:-3}))
betti res j

line=gens ideal"a,b"
canon=ideal (line*random(source line, S^{3:-2}))
betti res canon
allbut=canon:(ideal line)
betti res allbut

monomialCurveIdeal(S,{1,2,4,5})
