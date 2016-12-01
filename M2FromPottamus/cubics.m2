--compute the linear series of plane curves with assigned multiple basepoints etc
input "points.m2"
p2=kk[x..z]
pointsmat=id_(p2^3)|random(p2^3,p2^3)
idealpoints=points(pointsmat)
mults={2,2,2,1,1,1}
ideal((vars p2)*syz transpose (pointsmat_{3}))
pointsmat_{3}

idealOfMultiplePoints=(pointsmat, mults)->(
     R := ring pointsmat;
     l:= min(rank source pointsmat, #mults);
     listOfIdeals := apply(l , 
	  p -> (ideal((vars R)*syz transpose (pointsmat_{p})))^(mults_p));
     intersect listOfIdeals
     )
i=idealOfMultiplePoints(pointsmat, mults)

curveOfClass = (pointsmat, d, mults) -> (
     i=idealOfMultiplePoints(pointsmat, mults);
     ((gens i) * random(source gens i, (ring pointsmat)^{-d})))
curveOfClass(pointsmat, 4, mults)

p3=kk[a,b,c,d]

cubicSurface = (S, pointsmat)->
kernel(map(p2,S, gens idealOfMultiplePoints(pointsmat,toList (6:1))))
toList (6:1)
j=cubicSurface(p3, pointsmat)

idealCurveOfClass = (S, pointsmat, d, mults)->(
R := p2/ideal(curveOfClass(pointsmat, d, mults));
kernel(map(R, S , substitute((gens idealOfMultiplePoints(pointsmat,toList (6:1))),R))))

i=idealCurveOfClass(p3, pointsmat, 4, mults)
i/j

lineBundleOfClass = (S, pointsmat, d, mults) ->(
     i:=idealCurveOfClass(S, pointsmat, d, mults);
     j:=cubicSurface(S, pointsmat);
     prune Hom(i/j,S^1/j))
     
M1= presentation lineBundleOfClass(p3, pointsmat, 1, toList(6:0))

F1= prune image (M1**(p3/j))
F=coker (presF=lift(presentation F1,p3))

res transpose presentation F1
(res transpose presentation F1).dd_2
M1' = lift(transpose (res coker transpose presentation F1).dd_2, p3)
betti trim minors (1, M1'*presF)


L3=lineBundleOfClass(p3, pointsmat, 4, mults)
M3' = presentation L3

H=Hom(L3,F)
f = homomorphism H_{4}
L2= coker mingens image presentation coker f
M2=presentation L2

M1'*M3*M2

betti res L
M3= (extend(res L2,res F, id_(target M2)))_1

betti trim minors (1, M1'*((res L2).dd_1)*M3)

betti trim minors (1, M1'*M2*M3)

betti res minors(1,M2*M3*M1')

betti syz (transpose (M2*M3)**(p3/j))






