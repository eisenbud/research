genericArrangement= (S,n)->(
     --Makes a random product of n linear forms in S
     product apply(n, i->random(1,S))
     )
p=32003
kk=ZZ/p
S=kk[x,y,z]
--Q=ideal genericArrangement(S,7)
Q=ideal (x*y*z*(x+y+z)) --not free except char 2
jQi=ideal transpose jacobian Q
F=res jQi
F.dd
(gens Q )// (gens jQi)
--in char 2, Q is not contained in jQi!
-- so strictly speaking we need to look at the image of jQi in S/Q
S^1/Q
G=map(S^1/Q,S^{-3,-3,-3},gens jQi)
kernel G
--four gens instead of 3!


--NONE of the generic arrangements from \ell+1 hyp 
--on seem to be free in large char.
--Q=ideal (x*y*z*(x+y+z)*(x+2*y+3*z)) --free
--Q=ideal (x*y*z*(x+y+z)*(x+2*y+3*z)*(7*x+5*y+z))-- free

Q=ideal genericArrangement(S,5)
jQi=ideal transpose jacobian Q
jQs=saturate jQi
betti res jQs
betti res jQi
M=module jQs/(module jQi)
betti res trim M

F=res jQi
F.dd
degree coker transpose F.dd_3
res coker transpose F.dd_3
