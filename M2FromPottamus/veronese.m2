restart
kk=ZZ/32003
S=kk[a..f,A..F]
m=genericSymmetricMatrix(S,a,3)
m
i=minors(2,m)
betti res i
betti i
j = trim i
FF=res j

----------
--five general forms cut out the Vero scheme-theoretically -- though the first five minors don't. 
--(The five conic tangency conditions cut out the double of the Vero, 
--and presumably do it scheme-theoretically.)
f = map(S^6, S^{-2}, transpose gens j)
g = ideal(random(S^1, S^6)*f)
rand5 = ideal(random(S^5, S^6)*f)
codim((ideal (gens j)_{0..4}):(ideal j_5))
codim (rand5:(ideal j_5))
------------
i6= ideal i_5
i5:i6

AA=(vars S)_{6..11}
F=AA*FF.dd_2
aa=(vars S)_{0..5}
G=contract(transpose aa, F)
--rows of G correspond to vars a..f; cols correspond to the 8 relations.
codim minors(6, G) -- 0
codim minors(5, G) -- 3
codim minors(4, G) -- 3
codim minors(3, G) -- 6
codim minors(2, G) -- 6
codim minors(1, G) -- 6

--So every generalized row of the matrix has a 3-dim'l space of linear
--forms.

--Same game for the scroll S(2,2)
restart
kk=ZZ/32003
S=kk[a..f,A..F]
--m=genericSymmetricMatrix(S,a,3)
m=matrix{{a,b,d,e},{b,c,e,f}}
i=minors(2,m)
j= ideal presentation prune coker gens i
betti (FF=res j)
AA=(vars S)_{6..11}
F=AA*FF.dd_2
aa=(vars S)_{0..5}
G=contract(transpose aa, F)
--rows of G correspond to vars a..f; cols correspond to the 8 relations.
codim minors(6, G) -- 1
codim minors(5, G) -- 1
codim minors(4, G) -- 4
codim minors(3, G) -- 6
codim minors(2, G) -- 6
codim minors(1, G) -- 6

--Same game for the scroll S(1,3)
restart
kk=ZZ/32003
S=kk[a..f,A..F]
--m=genericSymmetricMatrix(S,a,3)
m=matrix{{a,b,c,e},{b,c,d,f}}
i=minors(2,m)
j= ideal presentation prune coker gens i
betti (FF=res j)
AA=(vars S)_{6..11}
F=AA*FF.dd_2
aa=(vars S)_{0..5}
G=contract(transpose aa, F)
--rows of G correspond to vars a..f; cols correspond to the 8 relations.
codim minors(6, G) -- 1
codim minors(5, G) -- 1
codim minors(4, G) -- 4
codim minors(3, G) -- 6
codim minors(2, G) -- 6
codim minors(1, G) -- 6

--so this distinguishes the veronese resolution from the scrolls!


--Same game for the cone over the rational normal curve S(0,4)
restart
kk=ZZ/32003
S=kk[a..f,A..F]
--m=genericSymmetricMatrix(S,a,3)
m=matrix{{a,b,c,d},{b,c,d,e}}
i=minors(2,m)
j= ideal presentation prune coker gens i
betti (FF=res j)
AA=(vars S)_{6..11}
F=AA*FF.dd_2
aa=(vars S)_{0..5}
G=contract(transpose aa, F)
--rows of G correspond to vars a..f; cols correspond to the 8 relations.
codim minors(6, G) -- 0
codim minors(5, G) -- 1
codim minors(4, G) -- 3
codim minors(3, G) -- 6
codim minors(2, G) -- 6
codim minors(1, G) -- 6


-------------
-- with Huneke and Ulrich, 9/24/02

S=kk[a,b,c,d]
i=ideal(a^2*b, a^2*c, a*c^2, b*c^2)
betti res i
betti res i^2
isGenerated gens i
j=ideal(a^2*b, a^2*c, a*c^2, b*c^2, a^2*d)
betti res j
betti res j^2

i=ideal(a^3, a^2*b, a*b^2, b^3, a*b*c)
betti res i
betti res i^2
i=ideal(a^3, a^2*b, a^2*c, a*c^2, a^2*d)
betti res i
betti res i^2

check = i->(
     print betti res i;
     print betti res i^2)
check i
i=ideal(a^3, a^2*b, a*b*c, b*c^2, a*b*d)
check i
S=kk[a,b,c,d,e]
i=ideal(b^2, a*b, b*c, c^2, b*d)
check i

--The following fails the generation conjecture (though the 
--square is linearly presented.
S=kk[a,b,c,d]
i=ideal(a^2*b, a^2*c,a*c^2, c^2*d, a*c*d)
codim i
check i
isGenerated gens i

i=ideal(a^3, a^2*b, a^2*c,a*c^2, b*c^2, c^3, a^2*d, a*c*d, d*c^2)
check i

-------
kk=ZZ/2
S=kk[a,b,c]
i=ideal(a^4-b^4, b^4-c^4, a^2*b^2, a^2*c^2, b^2*c^2)
m=ideal(vars S)
j=m*i
check j

restart
S=kk[a,b,c,d,e]
i=ideal(a^2-b^2, b^2-c^2,c^2-d^2,d^2-e^2,
     a*b, a*c, a*d, a*e, b*c, b*d, b*e, c*d, c*e, d*e)
betti res i

i2=ideal frobPower(gens i, 2)
betti res i2
LP=i->(
     F:=res i;
     d:= max (degrees F_2)_0;
     truncate(d-1, i))
ilin=LP i2

betti res ilin
betti res ilin^2
betti res ilin^3

--
restart
kk=ZZ/2
S=kk[a,b,c,d]
i1=ideal(a^3-b^3,b^3-c^3,c^3-d^3)
i=i1+ ideal(a*b*c, b*c*d, c*d*a, d*a*b)
betti res i
i2=ideal frobPower(gens i, 2)
betti res i2
LP=i->(
     F:=res i;
     deg:= max (degrees F_2)_0;
     truncate(deg-1, i))
ilin=LP i2
j=ideal mingens truncate(11,i2)
betti res j
betti res j^2
betti res ilin^3

--------
S=kk[a,b,c]
i=ideal(a^3*b^3, a^2*b^3*c, a^2*b^2*c^2, a*b^2*c^3, b^3*c^3, a^3*b*c^2, a^3*c^3)
betti res i
betti res i^2
isGenerated gens i

restart
S=kk[a,b,c,d,e]
m=matrix{{a,b,0,0},{0,c,b,0},{0,a,0,c}}
m=matrix{{a,d,0,0,0,0,0},{0,a,b,0,0,0,0},{0,0,a,c,0,0,0},
          {0,0,0,d,c,0,0},{0,0,c,0,0,b,0},{0,0,d,0,0,0,e}}

m=matrix{{a,d,0,0,0,0,0},{0,a,b,0,0,0,0},{0,0,a,c,0,0,0},
          {0,0,0,d,c,0,0},{0,0,c,0,0,b,0},{0,0,0,0,0,d,b}} n=transpose
m i=minors(6, n) codim i codim minors(5,n) 
betti res i betti res i^2


