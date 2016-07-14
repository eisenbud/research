restart
needsPackage "ReesAlgebra"
kk = ZZ/32003
S = kk[u,v,q,x,y,z]
i = ideal"u11,v11,u2q9+v2x9+uvqy8+uvxz8"
betti res i
time (A = reesAlgebra i) -- 212 sec in char 32003; 28 sec in char 2
time (PA = ideal presentation A);
betti (PA, Weights =>{1,1})
(T,g) = flattenRing(ring presentation A)
degrees vars T
T' = kk[w_0,w_1,w_2, u,v,q,x,y,z,Degrees=>{3:{12},6:{1}}]
h = map(T',T)
P'A = ideal (h*g) gens PA;
isHomogeneous  P'A
T1 = kk[w_0,W_0,w_1,W_1,w_2,W_2, u,v,q,x,y,z]
f = map(T1,T',{w_0*W_0^11,w_1*W_1^11,w_2*W_2^11,u,v,q,x,y,z})
I = ideal f gens P'A;
betti I -- max degree is 417
assert(degree I  == 375)
assert(codim I == 2)

--alternate, "direct" computation:
kk = QQ
S = kk[u,v,q,x,y,z]
i = ideal"u11,v11,u2q9+v2x9+uvqy8+uvxz8"
T = S[t]
it = t*sub(i,T)
R =S[w_0,w_1,w_2,Degrees =>{3:{12}}]
time (I = ker map (T,R,gens it));
T1 = kk[w_0,W_0,w_1,W_1,w_2,W_2, u,v,q,x,y,z]
f = map(T1,R,{w_0*W_0^11,w_1*W_1^11,w_2*W_2^11,u,v,q,x,y,z})
I1 = ideal f gens I;
betti I1 -- max degree is 417
assert(degree I1  == 375)
assert(codim I1 == 2)
betti res I1
