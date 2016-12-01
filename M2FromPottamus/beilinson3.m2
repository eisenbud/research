sortedBasis = (i,E) -> (
     -- We sort the monomials of degree i in E to match
     -- the order of the columns of 'koszul(i,vars S)',
     -- where S is a polynomial ring, and E is the exterior
     -- algebra on the dual set of variables.
     -- The monomial order in E should be the default: rev lex.
     m := basis(i,E);
     p := sortColumns(m,MonomialOrder=>Descending);
     m_p)

beilinson1=(x,degx,i,S)->(
     --If x\in E=\wedge V, makes the (+/- 1) matrix of the map
     -- representing the map U^(i-degx) <-- U^i.
     --This is usually a map :\wedge^(i+1)W -->\wedge^{i+1-deg x}W
     -- except when i is large or small.
     -- NOTE: the degrees of the result are not set correctly,
     -- since beilinson is supposed to do that.
     -- NOTE 2: if degx is 0, the map is + or - mult by x,
     -- depending on the congruence of degx, mod 4.  Is this a problem?
     E := ring x;
     mi := if i < 0 or i >= numgens E then map(E^1, E^0, 0)
           else if i === 0 then id_(E^1)
	   else sortedBasis(i+1,E);
     j := i - degx;
     mj := if j < 0 or j >= numgens E then map(E^1, E^0, 0)
	   else sortedBasis(j+1,E);
     if i === 0 and j === 0 then
	  map(E^1,E^1,{{x}})
     else if i > 0 and j === 0 then
	  (vars S) * substitute(diff(diff( x, mi), transpose mj),S)
     else
         substitute(diff(diff( x, mi), transpose mj),S)
     )

U = (i,S) -> (
     --sets U(i) = U^i =  \Omega^i(i), the ith exterior power of
     the tautological subbundle on Proj S
     if i < 0 or i >= numgens S then S^0
     else if i === 0 then S^1
     else cokernel koszul(i+2,vars S) ** S^{i+2}
     )

beilinson = (n,S) -> (
     -- n: sum(E(-a_i)) --> sum(E(-b_j)) is a graded matrix over the 
     -- exterior algebra E (with generators of degree 1).
     -- The output is the corresponding map sum(U(a_i,S)) --> sum(U(b_j,S)).
     coldegs := degrees source n;
     rowdegs := degrees target n;
     mats = table(numgens target n, numgens source n,
	          (r,c) -> (
		       -- Once degrees of variables of E are -1,
		       -- The next 3 lines will have to change.
		       -- Check also: beilinson1, basis.
		       rdeg = first rowdegs#r;
		       cdeg = first coldegs#c;
		       overS = beilinson1(n_(r,c), cdeg-rdeg, cdeg,S);
		       --overS = substitute(overE,S);
		       map(U(rdeg,S), U(cdeg,S), overS)));
     if #mats === 0 then matrix(S,{{}})
     else matrix(mats)
     )

symExt=method(TypicalValue=>Matrix)
symExt(Matrix,Ring) := (m,R) ->(
     ev := map(R,ring m,vars R);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
     ans:= transpose ev(q*jn);
     --now correct the degrees:
     map(R^{(rank target ans):1} ,R^{(rank source ans):0}, ans))

tateResolution = (M,E,loTwist,hiTwist)->(
     reg := regularity M;
     bnd := max(reg+1,hiTwist-1);
     mt  := presentation truncate(bnd,M);
     n   := symExt(mt,E);
     v := numgens E;
     --adjust degrees, since symExt forgets them
     nfixed   :=  map(E^{(rank target n):v-bnd+1},
	        E^{(rank source n):v-bnd},
	        n);
     res(coker nfixed, LengthLimit=>max(1,bnd-loTwist+2))
     )

beilinsonComplex = (C) -> 
     chainComplex apply(length C, i -> beilinson(C.dd_(i+1),S))

end
restart
load "beilinson2.m2"     



kk = ZZ/32003
v = 3
S = kk[vars(26..26+v-1)]
E = kk[vars(0..v-1),SkewCommutative=>true]

beilinson1(a,1,1,S)

m1=map(E^{-0}, E^{-1,-1},{{a,b}})
betti m1
M1=beilinson(m1, S)
m2=map(E^{2:-1},E^{-2},{{a},{b}})
M2=beilinson(m2, S)
M1*M2
homology(M1,M2)
prune oo

kk = ZZ/32003
v = 5
S = kk[vars(26..26+v-1)]
E = kk[vars(0..v-1),SkewCommutative=>true]

beta=map(E^1,E^{-2,-1},{{a*b+c*d,-e}})
alpha=map(E^{-2,-1},E^{-3},{{e},{a*b+c*d}})
B=beilinson(beta,S)
A=beilinson(alpha,S)
res prune homology(B,A)
betti oo

--Horrocks-Mumford
alpha1=matrix{{c*d,d*e,e*a,a*b,b*c},{b*e,c*a,d*b,e*c,a*d}}
beta=map(E^5,E^{-2,-2}, transpose alpha)
alpha=syz beta
B=beilinson(beta,S)
A=beilinson(alpha,S)
res prune homology(B,A)
betti oo

target M1
source M1
vars E
betti m1

kk = ZZ/32003
v = 4
S = kk[vars(26..26+v-1)]
E = kk[vars(0..v-1),SkewCommutative=>true]
-- test beilinson1

beilinson1(a*b+a*c,2,3)
beilinson1(a*b+a*c,2,2)
beilinson1(a*b+a*c,2,1)
beilinson1(0_E,2,3)
beilinson1(0_E,2,2)
beilinson1(0_E,2,1)
beilinson1(2_E,0,2)
beilinson1(a+b+c,1,2)
beilinson1(a+b+c,1,1)

-- test beilinson
F = beilinson(map(E^{-4}, E^{-6}, {{a*b+a*c}}),S)
F = beilinson(map(E^{-2}, E^{-4}, {{a*b+a*c}}),S)
F = beilinson(map(E^{-1}, E^{-3}, {{a*b+a*c}}),S)
F = beilinson(map(E^{0}, E^{-2}, {{a*b+a*c}}),S)
F = beilinson(map(E^{1}, E^{-1}, {{a*b+a*c}}),S)
F = beilinson(map(E^{2}, E^{0}, {{a*b+a*c}}),S)
F = beilinson(map(E^{3}, E^{1}, {{a*b+a*c}}),S)

F = beilinson(map(E^1, E^{-2,-1}, {{a*b+a*c, a+b+c}}),S)
F = beilinson(map(E^{-1}, E^{-3,-2}, {{a*b+a*c, a+b+c}}),S)
F = beilinson(map(E^{-2}, E^{-4,-3}, {{a*b+a*c, a+b+c}}),S)
F = beilinson(map(E^{0,-1}, E^{-2,-3}, {{a*b+a*c, a*b*d}, {a+b+c+d, c*d}}),S)

-- Do these compose to zero?

C = res(coker matrix{{a}},LengthLimit=>8)
C = res(coker matrix{{a*b-c*d,a+b+c+d}},LengthLimit=>4)
beilinsonComplex C

-- Tate resolution
C = tateResolution(S^1,E,-2,2)
betti C
beilinsonComplex C

-- Tate resolution
C = tateResolution(S^1/(S_0,S_1,S_2),E,-2,2)
beilinsonComplex C

