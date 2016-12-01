n=4
S=kk[vars(0..n-1)]
t= (I,j)-> (
     F:= res (S^1/I);
     (max degrees F_j)#0)
bound = (I,j,k)->(
     k*t(I,j)+t(I,1)*(n-1-k*(j-1))-n)
test =(I,j,k)-> bound(I,j,k)-regularity(S^1/(I^k))
--Conj: this is positive for k\leq (n-1)/(j-1)

m=2
i= (ideal(a^m, b^m, c^m,d^m)): ideal(a^(m-1)+b^(m-1)+c^(m-1)+d^(m-1))
test(i,2,2)
--- gets 2

m=3
i= (ideal(a^m, b^m, c^m,d^m)): ideal(a^(m-1)+b^(m-1),c^(m-1)+d^(m-1))
test(i,2,2)

betti res i
betti res i^2


kk=ZZ/101     
S=kk[x,y]
d=10
i=ideal(x,y)*ideal(x^d,y^d)
i=ideal(x^11, y^11)+ideal random(S^1, S^{-11})
for n from 1 to 11 do (
     print regularity (i^n))

RI=reesClassic( i, i_0)
peek betti res RI

--So the power that's needed for ideal(x,y)*ideal(x^d,y^d) is the d-1
--and the highest "y-twist" is 9 -- occuring in the 3rd, 4th, 5th spots.

--But for the three elements, degree 11, the power needed is 8 and the 
--highest y-twist, already in the first spot (gen of RI) is 11

--(of course any three elements of degree d defined a degree d plane curve,
--so the equation will show up in the first step with y-twist d) Sim, 4 polys
--of degree d in 3 vars gives y-twist at least d^2.

kk=ZZ/101     
S=kk[x,y,z]
d=5
i=ideal(x,y)*ideal(x^d,y^d)
i=ideal(x^d, y^d, z^d)+ideal random(S^1, S^{-d})
for n from 1 to d do (
     print regularity (i^n))

RI=reesClassic( i, i_0)
peek betti res RI

--Does the intersection of a quad and two cubics in P5 have trisecants that
--fill a hypersurface?

S=kk[a..f]
Q=ideal"ab+cd+ef"
F1=ideal"a3+b3+c3+d3+e3+f3"
F2=ideal random(S^1,S^{-3})
I=Q+F1+F2
R=S/I
L=ideal random(R^1,R^{4:-1})
mR=ideal vars R
time rank source compress(gens(mR^9) %  gb (L^8))
T=kk[A..D]
i=ker map(R,T,gens L)
G=gens i;
J=ideal diff(vars T,diff(vars T,G));
codim J
--DD=decompose J
