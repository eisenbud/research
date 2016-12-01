symbPower = (I, d) ->(
L:=decompose I;
intersect apply(L, i->i^d))

randomProducts = (L, n) -> (random first entries gens product(L/ideal))_{1..n}

isPower  = method()
isPower(ZZ,Ideal) := (d,I) ->(0 == compress (gens(J=symbPower(I,d))%I^d))
isPower(List) := L ->(
     bigHeight := max(L/codim);
     I := intersect apply(L, i ->i);
     J:=intersect apply(L, i->i^bigHeight);
     0 == compress ((gens J)%( I^bigHeight))
     )
isPower(ZZ, List) := (d,L) ->(
     bigHeight := max(L/codim);
     I := intersect apply(L, i ->i);
     J:=intersect apply(L, i->i^d);
     0 == compress ((gens J)%( I^d))
     )
     
///
I = monomialIdeal "xy,xz,yz"
symbPower(I,2)
///

bigHeight = method()
bigHeight List := L -> max(L/codim)
bigHeight Ideal := I -> bigHeight decompose I

end
restart
needsPackage "RandomIdeal"
load "points.m2"
load "symbPower.m2"

kk= ZZ/101
m = 4
S=kk[x_1..x_m,y_1..y_m,z_1..z_m]
L = {toList(x_1..x_m),toList(y_1..y_m), toList(z_1..z_m)}

time for m from 1 to 1000 do(
I=monomialIdeal randomProducts(L, 15);
M = decompose I;
--print M;
if isPower(2,M) then (
     print bigHeight M;
     if isPower(3,M) then
     print toString I)
)
)
I = monomialIdeal (x_1*y_3*z_1,x_1*y_4*z_1,x_1*y_2*z_2,x_2*y_2*z_2,x_3*y_2*z_2,x_4*y_2*z_2,x_3*y_2*z_3,x_1*y_3*z_3,x_3*y_3*z_3,x_2*y_1*z_4,x_1*y_2*z_4,x_2*y_2*z_4,x_4*y_2*z_4,x_1*y_3*z_4,x_4*y_3*z_4)
bigHeight I
codim I
time isPower(7,decompose I)
betti res I

I = monomialIdeal (x_3*y_1*z_1,x_4*y_1*z_1,x_2*y_3*z_1,x_1*y_2*z_2,x_2*y_2*z_2,x_4*y_2*z_2,x_2*y_3*z_2,x_4*y_3*z_2,x_1*y_1*z_3,x_3*y_1*z_3,x_2*y_3*z_3,x_1*y_4*z_3,x_4*y_4*z_3,x_2*y_3*z_4,x_3*y_3*z_4)
bigHeight I
codim I
for p from 3 to 7 do(
print p;
time print isPower(p,decompose I))
betti res I



I=monomialIdeal randomProducts(L, 10)
d = codim I
time J=symbPower(I,d)
transpose compress((gens J) % (I^d))

codim I
toString I
transpose gens I
I=monomialIdeal (x_2*y_1*z_1,x_4*y_1*z_1,x_2*y_4*z_1,x_2*y_2*z
       _2,x_1*y_2*z_3,x_1*y_4*z_3,x_2*y_4*z_3,x_3*y_4*z_3,x_2*y_2*z
       _4,x_2*y_4*z_4)

isPower decompose I




monomialIdeal (x y z , x y z , x y z , x y z , x y z ,
                       2 1 1   4 1 1   2 4 1   2 2 2   1 2 3 
       ------------------------------------------------------------
       x y z , x y z , x y z , x y z , x y z )
        1 4 3   2 4 3   3 4 3   2 2 4   2 4 4

-------
restart
load "points.m2"
load "symbPower.m2"
needsPackage "RandomIdeal"
--viewHelp "RandomIdeal"
kk=ZZ/101
S = kk[vars(0..6)]
time for m from 1 to 100 do(
I=randomSquareFreeMonomialIdeal(toList(12:4), S);
L= decompose I;
if isPower L then print L)

for n from 7 to 20 do
(I = randomPoints(S,n,1);
betti res trim I;
print time isPower(3,I))


