--compute the equations of the dual variety via the incidence corr.
--input the equations of a variety in P^n
--output the equations of the dual variety.

dualVariety = method()

dualVariety(Ideal, Ideal) := (I, SingularIdeal) -> (
    --assume that I is a homogeneous ideal in a standard graded (non-tower) ring, defining a 
    --variety X whose singular locus is defined by SingularIdeal (which should be set to ideal(1_(ring I/I))
    --when X is known to be smooth.
    -- We form the Jacobian matrix of I, pull it back to the
    --incidence correspondence, and compose with the new variables to get the ideal
    --in the incidence correspondence of planes containing the tangent line to X.
    --Saturating with respect to the pullback of SingularIdeal gives just the closure of the
    --part lying over the smooth locus, and elimination then gets the dual variety.
    
     S:= ring I;
     kk:=coefficientRing S;
    -- The tangent bundle of X is the kernel of the
    --transposed jacobian matrix of I, restricted to X, mod the Euler derivation.
    --Since the Euler derivation composes to zero with the new variables in the
    --incidence correspondence anyway, we don't need to factor it out.
    tan := syz((S/I)**(transpose jacobian I));
    --Now make the target ring, and begin to form the incidence correspondence 
     n:=numgens S-1;
--X = symbol X;
--Y = symbol Y;
     T:=kk[symbol Y_0..symbol Y_n];
     Inc:=kk[symbol X_0..symbol X_n, symbol Y_0..symbol Y_n];
     p1 := map(Inc, S, (gens Inc)_{0..n});
    --we form the bihomogeneous ring IncI that is the part of the incidence correspondence
    --point and hyperplane that lies over X.
     IncI := Inc/(p1(I)+ideal(sum(n+1, i -> X_i*Y_i)));
     --its irrelevant ideal and the map to it from the ring of X
     irrel := (ideal( (gens IncI)_{0..n}))*(ideal( (gens IncI)_{n+1..2*n+1}));
     p1bar := map(IncI, S/I, (gens IncI)_{0..n});
     --pull up the tangent bundle of X
     J:=sub(p1bar tan, IncI);
     --and compute its image when composed with the vector of new variables
     Yvars:=map(IncI^1, target J, (i,j)->IncI_(j+n+1));
     L:= ideal (Yvars*J);
     L = saturate(L, irrel);
    --The saturation of L is the ideal of {point and plane cotaining the tan space to X at the point.
    --We need to remove the part of L lying over the singular locus.
    L = saturate(L, p1bar sub(SingularIdeal, S/I));

     --now eliminate the X variables.
     final := IncI/L;
     p2:=map(final, T, (gens final)_{n+1..2*n+1});
     ker p2)


end
restart
load "dualVariety.m2"
kk=ZZ/101
R = kk[a,b,c,d]
I = minors(2, matrix"a,b,c;b,c,d")
dualVariety (I, ideal(1_(R/I)))


I = monomialCurveIdeal(R,{1,3,4})
dualVariety (I, ideal(1_(R/I)))
R = kk[a,b,c]
I = ideal"b2c-a3" -- cuspidal cubic
SI = ideal(a,b) -- singular locus
dualVariety(I,SI)

restart
load "dualVariety.m2"
kk= ZZ/101
C = kk[a,b,c,d,e,s,t]
f = (a*s-e*t)^2*(b*s-e*t)^2*(c*s-e*t)*(d*s-e*t)
T = kk[A..G]
C1 = kk[a..e]
N = sub(contract(gens (ideal(s,t))^6, f), C1)
G = ker map (C1, T, N)

restart
load "dualVariety.m2"
kk= ZZ/101
C = kk[a,b,c,d,e,f,s,t]
g = (a*s^2+b*s*t+c*t^2)^2*(d*s^2+e*s*t+f*t^2)
T = kk[A..G]
C1 = kk[a..f]
N = sub(contract(gens (ideal(s,t))^6, g), C1)
J=jacobian N
J4=minors(4,J);
codim J4
J5 = minors(5,J);
codim J5
G = ker map (C1, T, N)


