--example of a non-CohenMacaulay Almost complete int of codim 3:
--ell curve x ell curve \subset PP^2 x PP^2 \subset PP^8
--gives a normal pseudogorenstein ring. Its generic link should
--be the ACI.--

--First PP^1 x ell curve, which does not work (can bundle is (-2,0), not 
--     a mult of the hyp bndle.
R=kk[x,y,a,b,c]/ideal(a^3+b^3+c^3)
S=kk[A..F]]
I=kernel map(R,S, gens (ideal(x,y)*ideal(a,b,c)))
M=Ext^3(S^1/I, S)
betti res M
betti res I -- codim 3, pd 4
I2=ideal (gens I)_{0..2}
codim (I22=ideal((gens I)_{0}|(gens I)_{2}))

J=I22+ideal ((gens I)*random(source gens I, S^{1:-3}))
betti res J
K=J:I;
betti res K

-------Now ell curve x ell curve
restart
R=kk[x,y,z,a,b,c]/ideal(a^3+b^3+c^3, x^3+y^3+z^3)
S=kk[A..I]
I=kernel map(R,S, gens (ideal(x,y,z)*ideal(a,b,c)))
M=Ext^6(S^1/I, S)
betti res M
betti res I -- codim 3, pd 4
--these two modules are the same!
I2=ideal (gens I)_{0..8} -- the quadratic part; this is the segree of P2 x P2.

codim (I22=ideal( (gens I2)*random(source gens I2, S^{4:-2})))
J=I22+ideal ((gens I)*random(source gens I, S^{2:-3}))
--betti res J
K=J:I;
betti K
             0 1
o13 = total: 1 7
          0: 1 .
          1: . 4
          2: . 2
          3: . .
          4: . 1
