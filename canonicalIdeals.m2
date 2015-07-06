--simplicial complexes Delta where k[Delta] has a linear canonical ideal
--related to work of June Huh

--ideal of the k-skeleton of an r-simples
deltaIdeal = (k,r) ->(
    S := ZZ/101[x_0..x_r];
    prodsets := subsets(toList(x_0..x_r),k+1);
    I := ideal apply(prodsets, p -> product p);
    I)
randomElements = (m,d,I)->(
--choose m elements of degree d in an ideal I
    ideal ((gens I)*random(source gens I, (ring I)^{m:-d})))
reduceToDim1 = I ->(
    S := ring I;
    kk := coefficientRing S;
    codimI = codim I;
    S1 := kk[x_0..x_codimI];
    toS1mat := random(S1^1, S1^{(numgens S):-1});
    toS1 := map(S1, S, toS1mat);
    J = toS1 I)
end

restart
load "canonicalIdeals.m2"
I = deltaIdeal(2,4)
S = ring I
c = codim I
omega = Ext^c(S^1/I, S^{-5})
H = Hom(omega, S^1/I);
prune H

J = reduceToDim1 I
S1 = ring J
omega1 = Ext^c(S1^1/J, S1^{-4})
H1 = Hom(omega1, S1^1/J);
prune H1


A = randomElements((codim J, 3, J))
C = J+trim (A:J) -- canonical ideal of 1-dim'l ring R= S/J, as ideal of S
degrees gens trim C
H = Hom(module C, S1^1/J);
betti prune H
f = homomorphism (H_{0});
K = image f
betti res (S1^1/K)





