restart
    S = ZZ/101[x_1..x_6];
    f = random(S^1, S^{-3});
    I = ideal fromDual f;
    degree I
    degree (module I/module(I^2))
tt = apply(7, i-> Tor_i(S^1/I,S^1/I));
ttd = tt/degree
--{14, 76, 210, 296, 210, 76, 14}
sum ttd -- 896
14*2^6 -- also 896
apply(7, i->ttd_i-14*binomial(6,i))
--{0, -8, 0, 16, 0, -8, 0}

--it is enough to take the Gor with dual socle the sum of just 8 cubes of general linear forms.
    S = ZZ/101[x_1..x_6]
    f = matrix{{
	    sum(apply(6, i->(S_i)^3))
	    }}+gens((ideal random(S^1,S^{-1}))^3)+gens((ideal random(S^1,S^{-1}))^3)
    I = ideal fromDual f;
    degree I
    degree (module I/module(I^2))

For a generic smooth curve of genus 8, the double hyperplane section behaves differently (of course)
loadPackage "RandomCanonicalCurves"
K = (random canonicalCurve)(8,ZZ/32003[y_1..y_8]);
betti res K
degree K
degree (K^2)
betti res (K^2)
degree (module K/module(K^2)) -- 84
K6 = (map(S6,ring K,(vars S6)|random(S6^1,S6^{2:-1}))) K;
degree(K6^2)
