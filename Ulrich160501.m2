makeSeg = method()

makeSeg(ZZ,ZZ,ZZ) := (n,d,num)->(
    S := ZZ/101[x_1..x_n];
    H := apply(d+1, j->if j<d then binomial(n-1+j,j)
	                      else binomial(n-1+j,j)-num);
    I0 := lexIdeal(S,H);
    ideal((gens I0)_{0..num-1})
    )

makeSeg(ZZ,List) := (n,num)->(
    S := ZZ/101[x_1..x_n];
    H := apply(#num, j->binomial(n-1+j,j)-num_j);
    I0 := lexIdeal(S,H);
    sumnum := sum num;
    g := flatten degrees I0;
    ideal((gens I0)_(positions(g,i->i<#num)))
    )
end

viewHelp
installPackage("LexIdeals")
installPackage "RandomIdeal"

viewHelp LexIdeals
viewHelp RandomIdeal
restart
loadPackage("LexIdeals", Reload=>true)
load"Ulrich160501.m2"
loadPackage ("RandomIdeal", Reload=>true)

n = 5;d= 3;
L = apply(binomial(n-1+d,d), j->saturate(makeSeg(n,d,j),x_n));
max(L/(I->numgens(I)))

n = 5;d= 4;
L= flatten for i from 1 to binomial(n+d-1,d) list
    for j from 1 to macaulayBound(i,d) list
    {i,j};
time M = apply(L,p-> trim makeSeg(n,{0,0,0,binomial(n+d-1,d)-p_0,binomial(n+d,d+1)-p_1}));
#M
time max(M/(I -> numgens saturate(I,(ring I)_(n-1))))

restart
loadPackage( "RandomIdeal", Reload=>true)
n = 7
S = ZZ/32003[x_0..x_(n-1)]
J = monomialIdeal 0_S
scan(1000, i -> J= (randomSquareFreeStep J)_0)
time L = apply(100000, i -> J= (randomSquareFreeStep J)_0);
# L
# unique L -- 94,233/100,000
tally apply(L, I -> (codim I, length res I))
LCM = select(L, I -> (codim I===length res I));
#LCM -- 1291
--dLCM = apply(LCM, I-> apply (3, m->length res (I^(m+1))));
time d2AN = select(LCM, I -> 1+codim I >= length res I^2);
#d2AN -- 3/100,000
--the ones not in d3AN:
monomialIdeal (x_1*x_2*x_4,x_1*x_2*x_3*x_5,x_1*x_4*x_5,x_2*x_3*x_4*x_5,x_0*x_2*x_3*x_6,x_0*x_1*x_4*x_6,x
      _1*x_5*x_6,x_0*x_4*x_5*x_6,x_2*x_4*x_5*x_6)
monomialIdeal (x_0*x_1*x_2*x_3,x_0*x_2*x_3*x_4,x_0*x_4*x_5,x_2*x_4*x_5,x_0*x_1*x_3*x_6,x_1*x_2*x_4*x_6,x
      _0*x_2*x_5*x_6,x_1*x_2*x_5*x_6,x_1*x_3*x_4*x_5*x_6)
d3AN = select(d2AN, I -> 2+codim I >= length res I^3);
#d3AN --1/100,000
monomialIdeal (x_0*x_1*x_2*x_3,x_0*x_3*x_5,x_1*x_2*x_3*x_5,x_0*x_1*x_2*x_4*x_5,x_0*x_1*x_2*x_6,x_1*x_2*x
      _4*x_6,x_0*x_1*x_3*x_4*x_6,x_2*x_3*x_4*x_6,x_0*x_4*x_5*x_6,x_1*x_3*x_4*x_5*x_6)

d4AN = select(d3AN, I -> 3+codim I >= length res I^4);
0/100,000
#d4AN
d4AN_0
betti res d4AN_0
codim d4AN_0 == 3
betti res (d4AN_0^5)
betti res (d4AN_0^6)

///
--codim 4 CM examples in 7 vars with squares and cubes of right depth
S = ZZ/101[x_0..x_6]
I1 = monomialIdeal (x_0*x_1,x_0*x_3,x_1*x_2*x_3,x_0*x_2*x_4,x_1*x_2*x_4,x_1*x_3*x_4,x_2*x_3*x_4*x_5,x_0*x_2*x
      _6,x_1*x_2*x_6,x_1*x_3*x_6,x_4*x_6,x_2*x_3*x_5*x_6)
I2 = monomialIdeal (x_2,x_0*x_3,x_1*x_4,x_1*x_3*x_5,x_1*x_5*x_6,x_4*x_5*x_6)
--I1 is not G7, but I2 is
codim I2
betti res (I2^2)
varset = flatten entries vars S
apply(varset, y->numgens trim saturate(I2, y))
twos = subsets(varset,2)/product
apply(twos, y->numgens trim saturate(I2, y))
betti res I2
betti res (I2' = ideal((gens I2)_{1..5}))
degree I2'

///

