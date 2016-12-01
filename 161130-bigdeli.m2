
inOut = (S,d,m) ->(
    --generate a list outlist of m square-free monomials of degree d and a list of all the others
    --(outlist, inlist)
    n := numgens S;
    u := binomial(n,d);--number of square-free monomials of degree d in n vars
    if m>u then error"too many monomials";    
    E := coefficientRing S[X_1..X_n, SkewCommutative => true];
    Ed := basis(d,E);
    Sd = flatten entries((map(S,E,vars S)) Ed);
    rnd := {};
    while #rnd<m do rnd = unique({random u}|rnd);
    outlist = Sd_rnd;
    inlist = toList ((set Sd)-outlist);
    (inlist, outlist)
    )
end
restart
load"161130-bigdeli.m2"
n = 5
S = ZZ/2[x_1..x_n]
d = 2

tally apply(100,i->(
(inlist, outlist) = inOut(S,2,4);
betti res ideal inlist)
)
