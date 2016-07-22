--Singular locus of a ring or variety with nonstandard ZZ_(>0) grading

nonstandardSingularIdeal = method()    
nonstandardSingularIdeal Ring := S ->(
    K := coefficientRing S;
    d := lcm flatten((gens S)/degree);
    B := basis(d,S^1);
    n := numcols B;
    t := symbol t;
    T := K[t_0..t_(n-1)];
    I := ker (f = map(S,T,B));
    trim f (ideal presentation singularLocus (T/I))
    )
nonstandardSingularIdeal Ideal := I ->(
    nonstandardSingularIdeal ring I)
nonstandardSingularIdeal AffineVariety := X ->(
    nonstandardSingularIdeal ring X)
nonstandardSingularIdeal ProjectiveVariety := X ->(
    nonstandardSingularIdeal ring X)
    
nonstandardSingularLocus = method()
nonstandardSingularLocus ProjectiveVariety := X ->(
    S := ring X;
    J := nonstandardSingularIdeal S;
    Proj(S/J)
    )
nonstandardSingularLocus AffineVariety := X ->(
    S := ring X;
    J := nonstandardSingularIdeal S;
    Spec(S/J)
    )


end--

restart
load"NonstandardSingularLocus.m2"

S = QQ[x,y,z, Degrees =>{{1},{1},{2}}]
nonstandardSingularIdeal S
nonstandardSingularIdeal ideal(0_S)

X = Proj S
nonstandardSingularLocus X
X = Spec S
nonstandardSingularLocus X
