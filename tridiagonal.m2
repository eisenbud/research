--study the resolution of the cokernel of a tridiagonal matrix
--problem suggested by Mike Stillman; it arises in computing class groups of
--certain hypersurfaces in toric varieties.

loadPackage("RandomIdeals", Reload=>true)

pairs2 = L -> flatten apply(#L, i -> apply(#L-(i+1), j ->(L_i, L_(j+i+1))));

multidiag = method()
multidiag(Matrix, ZZ) := (m,n) -> (
    --m is a 1-row matrix of elements of the same degree.
    --script returns an n-rowed matrix, where the i-th row is m, shifted i places to the right
R := ring m;
d := degree m_0_0;
p := numcols m;
map(R^n, R^{n+p-1:-d}, (i,j) -> if i<=j and j<=i+p-1 then m_(j-i)_0 else 0_R)
)

///
kk= ZZ/101
R = kk[x,y]
m = gens (ideal vars R)^2
netList (for n from 1 to 10 list (n, minimalBetti coker multidiag(m,n)))
--always n+2 quadratic syzygies;
if n cong 0 or 2 mod 3 then 2 second syz of dgree n+2
if n cong 1 mod 3, then there are 2nd syz of degrees n+1, n+3

Note that the resolutions only depend on the hilbert function:
netList (for n from 1 to 10 list (n, degree coker multidiag(m,n)))
netList (for n from 1 to 10 list (n, tally flatten degrees source basis coker multidiag(m,n)))
= 3(t+t^2)/(1-t^2)*(1-t)
///

///
kk= ZZ/101
R = kk[x,y]
m1 = matrix"x3,x2y,y3" -- cusp
m2 = random(R^1, R^{3:-3}) -- node
netList (for n from 1 to 10 list 
    (n, minimalBetti coker multidiag(m1,n),minimalBetti coker multidiag(m1,n)))
--always n+2 quadratic syzygies;

Note that the resolutions only depend on the hilbert function:
netList (for n from 1 to 10 list (n, degree coker multidiag(m,n)))
netList (for n from 1 to 10 list (n, tally flatten degrees source basis coker multidiag(m,n)))
= 3(t+t^2)/(1-t^2)*(1-t)
///

///
restart
load "tridiagonal.m2"
kk= ZZ/3
R = kk[x,y]

netList (for n from 1 to 5 list 
    (n, tosequence, apply(s,
	    i-> minimalBetti coker multidiag(mm_i,n))))

deg = 10
mm = flatten apply((deg)//2,i-> matrix{{x^deg, y^deg, x^(i+1)*y^(deg-i-1)}})
netList (for n from 1 to 5 list 
    (n, tosequence, apply(#mm,
	    i-> minimalBetti coker multidiag(mm_i,n))))

deg = 10
mm = flatten apply((deg)//2,i-> matrix{{x^deg, y^deg, x^(i+1)*y^(deg-i-1)}})

netList (for n from 1 to 5 list 
    (n, tosequence, apply(#mm,
	    i-> minimalBetti coker multidiag(mm_i,n))))


tail =(m,n) ->sort apply(select(pairs minimalBetti coker multidiag(m,n), p-> p_0_0 == 2), p->(p_0_2, p_1))
scan(5, d->(
	<<netList  apply(mm,m->(m,tail(m,d+1)))<<endl;
	)
)	

///

///
restart
load "tridiagonal.m2"
kk= ZZ/101
R = kk[x,y,z]
mm = apply(100, i->gens randomMonomialIdeal(3:7,R));
mm = unique select(toList mm, m->codim ideal m == 2)
mm2 = pairs2 mm;
d = 1;
mm3 = select(mm2, p -> betti res coker multidiag(p_0,d) == betti res coker multidiag(p_1,d))
#mm3
d = 2;
mm4 = select(mm3, p -> betti res coker multidiag(p_0,d) == betti res coker multidiag(p_1,d))
#mm4
d = 3;
mm5 = select(mm4, p -> betti res coker multidiag(p_0,d) == betti res coker multidiag(p_1,d))
#mm5

select(mm3, p -> betti res coker p_0 == betti res coker p_1)


netList apply(1, n ->(
    (n, tosequence, apply(5,
	    i -> minimalBetti coker multidiag(mm_i,1)))))

///
