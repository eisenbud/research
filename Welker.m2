needsPackage "LexIdeals"
needsPackage "RandomIdeal"

lowerExterior = (a,d) -> (
    --takes macaulayRep of a,d and lowers the bottom elements of each binomial
    L := macaulayRep(a,d);
    L' := L/(i->{first i, last i-1});
    sum(L', i->binomial(first i, last i))
	)

X = T ->(
    t := length T;
    drop(apply(t, k-> sum(toList(k..t-1), j->(-1)^(j-k)*T_j)), 1)
    )
Y = x ->(
    t1 := length x;
    apply(t1-1,i->lowerExterior(x_(i+1),i+1))
    )
    

allowableBetti = T -> (
    --checks whether the list T is hilbert function of an extior alg mod a monomial ideal
    t := length T;
    x := drop(apply(t, k-> sum(toList(k..t-1), j->(-1)^(j-k)*T_j)), 1);
    L := apply(t-2,i->x_i-lowerExterior(x_(i+1),i+1));
    all(L, a -> a>=0)
    )

totalBetti = I ->(
    F := res I;
    apply(1+length F, i->rank F_i))

test = (L,S) ->(
    count :=0;
    t = true;
    while t do(
	I := randomMonomialIdeal(L,S);
	T := totalBetti I;
	t := allowableBetti T;
	if not t then print toString I;
	count = count+1;
	if count % 1000 === 0 then << "."<<flush;
    ))

end--
restart
--installPackage "RandomIdeal"
load "Welker.m2"
S = ZZ/101[vars(0..9)]
test(splice{15:2},S)
--the following are examples where the resolution does not satisfy the K3 condition
I1=ideal(e*h,b*e,c^2,f*g,d*g,b*g,a*d,e*f,c*f,h*i,c*g,a*f,c*i,a*j,f*h)
I2 = ideal(a*i,d*j,c*f,a*e,c*e,d*i,a*h,b*i,b*h,g*j,a*d,b*g,f*i,h*j,i^2)
I3 = ideal(g*i,f*h,a*i,i^2,b*e,f*g,e*j,b*f,i*j,g*j,h^2,e*h,d^2,b*i,c*i)
I4 = ideal(e*h,d*i,h^2,g*j,a*j,e*i,f*g,a^2,d*g,c*f,c*e,a*i,f*i,d*h,b*f)

I = I4
betti res I
T = totalBetti I
x = X T
y = Y x

--6 variable seems the minimum where there are examples -- and there are lots!
S = ZZ/101[vars(0..5)]
test(splice{7:2},S)
--first one:
I = ideal(d*f,f^2,b*c,a*f,d*e,a*c,b*e)
--total betti: T= {1, 7, 13, 12, 6, 1}
-- x = X T = {1, 6, 7, 5, 1}
-- y = Y x = {1, 5, 8, 4}
--



