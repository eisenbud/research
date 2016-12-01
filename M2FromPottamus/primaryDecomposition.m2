
pdecomp=method()
pdecomp(MonomialIdeal):= i ->(
     primes = ass i;
     irreds=primaryDecomposition(i, Strategy=>MonomialIdeal);
for c from 0 to (# primes)-1 list {intersect select(irreds, j-> primes_c==radical j)}
     )

pdecomp(Ideal) := i ->(
     primes = ass i;
     irreds=primaryDecomposition(i);
for c from 0 to (# primes)-1 list {intersect select(irreds, j-> primes_c==radical j)}
     )

show=method()
show(List):=L-> (apply(L, print);)

end 
restart
load "primaryDecomposition.m2"
--load "randomIdeal.m2"

kk=ZZ/101
S=kk[a,b,c,d]

i1= monomialIdeal (a^2, a*b, b^3, c*b^2)
i1=monomialIdeal truncate(4,ideal (a^2, a*b, b^3, c*b^2))
i1=monomialIdeal truncate(4,ideal (a^2, a*b^2, b^3))

i=randomMonomialIdeal({5,5,5,5,5}, S)

i=intersect(ideal(a^6,b^6,c^6,(a*b*c)^3), (ideal(a,b))^7)
show  pdecomp i
goods=irreds

i=intersect(goods_{3,7..9})
show pdecomp i
irreds

m=module(ideal(a^4,b^4))/(module i)
betti res m

--------
--Sturmfels' example:
I = ideal (a^8*b^5*c^2*d^3,   a^5*b^8*c^3*d^2,   a^2*b^3*c^8*d^5,  a^3*b^2*c^5*d^8,
      a^6*b^7*c^4*d,  a^7*b^6*c*d^4,  a*b^4*c^7*d^6,  a^4*b*c^6*d^7)
show  (L=pdecomp I)	
ArtI =  ideal(a^8, b^8, c^8, d^8,  a^7*b^6*c^4,   a^6*b^7*c^4,    a^7*b^6*d^4, a^6*b^7*d^4,
a^4*c^7*d^6,   a^4*c^6*d^7,   b^4*c^7*d^6,   b^4*c^6*d^7)
ArtI==(L_14)_0


R = QQ[a,b,c];
I = monomialIdeal(a^6, a^5*c^7, a^4*b^3*c^3, a^3*b^4*c^2, b^5*c^6, b^6);
P = monomialIdeal(apply(gens R, x -> x^10));
dual1 = monomialIdeal((gens(P:I)) % P);
dual1
J = monomialIdeal toList (set first entries (gens dual1) - set first entries((gens dual1) % ideal(product gens R)));
J= monomialIdeal select(first entries gens dual1, m->(m% (product gens R)=!=0))
dual2 = monomialIdeal((gens(P:J)) % P)


