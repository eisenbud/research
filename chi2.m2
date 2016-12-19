--constructions from Walker's proof that the sum of the betti numbers is exponential

tau = method()

tau(Ring,ZZ,ZZ) := (R,p,q) ->(
    --regarding P as degree s and Q as degree t, produce the natural map
    --P**Q --> Q**P.
    m := mutableMatrix(R,q*p,p*q);
    apply(p, i-> apply(q, j->
	    m_(j*p+i, i*q+j) = 1));
    map(R^(q*p),R^(p*q),matrix m)
    )

tau(Module, Module, ZZ,ZZ) := (P,Q,s,t) ->(
    --regarding P as degree s and Q as degree t, produce the natural map
    --P**Q --> Q**P.
    sgn := (-1)^(s*t);
    R := ring P;
    p := rank P;
    q := rank Q;
    sgn*tau(R,p,q)
    )

///
restart
load"chi2.m2"
S = ZZ/101[a,b,c]
P= S^{0,1}
Q = S^{3,5}
s = 1;t=1
tau(P,Q,s,t)
isHomogeneous oo
tau(P,Q,s,t)*tau(Q,P,s,t)
tau(S,1,3)

M = S^1/ideal{a^2,b^2,c^2}
N = S^1/((ideal gens S)^3)
F = res M
G = res N
H = G**F
tau(G_1,F_1,1,1)
tau(G_0,F_2,0,2)
G_0**F_2

phi = apply(length F * length G, n->(
apply(n, m-> (H_n)_[(m,n-m)]*tau(G_m,F_(m-n),m,n-m)*(H_n)^[(m,n-m)]
    ))
)
n = 0
m=0
(H_n)_[(m,n-m)]*tau(G_m,F_(n-m),m,n-m)*(H_n)^[(m,n-m)]

(H_n)_[(1,1)]*tau(G_1,F_1,1,1)*(H_n)^[(1,1)]++

(H_n)_[(2,0)]*tau(G_2,F_0,2,0)*(H_n)^[(2,0)]

betti F
betti G
betti H
components (H_2)
degrees F_2
degrees (H_2)
degrees (P**Q)
viewHelp mutableMatrix
///
end--
viewHelp "**"

load"chi2.m2"

n= 2
S = ZZ/101[x_0..x_n]
f = random(S^1, S^{-2})
I = ideal fromDual f
betti res I
M = prune (module I/module (I^2))
ma =random(source gens M, S^{n+1:-2})
degree image map(M, S^{n+1:-2}, ma)
degree (S^1/I)
