S=kk[a..c]
p=3
deg=3
i=ideal random (S^1, S^{2*deg:-deg})
mingens ideal (gens ((ideal vars S)^(p*deg))%(gens (i^p)))
betti res i^3

S=kk[a,b,c,d]
d=5
m=random(S^(d+1),S^{d+1:-1});
i=minors(d,m);
betti res i
betti res i^2

restart
for n from 3 to 6 do(
for d from 2 to 5 do(
S=kk[x_1..x_n];
f=random(S^1,S^{-2*d+2});
i=ideal fromDual f;
print betti res i))

