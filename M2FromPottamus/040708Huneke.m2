Work with Craig at Oberwolfach, based on random exaMPLE found by MS.

Try to find i in n vars, gen in degree d, such that t2(S/i^2)>d+2max(d, t2(S/i)-d) ;
(for the minimal counterex, need t2(S/i)>=(3d+1)/2). Then try 
J=i,(new var)^d. For a counterexample to (trunc J)^2 linear for 2 steps
(where (trunc J) is the first lin pres truncation) need
t3(S/J^2)>2t2(S/J).

restart
n=5
D=3
S=kk[vars(0..n-1)]
powers = (ideal(vars S))^[D]

i=mike=powers + ideal(f*(c*e-b^2), d^2*(a-e)) -- with n=6, D=3 this gives a (trunc J)^2 with only one step linear res
i=mike2=powers + ideal(c*d*(b-e), a^2*(b-c)) -- with n=5, D=3 this gives a (trunc J)^2 with only one step linear res

i=powers + ideal(random(S^1,S^{3:-D}))
i=powers + ideal(a*b^2+b*c^2+c*d^2+e*b*c)
i=powers + ideal(a*b^2+b*c^2+c*d^2+e*b*c, a*c*d)
i=powers + ideal(a*b^2+b*c^2+c*d^2+e*b*c)+ideal(random(S^1,S^{3:-D}))
i=powers + ideal(a*b^2+b*c^2+c*d^2) -- with n=5, D=3
i=powers + ideal(a*b^2+b*c^2+c*d^2 , e*b*c-a*b*d)
i=powers + ideal(a^2*(b-c), d*(c*e-b^2))
bettiBounds i
bettiBounds i^2

T=kk[vars(0..n)]
F=map(T,S)
I=F i
J=I+ideal((T_n)^D);
bettiBounds J
bettiBounds J^2
time betti res(J^2, LengthLimit=>3)

restart
S=kk[a,b,c]
i=(ideal(a,b))^3
i=(ideal(vars S))^2
g=ideal random(S^1,S^{3:-3})
s=i+g;
betti res s^2
m=(gens i) | (gens g)
T=kk[vars(0..6)]
F=map(S,T,m)
i=kernel F;
betti res i
bettiBounds oo
use S

restart
S=kk[a,b,c,d,e]
load "2xn.m2"
m=matrix{{0,a,b,c},{a,b,c,0}}
rnc(S,0,4)
i11=minors(2,oo)
i1=ideal (gens(i11)*random(S^{6:-2},S^{5:-2}));
i2=ideal(random(S^1,S^{5:-2}));
i=i1+i2;
mingens (i^3);
binomial(4+6,6)
T=kk[x_0..x_10]
F=map(S,T,gens i);
J=kernel F;
betti res J
