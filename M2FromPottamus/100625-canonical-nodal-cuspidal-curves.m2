--given g pairs of points pi, qi, on P1, find the canonical series
--by determining the g ratios ai that the section of O(2g-2)
--must satisfy to be canonical (note that this depends on choosing
--homogeneous coords at each point pi, qi)

--these are determined inductively: having chosen the first 
--g-1, and it's canonical series, we "add the two new points" -- that
--is, we look at the series of degree 2g-2
--having the given ratios at the first g-1 points, and take the new
--alpha to be the ratio of their values.


canonicalMultipliers = (R,P,Q) -> (
     delta:= numcols P; kappa := numcols R;
     g := delta+kappa;
     quadrics2 := apply(kappa, i-> (det(R_{i}|(transpose vars S)))^2);
     quadrics1 := apply(delta, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     quadrics := join(quadrics1,quadrics2);
     sections := (apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)));
     A = transpose matrix(apply(delta, i ->{sub(sections_i, transpose P_{i}), sub(sections_i, transpose Q_{i})}));
     B= transpose matrix(apply(kappa,i->{sub(diff (matrix{{x_1,-x_0}},sections_(i+delta)), transpose R_{i})}));
     (B,A))


linearSeriesFromMultipliers = (R,P,Q,B,A) ->(
     --find the linear series of forms of degree d on P^1 that induce
     --sections of a line bundle, specified by the multipliers A
     --on the nodal curve with the points P_{i} and Q_{i} identified.
     S := ring P;
     delta := numcols P; kappa := numcols R;
     g := delta+kappa;
     Bs := basis(2*g-2, S);
     jB :=jacobian Bs; 
     MR :=matrix apply(kappa, i->flatten entries((transpose B_{i})*sub(jB,transpose R_{i})));
     MP := matrix(apply(numcols P, i->flatten entries(A_(1,i)*(sub(Bs, transpose P_{i})))));
     MQ := matrix(apply(numcols P, i->flatten entries(A_(0,i)*(sub(Bs, transpose Q_{i})))));
     sy := syz(MP-MQ||MR);
     ell:= rank source sy;
     map(S^1, S^{ell:-2*g+2}, Bs*sy)
     )
end

restart
load "canonical-nodal-curves.m2"
l=30
L=apply(toList factor l,c->value c);
L
isPrime 32003
if l==2 then (r=-1;p=32003) else(
if #L>1 then while(
while (r=random(200);
f=factor (r^l-1);
p=first last f;
not(1000<p and p<32000)) do ();
ta=tally apply(L,c->mod(r^c-1, p) !=0);
not (ta_true==#L) )do() else
while (r=random(200);
f=factor (r^l-1);
p=first last f;
not(1000<p and p<32000)) do ();)
L
r,p,apply(L,c->mod(r^c-1, p))

restart
load "canonical-nodal-cuspidal-curves.m2"
l=2;r=-1;p=32003
--l=4,r=random(300)
--p=first last factor(r^3-1)


kk= ZZ/32003
k=7
g=2*k
delta=g-3
S = kk[x_0..x_1]
R=matrix{{1,0,1},{0,1,1}}**S
P=random(S^2,S^delta)
Q=random(S^2,S^delta)
--P=matrix{{1,1,1,1,1},{4,5,6,7,8}}**S
--Q=matrix{{1,1,1,1,1},{10,9,11,12,13}}**S
(B,A)=canonicalMultipliers(R,P,Q)
B
linearSeriesFromMultipliers(R,P,Q,B,A)
gg=floor(g/2)
delta=numcols A
A1 = map(S^2, S^delta,  (i,j) -> 
     (if i == 0 then A_(i,j) else if j>=0 then r*A_(i,j) else A_(i,j)));
L=linearSeriesFromMultipliers(R, P,Q,B,A);
L=linearSeriesFromMultipliers(R, P,Q,B,A1);
T= kk[y_0..y_(numcols L -1)];
time I=trim ker map(S,T,L);
degree I,codim I, genus(T/I), betti I,l
--time betti res (I, DegreeLimit=>1) 
T1= kk[y_0..y_(numcols L -3)];
I1=substitute(I,T1);
codim I1==codim I
--time betti res (I1, DegreeLimit=>1)
-- genus g=12 :used 77.8 seconds
betti(K=koszul(k-2,vars T1))
betti(phi=K**vars T1)
T1r=T1/I1
betti(phir=lift(substitute(phi,T1r),T1))
m=mingens ideal (gens( (ideal vars T1)^2)%I1)

betti(M=contract(m_0,phir))
scan(g-1,i->M=M||contract(m_(i+1),phir))
betti substitute(M,kk)

time betti(sM=syz transpose substitute(M,kk))
     --g=12: used 11.84 seconds

--rank source sM ==binomial(g-3,k-1)


g=2*k
n=g-3
binomial(n,k-1),binomial(n,k-2),binomial(n,k-3)
binomial(n,k-1),n*binomial(n,k-2),g*binomial(n,k-3)
binomial(n,k-1)-n*binomial(n,k-2)+g*binomial(n,k-3)
 