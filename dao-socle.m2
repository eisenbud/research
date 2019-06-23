--are there artinian rings such that the third syz of the res field k contains k as summand?
syzygy = (m, M) ->(
    F := res(M, LengthLimit => m+1);
    image F.dd_(m+1))

socleSummand = method(Options=>{Count =>false})
socleSummand Module := o-> M -> (
    R:= ring M;
    mm := ideal vars R;
    soc := (0_R*M):mm;
--    error();
    if o.Count == false then ((gens soc) % (mm*M)) != 0
    else 
    (degrees mingens image ((gens soc) % (mm*M)))_1
    )

test = method(Options => {Count => false})   
test(Ideal, ZZ)  := o-> (I, sy)->(
    S := ring I;
    k := coker vars (S/I);
    F := res(k, LengthLimit => sy+1);
    MM := apply(sy,i-> image F.dd_(i+1));
    apply(MM, M-> socleSummand(M, Count => o.Count))
    )

mpowerMinus1 = (S,pow,i) ->(
    mm := ideal vars S;
    I0 = mm^pow;
    n := numgens I0;
    ideal((gens I0)_(toList(0..i-1)|toList(i+1..n-1)))    
    )

randomTest = (S, degs, sy) ->(
    --does the sy-th syzygy of k over  S/(random ideal with generators of degrees degs)
    --have k as a summand.
    I := ideal random(S^1, S^-degs); 
    k := coker vars (S/I);
    F := res(k, LengthLimit => sy+1);
    MM := apply(sy,i-> image F.dd_(i+1));
    ss := MM/socleSummand;
    t := any(ss, i->i);
    if dim I == 0 and t and not ss_1 and ss_3 then print (ss, toString I);
    if dim I == 0 and t and not ss_3 then print (ss, toString I);
    )

--2 vars:
cod2 = method(Options => {Count => false})

cod2(Ring, List, List) := o-> (S, rowdegs, coldegs)->(
M := random(S^(-rowdegs), S^(-coldegs));
phi :=map(S,S,toList(numgens S:0_S));
Mconstant := map(target M, source M, (i,j) -> phi(M_j_i));
--Mconstant = sub(M,toList(numgens S, S_i=>0_S))
M = M-Mconstant;
I := minors(#coldegs, M);
--print I;
T := test(I, 8, Count => o.Count);
--if T !={false, false, true, false, true} then 
print(M, rowdegs, coldegs, T)
)

golod = method()
golod(ChainComplex) := (C) ->(
    --adapted to codim 2 perfect ideals in 2 variables
    --for the moment produces the first 5 terms
    S = ring C;
    F1 = C_1;
    F2 = C_2
    )
///
restart

 comps1 = (n,g,p) ->(
          --all lists of non-neg integers M
	  -- of length 1+p, where 0<= M_0 <=n and 1<= Mi<= n-p and sum M =n-p.
          L1 = apply(n,i->i+1);
	  if p==0 then return {{g}};
          if p==1 then return {L1};
          M = L1;
          M = apply(p-1, e->  M = flatten apply(M, ell->apply(n, i->flatten {ell}|{i+1})));
          Mp = select(flatten M, m->p == #m and sum m <= g-p);
	  Mpp = apply(Mp, m-> prepend(g-p-sum m, m))
	  )
 comps = (n,g) -> flatten  apply(g//2, p->comps1(n,g,p))
n=2;g = 7; p=3;
c1 =  comps1(n,g,p) 
comps(n,g)
f = {0,3,2}
rankComps = (n,g) -> sum apply(comps(n,g), m-> flatten {binomial(n,m_0), 
	apply(#m,i->(f_(i+1))^(m_(i+1)))})
comps(2,0)--should be {0},coming from:
comps1(2,0,1)--should be {0}.
comps1(2,0,1) -- should be empty.

rankComps(2,0) -- should be 1
rankComps(2,1) -- should be 2
rankComps(2,2) trouble!

///
end--

restart
load "dao-socle.m2"
kk = ZZ/32003
S = kk[a,b,c]
--R = S/(ideal vars S)^3
R = S/(ideal"a3,b3,c3")
M =  syzygy(6,coker vars R)
socleSummand (M, Count =>false)

restart
load "dao-socle.m2"
S = ZZ/5[a,b,c]
mm = ideal vars S
I = ideal(a^2,b^2)
I = ideal"a3, a2b, b3"
I = ideal"a4,a3b,ab3,b4"
I = ideal"a4,a3b,a2b2,b4"

S = ZZ/5[a,b]
mpoowerMinus1(S

test(I, 7)
for i from 2 to 10 do print test(I^i, 10)

degs = {9,9,9,9}
sy = 5
time scan(1000,i-> randomTest(S,degs, sy))





--degrees 3,3,3,4
--an example where the socle is a summand in the 4th syzy, not before.
kk = ZZ/32003
S = kk[a,b,c]
degs = {3,3,3,4}
I = ideal(-2*a^3-2*a^2*b+2*a*b^2-a*b*c+2*a*c^2+b*c^2-2*c^3,2*a^3+2*a^2*b+a*b^2-2*b^3+a^2*c+a*b*c-b^2*c-2*a*c^2+2*b*c^2+2*c^3,a^2*b-a^2*c-2*a*b*c+2*a*c^2-b*c^2+2*c^3,-2*a^4+a^3*b+2*a^2*b^2-a*b^3-b^4+a^3*c+a*b^2*c-b^3*c+2*a*b*c^2-2*b^2*c^2+a*c^3+2*c^4)
R = S/I
k = coker vars R
betti (F = res (k, LengthLimit =>7))
MM = apply(6, i-> image F.dd_(i+1));
MM/socleSummand

degs = {5,5,5},
2 vars, 
ZZ/5
({false, false, true, false, true, true, true}, ideal(a^5-2*a^4*b-2*a^2*b^3+a*b^4-b^5,2*a^5+a^4*b-a^3*b^2-a^2*b^3+a*b^4-2*b^5,-2*a^4*b+2*a^2*b^3-2*a*b^4-2*b^5))


restart
load "dao-socle.m2"
S = ZZ/32003[x,y]
rowdegs = r = {4,4,5}
coldegs = c = {5,6}
cod2(S,r,c, Count => false)
cod2(S,r,c, Count => true)


