--given g pairs of points pi, qi, on P1, find the canonical series
--by determining the g ratios ai that the section of O(2g-2)
--must satisfy to be canonical (note that this depends on choosing
--homogeneous coords at each point pi, qi)

--these are determined inductively: having chosen the first 
--g-1, and it's canonical series, we "add the two new points" -- that
--is, we look at the series of degree 2g-2
--having the given ratios at the first g-1 points, and take the new
--alpha to be the ratio of their values.


canonicalMultipliers = (P,Q) -> (
     --P,Q are the 2 x g matrices of field elements
     --whose i-th columns give homog coords of the points p_i, q_i to be
     --identified.
     g := numcols P;
     --make "quadrics" a list whose i-th elt is the quadratic form that vanishes at pi and qi
     quadrics := apply(g, i->(det(P_{i}|(transpose vars S)))*(det(Q_{i}|(transpose vars S))));
     --make "sections" a list whose i-th elt is the product of all but the i-th quadric
     sections := (apply(g, i -> product(g, j-> if i == j then 1_S else quadrics_j)));
     -- output the  matrix whose entries in the i-th col are
     -- the results of evaluating the i-th element of "sections" on pi and qi
     transpose matrix(apply(g, i ->{sub(sections_i, transpose P_{i}), sub(sections_i, transpose Q_{i})}))
     )


linearSeriesFromMultipliers = (d, P,Q,A) ->(
     --find the linear series of forms of degree d on P^1 that induce
     --sections of a line bundle, specified by the multipliers A
     --on the nodal curve with the points P_{i} and Q_{i} identified.
     g := rank source A;
     S := ring P;
     B := basis(d, S);
     -- evaluate the elements of B at the points specified by the columns of P, Q
     MP := matrix(apply(g, i->flatten entries(A_(1,i)*(sub(B, transpose P_{i})))));
     MQ := matrix(apply(g, i->flatten entries(A_(0,i)*(sub(B, transpose Q_{i})))));
     -- form the matrix specifying the linear combinations that have the correct ratios
     sy := syz(MP-MQ);
     ell := rank source sy;
     --output the matrix whose entries are these linear combinations.
     map(S^1, S^{ell:-d}, B*sy))
end

restart
load "canonical-nodal-curves.m2"
kk= ZZ/32003
S = kk[x_0..x_1]

gener={14}

apply(gener, g->(
P = matrix{{1_S,0,1},{0,1,1}}|random(S^2, S^(g-3));
Q = random(S^2, S^g);
A=canonicalMultipliers (P,Q);
A1 = map(S^2, S^g,  (i,j) -> 
     (if i == 0 then A_(i,j) else if j>=g//2 then (-1)*A_(i,j) else A_(i,j)));
L=linearSeriesFromMultipliers(2*g-2, P,Q,A1);
T1= kk[y_0..y_(numcols L -1)];
I1=trim ker map(S,T1,L);
T=kk[y_0..y_(numcols L -3)];
I = (map(T,T1))I1;
time FF= res (I, LengthLimit => (g//2 - 2), DegreeLimit => 1);
<<(g, codim I, degree I, genus(T/I), betti FF) <<endl
))

