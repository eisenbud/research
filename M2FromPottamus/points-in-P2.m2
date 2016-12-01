--compute some invariants from Hilbert-Burch matrices for a set
--of singular points of a plane curve
--s1
--t1 s2
--   t2 s3
--      t3
--s1>=t1>=s2>=t2...
--so code them as one weakly decreasing sequence of 2n terms.
weaklyDecreasingSequences = (maxpart, len) ->(
     --produce a list of all lists of integers 
     --{k1,..,kn} with  n >= k1 >= k2...kn>= 1
     L :=flatten apply((maxpart-1)*len, i ->partitions(i, maxpart-1));
     L = apply(L, i->toList i);
     L = select(L, j-> length j <= len);
     L = apply(L, m -> splice (m|{len-length m:0}));
     ones = splice{len:1};
     apply(L, n-> ones+n)
)
wds = weaklyDecreasingSequences

BezoutVSNew = st ->(
     --st a weakly decreasing sequence of 2n integers -- the degrees
     --on the diagonals of a Hilbert-Burch matrix, interleaved. 
     --should be >0.
     assert (#st%2==0);
     --assert st is weakly decreasing
     n = #st//2;
     s = for i from 0 to n-1 list st_(2*i); --the first diagonal
     t = for i from 0 to n-1 list st_(2*i+1); --the second diagonal
     reg = s_0+sum t - 1; -- the regularity of the ideal

     a = apply(n+1, i-> (sum s_{0..i-1})+(sum t_{i..n-1}));
     	  -- the degrees of the generators, from small to big
     b = apply(n, j->s_j+a_j);
     	  --the degrees of the relations, from big to small
--	  print a;
--	  print b;
	  deg = ((1/2)*(sum (apply(b, x ->x^2))- sum(apply(a,x->x^2))));

     assert (deg == sum apply(#s, i-> s_i*sum(t_{i..#t-1}))); -- the degree of the var
     amin = min a;
     lowest = amin;
     aminMult = # select(a,i-> i==amin);
     dMin = ceiling((aminMult-1+2*deg)/lowest); --lowest degree of an irred curve
                                   --through the points allowed by Bezout
     (dMin, reg, deg, lowest, s, t))
BvN = BezoutVSNew
end
restart
load "points-in-P2.m2"

st = {5,5,5,4,1,1}
st={5,5,1,1}
BezoutVSNew st
BezoutVSNew splice{8:1}
candidates = wds(5,4)
candidates = wds(5,6)

candidates = wds(7,8);
length candidates
scan(candidates, st ->(
	  L = BezoutVSNew st;
	  if L_0<L_1+2 then print L))

test= dif ->(
candidates = wds(2*(2+dif)-1,2*(2+dif));
print length candidates;
scan(candidates, st ->(
	  L = BezoutVSNew st;
	  if L_0<L_1+2-dif then print L)))
test 3

--first line of output for test  ..test 3
--(7, 6, 13, 4, {3, 1}, {3, 1})
--(13, 13, 57, 9, {5, 2, 2}, {5, 2, 2})
--(18, 19, 115, 13, {7, 2, 2, 2}, {7, 2, 2, 2})
--(23, 25, 193, 17, {9, 2, 2, 2, 2}, {9, 2, 2, 2, 2})
(28, 31, 291, 21, {11, 2, 2, 2, 2, 2}, {11, 2, 2, 2, 2, 2})

BvN {11,11,2,2,2,2,2,2,2,2,2,2}

test1 = n -> BvN splice{2*n+1, 2*n+1, 2*n:2}
test1 3
test1 0
oo_1

--test1 n has reg+2-mind = n
for n from 1 to 10 do (
     L = test1 n;
     print L;
     print (L_1+2-L_0))

for n from 1 to 10 do(
L = test1 n ;
print(L_{0,1,2,3} == {3+5*n, 1+6*n, 1+18*n+20*binomial(n,2), 1+4*n}))

{*
So the (n+1) x (n+2) degree matrix
2n+1  2 2 ...
2n+1  2 ..
 .    .
 .    .
 .    .
 
leads to 
dmin, reg, deg, lowest = 
3+5*n, 1+6*n, 1+18*n+20*binomial(n,2), 1+4*n
*}


--First case
S = kk[A,B,C]
nn=1
test1 nn
M = random(S^{nn+2: -(1+4*nn)}, S^{-(2*nn+1)-(1+4*nn), nn:-2-(1+4*nn)});
betti M
I = minors(nn+1,M);
min (flatten (degrees gens I)_1)
T = top(I^2); --(the symbolic square)
min (flatten (degrees gens T)_1) -- for nn=1 this is 10 = reg+3; for nn=2 it's 18 = reg+5.N
test1 nn
f = (gens T)*random(source gens T, S^{-10});
diffs = diff(vars S, f)
degree ideal diffs
degree I
genus ideal f
