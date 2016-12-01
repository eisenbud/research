test=(n,d,k) ->(
S = kk[x_1..x_n];
mm = ideal gens S;
g=ideal((sum gens S)*product gens S); -- product of n+1 "standard" linear forms
f = (ideal(random(S^1, S^{n:-1})))^d; --d-th power of one more
i = f*g+mm^(d+2+n+k); -- this is the ideal that would move in a family
I = intersect(g, mm^(n+d+1))+mm^(d+2+n+k); -- defines the biggest subscheme of the intersection
A = degree I + degree kernel transpose ((S/I)**jacobian I); -- value for the fixed scheme
B = degree kernel transpose ((S/i)**jacobian i); --value for the moving scheme. Ever bigger?
numeric(A/B)); -- want A/B <1

end

test(2,4,7)

restart
load "tangent.m2"


vals = for n from 2 to 4 do(
     for d from 2 to 6 do (
	  for k from d to 10 do(
	       print(n,d,k,test(n,d,k))
	       ))
)

n=3 -- embedding dim
d =  --should be at least 2
k = 4 -- degree of truncation

testLines = (n,d,k) -> ( --n+d lines truncated to degree k)
S = kk[x_1..x_n];
mm = ideal gens S;
nLines = intersect for i from 0 to n-1 list ideal ((gens S)_{0..i-1, i+1..n-1});
dLines = intersect for i from 1 to d list ideal random(S^1, S^{n-1:-1});
Lines =  intersect(nLines, dLines);
i = trim (Lines + mm^k);
--print betti i;
I = trim(mm^(min flatten degrees i));
--print betti I
A = degree I + degree kernel transpose ((S/I)**jacobian I); -- value for the fixed scheme
B = degree kernel transpose ((S/i)**jacobian i); --value for the moving scheme. Ever bigger?
numeric(A/B)
 -- want A/B <1
)

vals = for n from 3 to 5 do(
     for d from 2 to 6 do (
	  for k from d to 10 do
	       print(n,d,k,testLines(n,d,k))
	       ))

testLines(3,2,5)
A == 13
B == 31

testForms = (n,d,k) -> ( --one form of degree d plus the k-th power of the max ideal vs all forms of deg d)
S = kk[x_1..x_n];
mm = ideal gens S;
i = trim (mm^k+ideal random(S^1, S^{-d}));
I = trim (mm^d);
--print betti I
A = degree I + degree kernel transpose ((S/I)**jacobian I); -- value for the fixed scheme
B = degree kernel transpose ((S/i)**jacobian i); --value for the moving scheme. Ever bigger?
numeric(A/B))
 -- want A/B <1)

testForms(2,4,7)
A,B = 28,31
testForms(4,6,10)
A,B 

testForms(3,3,5)
(A,B) == (37, 70)
I
i
degree i == 31
degree Hom(i/i^2, S^1/i) == 207
TY= kernel transpose ((S/i)**jacobian i)
TY0=kernel transpose ((S/I)**jacobian I)
degree TY
degree TY0
degree I
vals = for n from 2 to 5 do(
     for d from 3 to 6 do (
	  for k from d+1 to 10 do
	       print (n,d,k,testForms(n,d,k))
	       ))

--i = ideal(f)+mm^9
ji=jacobian i
Ri = S/i
omegai = coker(sub(ji, Ri))
tanSheafi = Hom(omegai, Ri)
degree tanSheafi
degree Ri


jI=jacobian I
RI = S/I
omegaI = coker(sub(jI, RI))
tanSheafI = Hom(omegaI, RI)
degree tanSheafI
degree RI
