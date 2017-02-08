
--Example 6.1 in the 2017 version of the paper 
--"Duality and Socle Generators for Residual Intersections"
--by David Eisenbud and Bernd Ulrich
--purports to be a border case for Theorem 2.6, showing that the
--condition that I has  G_(v+t) cannot be weakened to G_(v+t-1)
--even when I is codimension 2 perfect (and thus licci).

--To check this, We first produce
--An s-residual intersection that is G_{w-1} but not G_{w},
--where w = v+t = v+s-g.

--We take:
--g=2; 5<=s<=7; t=s-g;
--max(1,ceiling ((s-3)/2)) <= v <= s-2 ; 
--w = v+2; t=s-g; 
--note that this would be empty if s<5;

-- we claim to have checked this for all admissible values 
-- of v and s<=7. The computation of the residual intersection becomes
-- very slow from s=7, w=4 on (that is, all the cases s=7 (we allow w=4,5,6).
-- we have checked that it's an s-residual int up to the case 7,4, not the others.
-- Better to only do the cases s<=6 for the moment.
-- We start from the Macaulay matrix, whose minors are a power of the max ideal.

macaulayMat= (R,s)->(
     map(R^(s), R^{2*s-1:-1}, (i,j) -> 
    if i<=j and i>=j-s+1 then R_(j-i) else 0_R)
)

test = (s,v) ->(
w = v+2;t=s-2;
--make an s x (s-1) matrix N whose 
--ideal of (s-1)-minors I satisfies G_w, not G_{w-1}:
<<(s,w)<<endl;
kk = ZZ/101;
R = kk[x_0..x_(s-1)];
M' = mutableMatrix (M= macaulayMat(R,s));
N' = M'_(toList(1..s-1));
N'_(s-w,s-2) = 0;
N = matrix N';
I = minors(s-1,N) ;
assert (codim I ==2);
codims = apply(s-1, j -> codim minors(s-1-j,N));
GinftyCodims = toList(2..s);
codims - GinftyCodims;
print (min positions(codims-GinftyCodims, i-> i<0) == w-2);
-- this proves: I is codim 2 and satifies G_(w-1) but not G_{w}.
M' = mutableMatrix (M= macaulayMat(R,s));
M'_(s-w,s-1) = 0;
M'_(s-w,0) = M'_(s-w,0)+ R_(w-1) ; -- replaced 1 by 0
M'_(s-w,2*s-w) = R_(w-1) ;
M' = matrix M';
--M'
--print(codim minors(s,M') == s);
--shows that the maximal minors of M' are codim s
--M' is (s-1) x (2*s-2); maximal minors are the (s-1) power of ideal vars S
colList = {0}|toList(s..2*s-2);
P = M'_colList;
J = ideal(transpose(syz transpose N)*P);
<<"special choice of J"<<endl;
--print(codim(K = (J:I)) == s);
--this shows that K is an s-residual intersection. The computation gets slow from (7,4) on.
--checked up to hear for s<=6 in 15 sec on old mac pro.
--
--
--Up to here we have shown that 
--the hypothesis of theorem 2.6 are satisfied EXCEPT for G_(w).
--
--Ns = gens minors(s-1,N);
-- <<"general choice of J"<<endl;
--J = ideal(Ns*random(source Ns, R^{s:-s} ));
--print(codim(K = (J:I)) == s)
--this shows that K is an s-residual intersection in this generic case, too. 
--The computation gets slow from (7,4) on.
--
--Test duality:
for u from max(1,t-v) to min(1+v,(s-1)//2) do(
    <<(u,s-1-u)<<endl;
    << betti res prune(I^u/(J*I^(u-1)))<<endl<<endl;
    if u<s-1-u then 
    << betti prune (I^(s-1-u)/(J*I^(s-2-u)))<<endl<<endl<<endl;
	)
)

makeIJ = (s,w) ->(
v = w-2;t=s-2;
--make an s x (s-1) matrix N whose 
--ideal of (s-1)-minors I satisfies G_w, not G_{w-1}:
kk = ZZ/101;
R = kk[x_0..x_(s-1)];
M' = mutableMatrix (M= macaulayMat(R,s));
N' = M'_(toList(1..s-1));
N'_(s-w,s-2) = 0;
N = matrix N';
I = minors(s-1,N) ;
assert (codim I ==2);
codims = apply(s-1, j -> codim minors(s-1-j,N));
GinftyCodims = toList(2..s);
codims - GinftyCodims;
assert(min positions(codims-GinftyCodims, i-> i<0) == w-2);
-- this proves: I is codim 2 and satifies G_(w-1) but not G_{w}.
M' = mutableMatrix (M= macaulayMat(R,s));
M'_(s-w,s-1) = 0;
M'_(s-w,0) = M'_(s-w,0)+ R_(w-1) ; -- replaced 1 by 0
M'_(s-w,2*s-w) = R_(w-1) ;
M' = matrix M';
colList = {0}|toList(s..2*s-2);
P = M'_colList;
J = ideal(transpose(syz transpose N)*P);
apply(numgens R, i-> assert ((gens(R_i^s*I))%J == 0));
--shows J:I is an s-residual intersection containing the variables to the s power
(I,J)
)

testDuality = (I,J,s,w) ->(
    t=s-2;v=w-2;
    for u from max(1,t-v) to min(1+v,(s-1)//2) do(
    <<"----------"<<"(u, s-1-u) =  "<< (u,s-1-u)<<"------------"<<endl;	
    if u<s-1-u then 
    <<time minimalBetti(I^u/(J*I^(u-1)), LengthLimit =>1)<<endl<<endl;
    if u<=s-1-u then 
    << time minimalBetti(I^(s-1-u)/(J*I^(s-2-u)))<<endl<<endl<<endl;
	))

end--
restart


load "170207-duality-example-with-Ulrich.m2"

time for s from 7 to 7 do(
for w from max(3, ceiling((s+1)/2)) to s do(
    <<"==========="<<"s and w: " << (s,w)<<"==========="<<endl;
    (I,J) = makeIJ(s,w);
    testDuality(I,J,s,w))
    )

viewHelp minimalBetti
(I,J) = makeIJ(6,4);
testDuality(I,J,5,3)


s=5;
time for v from max(1,ceiling ((s-3)/2)) to s-2 do(
	test(s,v))

s=6;
for v from max(1,ceiling ((s-3)/2)) to s-2 do(
	time test(s,v))

