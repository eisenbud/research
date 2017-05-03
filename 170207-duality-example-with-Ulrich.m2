
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

-- We start from the Macaulay matrix, whose minors are a power of the max ideal.

macaulayMat= (R,s)->(
     map(R^(s), R^{2*s-1:-1}, (i,j) -> 
    if i<=j and i>=j-s+1 then R_(j-i) else 0_R)
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
    if u<s-1-u then (
    <<"----------"<<"presentation of I^u/JI^(u-1) "<<"------------"<<endl;	
    <<time minimalBetti(I^u/(J*I^(u-1)), LengthLimit =>1)<<endl<<endl);
    if u<=s-1-u then (
        <<"----------"<<"Betti table of I^(s-1-u)/JI^(s-2-u) "<<"------------"<<endl;	
    << time minimalBetti(I^(s-1-u)/(J*I^(s-2-u)))<<endl<<endl<<endl);
	))

end--
restart
--GC_INITIAL_HEAP_SIZE=14G (before M2
load "170207-duality-example-with-Ulrich.m2"

time for s from 5 to 7 do(
for w from max(3, ceiling((s+1)/2)) to s do(
    <<"==========="<<"s and w: " << (s,w)<<"==========="<<endl;
    (I,J) = makeIJ(s,w);
    testDuality(I,J,s,w))
    )



-----
S= ZZ/101[x_1..x_7]
f = random(S^1,S^{-2,-2,-3})
I = ideal fromDual f
betti (F = res I)
omega = prune coker dual(F.dd_7)
degree (S^1/I)
degree((module I)/(module(I^2)))
degree(omega ** ((module I)/(module(I^2))))


betti res (I^2)
mm = ideal vars S
numgens trim ideal(gens(I*(mm^2)) %(I^2))

T = QQ[n]
p=((n)*(n-1)/2+(n+2)*(n+1)*(n)/6-1)-(2*n+2)*n
apply (10, i-> sub(p, n=>i))
sub(p, n=>6)
