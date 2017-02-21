
--Example 6.1 in the 2017 version of the paper 
--"Duality and Socle Generators for Residual Intersections"
--by David Eisenbud and Bernd Ulrich
--presents a border case for Theorem 2.6, showing that the
--condition that I has  G_(v+t) cannot be weakened to G_(v+t-1)
--even when I is codimension 2 perfect (and thus licci).

--To check this, We first produce
--An s-residual intersection that is G_{w-1} but not G_{w},

--We take:
--g=2; 5<=s<=7; t=s-g; v = u+g = u+2
--1 <= u <= s-1-u.
--By Theorem 2.6 we get duality when 
-- w-1 >=g+v = 2+v = 4+u and (t-1)/2<=v<=t.


-- We start from the Macaulay matrix, whose minors are a power of the max ideal.

macaulayMat= (R,s)->(
     map(R^(s), R^{2*s-1:-1}, (i,j) -> 
    if i<=j and i>=j-s+1 then R_(j-i) else 0_R)
)

-- We now make a pair (I,J) where I is codim 2 perfect in s variables, satisfying G_{w-1} but not G_w,
-- and J is such that J:I is an s-residual intersection, with I/J the cokernel of a certain
--altered Macaulay matrix.
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

--programs to extract the list of total betti numbers from a BettiTally
totalBetti = method()
totalBetti(ZZ,BettiTally) := (j,B) ->(
     Bj := select(keys B, k->k_0==j);
    sum(Bj, k->B#k))
totalBetti(ZZ,Module) := (j,M) -> (
    totalBetti(j, minimalBetti M))
totalBetti BettiTally := B->(
    len = max apply(keys B, k->k_0);
    apply(len+1, j -> totalBetti(j,B)))
totalBetti Module := M ->(
    totalBetti minimalBetti M)
totalBetti Ideal := I -> totalBetti minimalBetti I
totalBetti (ZZ,Ideal) := (j,I) -> totalBetti (j, minimalBetti I)

--Test of duality. For minimal computation, keep Both => false
testDuality = method(Options =>{Verbose => true, Both => false})
testDuality(Ideal,Ideal,List) := o-> (I,J,L) ->(
    s := L_0; w := L_1; u' := L_2;
    u := min(u',s-1-u');
    if u<1 then error "u or s-1-u not positive";    
    <<"----------"<<"(u, s-1-u) =  "<< (u,s-1-u)<<"------------"<<endl;	
    if u<s-1-u then (  --in this case we need two resolutions
    <<"----------"<<"presentation of I^u/JI^(u-1) "<<"------------"<<endl;	
    if o.Both == false then Bu := minimalBetti(I^u/(J*I^(u-1)), LengthLimit =>1) else
    Bu = minimalBetti(I^u/(J*I^(u-1)));
    if o.Verbose == true then <<Bu<<endl<<endl);
    if u<=s-1-u then (
        <<"----------"<<"Betti table of I^(s-1-u)/JI^(s-2-u) "<<"------------"<<endl;	
	Bu' := minimalBetti(I^(s-1-u)/(J*I^(s-2-u)));
    << if o.Verbose == true then << Bu'<<endl<<endl);
    if u< s-1-u and (totalBetti Bu)_{0,1}  != (totalBetti Bu')_{s,s-1} then (<<endl << "is not dual"<<endl) else
    if u==s-1-u and (totalBetti Bu')_{0,1} != (totalBetti Bu')_{s,s-1} then (<<endl << "is not dual"<<endl) else
    <<endl << "is dual"<<endl<<endl;
)

testDuality(Ideal,Ideal,ZZ,ZZ) := o -> (I,J,s,w) ->(
    u := min (s-w,w-1); --note s-1-u = w-1, need this also >=1
    testDuality(I,J,{s,w,u},o)
    )


end--
restart
load "170217-dualityExample.m2"

time for s from 5 to 7  do(
for w from 3 to 2+(s)//2 do(
    <<"==========="<<"s and w: " << (s,w)<<"==========="<<endl;
    (I,J) = makeIJ(s,w);
    testDuality(I,J,s,w,Verbose =>false)
    ))

(s,w,u) = (4,4,2)
(I,J) = makeIJ(s,w);
testDuality(I,J,{s,w,u}, Verbose=>true, Both=>true)

(s,w,u) = (6,5,1)
(I,J) = makeIJ(s,w);
testDuality(I,J,{s,w,u}, Verbose => true)


--to run with "both" for 5 to 7, do
--C-u,<f12> 
--and insert
--GC_INITIAL_HEAP_SIZE=50G 
--before the M2 invocation.





