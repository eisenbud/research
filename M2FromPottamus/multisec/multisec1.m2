From psorin@shire.math.columbia.edu Tue Oct  7 08:54:26 1997
Received: from msri.org by chern.msri.org (8.8.2/HUB)
	id IAA17164; Tue, 7 Oct 1997 08:54:25 -0700 (PDT)
Received: (from smap@localhost) by msri.org (8.8.2/8.7.2) id IAA02464 for <de@msri.org>; Tue, 7 Oct 1997 08:54:24 -0700 (PDT)
Received: from shire.math.columbia.edu(128.59.209.11) by msri.org via smap (V1.3)
	id sma002460; Tue Oct  7 08:53:57 1997
Received: from fifthave.math.columbia.edu (fifthave.math.columbia.edu [128.59.209.23])
	by shire.math.columbia.edu (8.8.5/8.8.5) with ESMTP id LAA09661;
	Tue, 7 Oct 1997 11:53:41 -0400
Received: from localhost (psorin@localhost)
	by fifthave.math.columbia.edu (8.8.5/8.8.5) with SMTP id LAA03019;
	Tue, 7 Oct 1997 11:53:33 -0400
X-Authentication-Warning: fifthave.math.columbia.edu: psorin owned process doing -bs
Date: Tue, 7 Oct 1997 11:53:33 -0400 (EDT)
From: Sorin Popescu <psorin@shire.math.columbia.edu>
To: David Eisenbud <de@msri.org>
cc: Mike Stillman <mike@math.cornell.edu>
Subject: multisec1.m2 June 2 (this seems to be the latest)
In-Reply-To: <19971007000311.06687@msri.org>
Message-ID: <Pine.LNX.3.96.971007115230.702D-100000@fifthave.math.columbia.edu>
MIME-Version: 1.0
Content-Type: TEXT/PLAIN; charset=US-ASCII
Status: RO
Content-Length: 9738
Lines: 331

-- Construct the variety of 3-secant lines, or 4-secant-lines, to
-- a curve or other scheme in P^3.
--FIXES the bug that the multisecant lines with an intersection at
--infinity are ignored.

--The following chooses the positions in an ideal with generators 
--of degree in a given range.
positionsByDegrees= (lo,high,I)->(
     positions(0..numgens source gens I-1, i -> 
	  degree I_i >={lo} and degree I_i <= {high})
     )

--The following is the inner loop of the functions 
--multisecant and multisecant2. Computes the ideal of 
--secants with the cell represented by S.
multisecantcell := (k,S,Sbase,phi,I,Ik)->(
     -- phi is a map from ring I to S
R := ring I;
J := phi I;
Jk:=phi Ik; --makes an ideal of S
Jk = coefficients({0},Jk);
Jk = Jk_1;
J = J+ideal Jk;
g = gens gb J;
mm = coefficients({0,1},leadTerm(3,g));
mons := mm_0;
coeffs := mm_1;
p = positionsByDegrees(0, k-1, ideal mons);
g = g_p;
mn := coefficients({0},g);
L:=substitute(mn_1, Sbase);
Ls:= ideal divideByVariable(gens gb L,Sbase_(-1));
if Ls==ideal(1_Sbase) then 
   ideal(1_R) 
else
    (A:=S/substitute(Ls,S); 
     ker map(A,R, substitute(phi.matrix,A)))
)


multisecant = (k,I) -> (
   --- k-secant lines to a curve V(I) in P^3, via initial terms
R := ring I;
kk :=coefficientRing R;
-- Make a matrix Ik whose entries are polynomials that
-- obviously contain the k-secants (assuming that no k-secant
-- is contained in V(I))
pos := positionsByDegrees(0,k-1,I);
comp := set elements(0..(numgens I -1)) - set pos;
comp = elements comp;
Ik := (gens I)_pos;
if  numgens source Ik>=2 then 
    Ik=gens (ideal Ik  : ideal (gens I)_(comp)) ;
-- Loop through the affine cells of the Grassmannian of lines in P^3
secantIdealList := 
  apply(0..2,i->(
     apply(i+1..3,j->(
	a:=quote a;
        b:=quote b;
        z:=quote z;
        s:=quote s;
        t:=quote t;
	Sbase := kk[a_(i+1)..a_(j-1),a_(j+1)..a_3,
		      b_(j+1)..b_3,z];
	S := kk[s,t,a_(i+1)..a_(j-1),a_(j+1)..a_3,
		      b_(j+1)..b_3,z, 
		      MonomialOrder=>Eliminate 2];
        phimat := map(S^2,4,(u,v)->(
		  if u==0 then (
		       if v<i or v==j then 0 else
		       if v==i then z*s else
		       s*a_v)
		  else (
		       if v<j then 0 else
		       if v==j then z*t else
		       t*b_v)));
	phimat = map(S^1,S^2,{{1,1}})*phimat;
	phi := map(S,R,phimat);
        multisecantcell(k,S,Sbase,phi,I,Ik)
	))));
intersect splice secantIdealList
)





document {quote multisecant,
         TT "-- multisecant(k:ZZ,I:homogeneous ideal in 4 variables)",BR,
NOINDENT,
"Returns the ideal in P^3 of the union of the k-secant lines to 
a scheme defined by the ideal I.",
PARA,
"This script divides the Grassmannian of lines in P^3 into
6 affine sets, the open sets of the Schubert cycles. The
secants contained in each are computed, then the intersection
of the ideals is returned. Thus the scheme structure of what
is returned has little meaning except in the principal open
set of lines not meeting the line (*,*,0,0). However the
script runs many times faster than multisecant2, which 
uses 5 open cells. The method used in each affine set is to
let t be a parameter on the generic line in the set, and
collect the coefficients of 1,t,...,t^(k-1) in a Groebner
basis taken with respect to an order eliminating t. To this
is added the ideal (I_(<k) : I) (applied to the generic point
of the line), where I_(<k) denotes the ideal generated by the
elements of I of degree <k. ",
EXAMPLE 
///
-- complete intersection of cubic and quartic;
-- the 4-secants are the 27 lines.  
-- The 3-secant surface seems to take a LONG time to compute.
kk=ZZ/101
R = kk[x_0..x_3]
I1 = ideal(sum(4,i->x_i^4),sum(4,i->x_i^3))
--multisecant(3,I1)
multisecant(4,I1)
	 ///,
	 EXAMPLE 
///-- rational quintic with unique quadrisecant
I2 = ker map(R,R,
     {x_0^5, x_0^4*x_1-x_0^3*x_1^2, x_0^3*x_1^2+x_0^2*x_1^3+x_0*x_1^4, x_1^5})
multisecant(4,I2)
multisecant(3,I2)
         ///,
	 EXAMPLE 
///I3 = monomialCurve(R,{1,3,4})
multisecant(3,I3)
multisecant(4,I3)
///,
SEEALSO "multisecant2",
"   Created by DE+SP+MS, May 31, 1997."
	}


--------------------------------------

multisecant2 = (k,I) -> (
   --- k-secant lines to a curve V(I) in P^3, via initial terms
R := ring I;
kk :=coefficientRing R;
--
-- Make a matrix Ik whose entries are polynomials that
-- obviously contain the k-secants (assuming that no k-secant
-- is contained in V(I))
pos := positionsByDegrees(0,k-1,I);
comp := set elements(0..(numgens I -1)) - set pos;
comp = elements comp;
Ik := (gens I)_pos;
if  numgens source Ik>=2 then 
    Ik=gens (ideal Ik  : ideal (gens I)_(comp)) ;
-- Loop through the affine cells of the Grassmannian of lines in P^3
secantIdealList := 
  apply(0..2,i->(
     apply(i+1..3,j->(
        a:=quote a;
        b:=quote b;
        z:=quote z;
        t:=quote t;
	Sbase := kk[a_(i+1)..a_(j-1),a_(j+1)..a_3,
	              b_(i+1)..b_(j-1), b_(j+1)..b_3,z];
	S := kk[t,a_(i+1)..a_(j-1),a_(j+1)..a_3,
	              b_(i+1)..b_(j-1), b_(j+1)..b_3,z, 
		      MonomialOrder=>Eliminate 1];
        phimat := map(S^2,4,(u,v)->(
		  if u==0 then (
		       if v<i or v==j then 0 else
		       if v==i then z^2 else
		       z*a_v)
		  else (
		       if v<=i then 0 else
		       if v==j then z*t else
		       t*b_v)));
	phimat = map(S^1,S^2,{{1,1}})*phimat;
	phi := map(S,R,phimat);
        multisecantcell(k,S,Sbase,phi,I,Ik)
	))));
intersect splice secantIdealList
)



document {quote multisecant2,
         TT "-- multisecant2(k:ZZ,I:homogeneous ideal in 4 variables)",BR,
NOINDENT,
"Returns the ideal in P^3 of the union of the k-secant lines to 
a scheme defined by the ideal I.",
PARA,
"This script divides the Grassmannian of lines in P^3 into
6 affine open sets, the open sets of the Schubert cycles. The
secants contained in each are computed, then the intersection
of the ideals is returned. 
The scheme structure returned presumably has some significance.
However the
script runs many times slower than multisecant2, which 
uses 6 locally closed affine sets. The method used in each affine set is to
let t be a parameter on the generic line in the set, and
collect the coefficients of 1,t,...,t^(k-1) in a Groebner
basis taken with respect to an order eliminating t. To this
is added the ideal (I_(<k) : I) (applied to the generic point
of the line), where I_(<k) denotes the ideal generated by the
elements of I of degree <k. ",
EXAMPLE 
///
-- complete intersection of cubic and quartic;
-- the 4-secants are the 27 lines.  
-- The 3-secant surface seems to take a LONG time to compute.
kk=ZZ/101
R = kk[x_0..x_3]
I1 = ideal(sum(4,i->x_i^4),sum(4,i->x_i^3))
--multisecant2(3,I1)
multisecant2(4,I1)
	 ///,
	 EXAMPLE 
///-- rational quintic with unique quadrisecant
I2 = ker map(R,R,
     {x_0^5, x_0^4*x_1-x_0^3*x_1^2, x_0^3*x_1^2+x_0^2*x_1^3+x_0*x_1^4, x_1^5})
multisecant2(4,I2)
multisecant2(3,I2)
         ///,
	 EXAMPLE 
///I3 = monomialCurve(R,{1,3,4})
multisecant2(3,I3)
multisecant2(4,I3)
///,
SEEALSO "multisecant",
"   Created by DE+SP+MS, May 31, 1997."	}
     
 
///
kk=ZZ/101
R = kk[x_0..x_3]
I1 = ideal(sum(4,i->x_i^4),sum(4,i->x_i^3))
I2 = ker map(R,R,
     {x_0^5, x_0^4*x_1-x_0^3*x_1^2, x_0^3*x_1^2+x_0^2*x_1^3+x_0*x_1^4, x_1^5})     
I3 = monomialCurve(R,{1,3,4})
     --times are 5ave

time multisecant2(3,I3) ---1.17
time multisecant(3,I3)--.7

time multisecant2(4,I2) --1.21
time multisecant(4,I2) -- .73

time multisecant2(3,I2) --- 102.27
time multisecant(3,I2) -- 9.1

--time multisecant2(3,I1) -- Danger!
--time multisecant(3,I1)  -- Danger ! >90min on 5ave

time multisecant2(4,I1) --- 2.86
time multisecant(4,I1) --- 1.36
///



--The following is
--NOT USEABLE now (5/31/97); needs a version of pushforward that
--works for inhomogeneous modules.

multisecant2p = (k,I) -> (
     -- k-secant variety to I in P^3 via pushforward (I must contain no lines)
R = ring I;
kk =coefficientRing R;
a:=quote a;
b:=quote b;
z:=quote z;
t:=quote t;
--
-- Make a matrix Ik whose entries are polynomials that
-- obviously contain the k-secants (assuming that no k-secant
-- is contained in V(I))
pos = positionsByDegrees(0,k-1,I);
comp = set elements(0..(numgens I -1)) - set pos;
comp = elements comp;
Ik = (gens I)_pos;
if  numgens source Ik>=2 then 
    Ik=gens (ideal Ik  : ideal (gens I)_(comp)) ;
-- Loop through the affine cells of the Grassmannian of lines in P^3
secantIdealList = 
  apply(0..2,i->(
     apply(i+1..3,j->(
	Sbase = kk[a_(i+1)..a_(j-1),a_(j+1)..a_3,
	              b_(i+1)..b_(j-1), b_(j+1)..b_3,z];
	S = kk[t,a_(i+1)..a_(j-1),a_(j+1)..a_3,
	              b_(i+1)..b_(j-1), b_(j+1)..b_3,z];
        phimat = map(S^2,4,(u,v)->(
		  if u==0 then (
		       if v<i or v==j then 0 else
		       if v==i then z^2 else
		       z*a_v)
		  else (
		       if v<=i then 0 else
		       if v==j then z*t else
		       t*b_v)));
	phimat = map(S^1,S^2,{{1,1}})*phimat;
	phi = map(S,R,phimat);
        temp = multisecantpcell(k,S,Sbase,phi,I,Ik);
	print temp;
	temp))));
print secantIdealList;
intersect toSequence flatten secantIdealList
)

multisecantpcell = (k,S,Sbase,phi,I,Ik)->(
--- correct in generic coordinates, that is
--- when the projection is finite. The projection
--- is finite on the affine z=1. When pushForward
--- can accomodate inhomogeneous modules, add z-1 to
--- ideal j and try again ... 05/30/97
R = ring I;
z = S_(-1); -- last var of S, with which we'll homogenize.
J = phi I;
Jk=phi Ik;
Jk = coefficients({0},Jk);
Jk = Jk_1;
J = J+ideal Jk;
J=ideal divideByVariable(gens J,z);
j = divideByVariable(gens gb J,z);
A=S/ideal j;
f = map(A,Sbase);
M = trim pushForward(f,A^1);
dets=minors(numgens M - k + 1, presentation M);
z = Sbase_(-1);
L=divideByVariable(gens gb dets,z);
L= substitute(L, S);
A=S/ideal L; 
ker map(A,R, substitute(phi.matrix,A))
)


