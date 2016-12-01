
HPR=ZZ[tt,b_0..b_n] -- Hilbert Poly Ring
bs=(vars HPR)_{1..n+1} -- Betti Sequence

bin=alpha->product(n-1,i->alpha+tt+n-1-i) --binomial coeff numerator

hp=method() --hilb poly as a funct of betti numbers b_i (vars) in degree d_i (in ZZ).
hp(List):=a->sum(#a,i->(-1)^i*b_i*bin(-a_i))


bettiNumbers=method()
bettiNumbers(List):=a->(pp:=hp(a); -- a is the list of degrees
     --returns betti nums of a pure complex
     pcoef:=(coefficients(pp,Variables=>{tt}))_1;
     bb:=transpose syz substitute(diff(bs,pcoef),ZZ);
     if bb_0_0>0 then bb else -bb)

rangeOK=(d,r,n)->#d==n+1 and 0<= d_0 and 
   apply(n,i-> d_i<d_(i+1))==toList(n:true) and d_n<=r+n 
   --tests whether degree seq is non-neg, strictly increasing, of the right length n, and last elt
   -- is bounded by reg + num vars, and 

bettiMatrix=method()
bettiMatrix(List):=d->(
     --betti matrix of a pure complex from list of degs
     if  rangeOK(d,r,n) then (
     bb:=bettiNumbers(d);
     matrix apply(r+1,i->apply(n+1,j->if (d_j)==i+j then bb_(0,j) else 0))
     ) else "wrong Range")

nextLower=(d)->(if d_0>0 then join( {d_0-1},d_{1..n}) else (
	  --returns A deg seq adjacent to d and below it (chooses one such)
	  k:=1; 
	  while (d_k-1==d_(k-1) ) do (k=k+1);
	  join(d_{0..k-1},{d_k-1},d_{k+1..n})))
nextUpper=(d)->(if d_n<n+r then join(d_{0..n-1},{d_n+1}) else (
	  --same but above
	  k:=n; 
	  while (d_k-1==d_(k-1) ) do (k=k-1);
	  join(d_{0..k-2},{d_(k-1)+1},d_{k..n})))

     
lowerRange=(d)->(A:={d};if (
	  --returns a maximal chain of deg seqs below d
	  d =!= toList(0..n) ) then ( 
          e:=nextLower(d);
	  A=join(A,lowerRange(e)););
     	  A)	  
upperRange=(d)->(A:={d};if (
	  --same but above
	  d =!= toList(r..n+r) ) then ( 
          e:=nextUpper(d);
	  A=join(A,upperRange(e)););
     	  A)	  

rangeMatrices=(e)->apply(n+1,k-> matrix apply(r+1,i->apply(n+1,j->
	       --takes a deg seq, returns list of mats, i-th has 
	       --a one in posn e_i-i, i
	       if  k==j and e_k==i+j then 1 else 0)))

supportingEquation=(d,e)->(
     --given degree sequences d < e, with e-d has ones in two consecutive places (the box),
     --computes the supporting equation of the exterior facets involving this edge.
     A:=matrix apply(lowerRange(d),c->join(toSequence entries bettiMatrix(c)));
     B:=matrix apply(upperRange(e),c->join(toSequence entries bettiMatrix(c)));
     C:=matrix apply(rangeMatrices(e),c->join(toSequence entries c));
     D:=(entries transpose syz(A||B||C))_0;
     A=matrix apply(r+1,i->apply(n+1,j->D_((n+1)*i+j)));
     de:=middleComplex(d,e);
     B=bettiMatrix(de);
     if dotProduct(A,B)>0 then A else -A)

dotProduct=(A,B)->sum(r+1,i->sum(n+1,j->A_(i,j)*B_(i,j)))
--dot product of matrices as vectors

peskineSzpiro=(r,n)->apply(n+r+1,k->matrix apply(r+1,i->apply(n+1,j->
--returns (redundant) list of n+r+1 Peskine-Szpiro relations in hilb function form
--(the Hilb fcn values from *** to ***) Note: the P-S eqns in this sense are
--\chi(O(m)\otimes M)= 0 .
	       (if k<r then 1 else (-1)^(k-r))*(-1)^(n-j)*
	       binomial(n+r-k-i-j+n-1,n-1)
	       )))
PS=peskineSzpiro(r,n); -- Note that this becomes a global variable

numericalComplex=A->(AA:=A;apply(n+r+1,i->(
	       ss:=if i<=r then AA_(r-i,n) else AA_(0,n-i+r);
	       AA=AA-ss*PS_i;
	       ss)))
--The numerical complex that flips the "upper" eqn to the "lower" eqn, written
--as the sequence of coefficients of the PS-equations.

flipEquation=(A)->(aa:=numericalComplex(A);
     apply(n+r+1,c->A-sum(c,i->aa_(i)*PS_(i))))
upperEquation=(A)->(L:=flipEquation(A);L_(#L-1))
--the necessary lin comb of the PS equations.

middleComplex=(d,e)->(t:=1;
     L:=apply(n+1,i->(t=t*if d_i==e_i then 1 else -1 ));
     apply(n+1,c->if L_c==1 then e_c else d_c))

nextPure=(d,k)->if d_k+1==d_(k+1) and d_(k+2)>d_(k+1)+1 then 
     apply(#d,i->if i<k or i>( k+1) then d_i else d_i+1) else error("no next pure sequence")
--in the case of two degree sequences differing by one in two consec places, computes
--the degree sequence in between.


twoRowPureComplex=(d0,k,reg)->apply(n+1,i->if i<k then d0+i else d0+i+reg-1)
--deg sequence of a two-row pure resolution
--with generator in degree d0, k>=2 position of the step, reg=regularity-d0

twoRowFacet=(d0,k,reg)->(
     --returns the facet equation and other info for the facet corresponding to an
     --upper complex with degrees as produced by twoRowPureComplex
     d:=twoRowPureComplex(d0,k,reg);
     e:=nextPure(d,k-2);
     de:=middleComplex(d,e);
     R:=sum(rangeMatrices(e))+sum(rangeMatrices(d))+sum(rangeMatrices(de));
     A:=supportingEquation(d,e);
     ss:=numericalComplex(A);
     Aminus:=upperEquation(A);
     (A,R,ss,Aminus))

threeRowFacet=(d0,k,steps)->(
     --similar for a "three-row complex" (one "elevator", ie
     --------
             
	     --
	     --
	       
	       ------------)
     --generator in degree d0, 1<k position of the step, 
     --0<=step_0,1<=step_1 step size)
     d:=apply(n+1,i->if i<k then d0+i else if i<k+2 then d0+i+steps_0 else d0+i+steps_0+steps_1);
     e:=nextPure(d,k);
     de:=middleComplex(d,e);
     R:=sum(rangeMatrices(e))+sum(rangeMatrices(d))+sum(rangeMatrices(de));
     A:=supportingEquation(d,e);
     ss:=numericalComplex(A);
     Aminus:=upperEquation(A);
     (A,R,ss,Aminus))

end
restart
n=4
r=10
load "BScomplex2.m2"
d={3,4,5,9,10,12,13,16}
e=nextPure(d,1)
f=nextPure(d,3)
supportingEquation(d,e)
supportingEquation(d,f)

restart
n=4
r=10
load "BScomplex2.m2"
d={3,4,6,7,8}
d={3,4,8,9,10}
e=nextPure(d,3)

supportingEquation(d,e)



(threeRowFacet(3,1,{0,4}))_{0,2}
(threeRowFacet(3,1,{1,3}))_{0,2}
(threeRowFacet(3,1,{2,2}))_{0,2}
data=(d0,reg)->apply(2..n,k->twoRowFacet(3,k,3))

data(2,3)

