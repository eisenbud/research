S = ZZ/101[a,b,c]
R = S/ideal"a5"
(phi, psi) = approximation(module (ideal vars R)^10)
source  psi
betti res coker vars R
-----Where does "high syzygy" behavior begin?
--Conjecture: where regularity of the even and odd ext modules is 0 -- independently of whether there are socle elements in degree 0.
--but to produce the behavior, the CM approx method is necessary; our matrixFactorization script won't do it!
--need to test this conjecture further!


--First of all, both the even and odd regularities seem to
--be inherited by the MCM approx module.

--In the case of one of the syzygies of the res field in c=3,
--it seems that reg evenExtModule = 1, reg oddExtModule =0 is enough!!
--In case c= 4 even {2,1} seems to be good enough. Note that's a case where
--reg ExtModule = 4.

--One-step conjecture: if R is codim 1 in R', complete intersections in S,
--and  M is a CM module over R, then:
--the resoluttion of the "R'-CM-approx map" over S is equal to the 
--resolution of M over S 
--iff
--Ext_R(M,k) has trivial summands in degrees 0,1 and after factoring those out
--the CI operator is a nzd.
--Moreover, In this case, the Ext module of the essential R' CM approximation
--is (Ext_R(M,k)/socle)/t

--If this is true, then in the case when Ext_R(M,k) has regularity <= 1 AND if the reg Ext_R'(M',k) <= reg Ext_R(M,k), thi could continue
--inductively. Note that reg(E/tE) <= reg(E) if t is a quasi-regular element on E (that is: a nzd on E/H^0_mm(E)). On the other hand,
-- Ext_R'(M',k) ! =  Ext_R(M,k)/t, so we can't use this directly.

--A crucial question is whether the socle of Ext_R(M,k) is represented by a free summand of the resolution.

----------------- Where regularity and minimality criteria set in
---we should add a test for the presence of socle in Ext^0.
restart
loadPackage("MCMApproximations", Reload=>true)
low = -2
high = 4
c = 2; d=3;
S = setupRings(c,d);
R = S_c;
--Mc = coker matrix {{R_0,R_1,R_2},{R_1,R_2,R_0}} -- with 3 vars
-- Mc = coker matrix {{R_0,R_1,R_2},{R_1,R_2,R_3}} -- with 4 vars this is too slow
Mc = coker random(R^1, R^{2:-2})
Mc = coker random(R^2, R^{-2,-3})
time test(S,Mc,low,high)

--installPackage "MCMApproximations"
--installPackage "CompleteIntersectionResolutions"



--Conjecture 1: the "regularity of the successive MCM approximations is decreasing
restart
uninstallPackage "MCMApproximations"
installPackage "MCMApproximations"
loadPackage("MCMApproximations", Reload=>true)
loadPackage("CompleteIntersectionResolutions", Reload=>true)
c = 3
R =setupRings(c,3)
Rc=R_c
M0 = coker vars Rc
range  = toList(-2..3)

scan(range, i-> (
	MM0 = syzygyModule(i,M0);
	Ee := null; Eo:= null;
	(M,kkk,p) = setupModules(R,MM0);
	apply(c-1, j->(
	a := auslanderInvariant M_(c-1-j);
	phi = approximation(M_(c-1-j),Total=>false);
	b := numgens prune ker(kkk_(c-1-j)**phi);
	re := regularity (Ee = evenExtModule(M_(c-1-j)));
	ro := regularity (Eo = oddExtModule(M_(c-1-j)));	
	se := degree Hom(coker vars ring Ee, Ee);
	so := degree Hom(coker vars ring Eo, Eo);	
	<<{{i,c-1-j},{a,b},{re,se}, {ro, so}};<<endl;<<endl;
	flush;
	))
    ))



------image of essential approximation, compared with ker t.
restart
loadPackage("MCMApproximations", Reload=>true)
loadPackage("CompleteIntersectionResolutions", Reload=>true)

tensor (Ring,Matrix) := (R,phi) -> (
    RR' := map(R, ring phi);
    map(R**target phi, R**source phi, RR' matrix phi)
    )

--the following uses notation from "test";
--should also test whether the kernel of t is the image of phi all mod the max ideal.

L0 = apply(toList(low..high+low-1),i->(
	m1 := map(coker T.dd_(i+1), coker T.dd_(i+3), tt_(i+low)_2);
	m2 := phi_(i+2+low);
	{m1,m2}));

L1 = apply(toList(low..high+low-1),i->(
	m1 := tt_(i-low)_2;
	m2 := matrix phi_(i+2-low);
	{m1,m2}));

matrix{toList(low..high+low-1),
        apply(L1, p ->if KR(map(target p_0, source p_1, matrix p_0 * matrix p_1))!=0 then 1 else 0)}


L2 = apply(toList(low..high+low-1),i->(

	m1 := map(coker T.dd_(i+1), coker T.dd_(i+3), tt_(i-low)_2);
	m2 := phi_(i+2-low);
	--why can't we write m1*m2? the target of m2 is supposedly the same as the source of m1!
	map(target m1, source m2, matrix (m1) * matrix(m2))));

L3 = apply(toList(low..high+low-1),i->(
	m1 := tt_(i-low)_2;
	m2 := matrix phi_(i+2-low);
	{m1,m2};
	m1*m2))

///

///
--Test of the conjecture that, in the case of a CI of quadrics with at most one form
--of higher degree, the even and odd Betti numbers agree eventually with a single polynomial
--(Avramov's "one polynomial" conjecture.)
restart
loadPackage("MCMApproximations", Reload=>true)
S = ZZ/101[a,b,c,d]
ff = matrix"a2,b2,c3d2"
cod = numcols ff
R = S/ideal ff
M = coker random(R^{0,1}, R^{2:-1, 2:-2})
M = R^1/ideal"ab, c2,a3c+d4"
(ppe, r) = onePoly M
L1 = apply(r + 2*cod, j-> sub(ppe, {(ring ppe)_0=>j}))
L2 = apply(r+2*cod, i -> rank ((res(M, LengthLimit =>r+6))_i))
L1-L2 -- having one poly is equivalent to having 2*cod trailing zeros (if r is big enough
///

--study of regularity sequences:
test = method()
test(List,Module,ZZ,ZZ) := (S,Mc, low, high) ->(
c := length S -1;
R' := S_(c-1);
R := S_c;
RR' := map(R,R');
ff := presentation R;
K := coefficientRing R;
KR := map(K,R);
(M,kk,p) := setupModules(S,Mc);
<< regularitySequence(S,Mc)<<endl;
T := TateResolution(Mc,low,high);
tt := apply(toList(low+2..high), i-> makeT(ff, T, i));
phi' := apply(toList(low+1..high), --was high-2
    j->approximation(pushForward(RR', coker T.dd_j), Total => false));
phi := phi'/(ph ->  prune map(R**target ph, R**source ph, RR' matrix ph));
report := matrix{toList(low+2..high), 
       apply(toList(low+2..high), i->if isSurjective tt_i_(c-1) then 0 else 1),
       apply(toList(low+2..high), i->(numgens ker KR matrix phi_(i+low-1))),
       apply(toList(low+2..high), i->(regularity evenExtModule coker T.dd_i))};
<<"KEY:"<<endl;
<<"report_(0,j) = i : index of a free module F_i in T"<<endl;
<<"report_(1,j): whether the CI map emerging from F_i is surjective"<<endl;
<<"report_(2,j): whether the CM approx embeds mod the max ideal"<<endl;
<<"report_(3,j): regularity of the even ext module"<<endl;
report)
doc ///
   Key
    test
    (test, List, Module, ZZ, ZZ)
   Headline
    reports on factors related to the one-step resolution
   Usage
    report = test(S, Mc, low, high)
   Inputs
    S:List
     list of successive rings S_0, S_0/(f_1) .. S_c = S_0/(f_1..f_c)
    Mc:Module
     module over S_c
    low:ZZ
     start of window of Tate resolution
    high:ZZ
     end of window of Tate resoluion
    report:Matrix
     matrix of integers:
   Description
    Text
     "report_(0,j) = i : index of a free module F_i in T"
     "report_(1,j): whether the CI map emerging from F_i is surjective"
     "report_(2,j): whether the CM approx embeds mod the max ideal"
     "report_(3,j): regularity of the even ext module"
    Example
      low = -2; high = 4;
      c = 2; d=3;
      S = setupRings(c,d);
      R = S_c;
      Mc = coker random(R^1, R^{2:-2})
      Mc = coker random(R^2, R^{-2,-3})
      time test(S,Mc,low,high)
   SeeAlso
    regularitySequence
    socleDegrees
///
