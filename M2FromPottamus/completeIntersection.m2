{*
Code to analyze resolution over a complete intersection.
In particular, the goal is to compute the matrix of the i-th
differential d_i in the form
(d' |  *       )
---------------
(0  | d_(i-2)  )
and to do so in "adapted" bases for the columns.
*}

{*
Caveat: For the moment at least, the code assumes that
R  = S/(f1..fc) is a homogeneous complete intersection, and 
S is a polynomial ring over a field.
*}

ExtModule = method()
ExtModule(Module) := M -> (
     --If M is a module over a complete intersection R
     --of codim c, the script returns 
     --Ext^*(M,(ring M)^1/(ideal vars ring M))
     --graded in POSITIVE degrees
     --as a module over the polynomial ring kk[X_1..X_(codim R)],
     --where the vars have degree 2
     if M == 0 then return 0;
     kk := coefficientRing R;
     kkk := (ring M)^1/(ideal vars ring M);
     E := Ext(M,kkk);
     TE := ring E;
     c := numgens source presentation R;
     T := kk[X_0..X_(c-1), Degrees => toList(c:{2})];
     v := map(T,
	  ring E, 
	  vars T | matrix{toList ((numgens R):0_T)}, 
	  DegreeMap => i -> {-first i} );
     prune coker v presentation E)


///
--the vars of the new ring do NOT correspond exactly to the complete intersection generators given.
restart
load "completeIntersection.m2"
kk = ZZ/7
S = kk[a,b]
R = S/ideal(a^5, b^5)-- replacing this by 
--R1 = S/ideal(a^5,a^5+b^5) --produces the same ext module
///

evenExtModule = M -> (
     --If M is a module over a complete intersection R
     --of codim c, the script returns 
     --Ext^(even)(M,(ring M)^1/(ideal vars ring M))
     --graded in POSITIVE degrees
     --as a module over the polynomial ring kk[X_1..X_(codim R)],
     --where the vars have degree 1
     E := ExtModule M;
     P := positions(flatten degrees E, even);
     Ee:=prune image (E_P);
     T := ring E;
     kk:= coefficientRing T;
     T1 := kk[X_0..X_(numgens T -1)];
     v1 = map(T1, T, DegreeMap => i->{(first i)//2});
     coker v1 presentation Ee
     )

oddExtModule = M -> (
     --If M is a module over a complete intersection R
     --of codim c, the script returns 
     --Ext^(odd)(M,(ring M)^1/(ideal vars ring M))
     --graded in POSITIVE degrees
     --as a module over the polynomial ring kk[X_1..X_(codim R)],
     --where the vars have degree 1
     E := ExtModule M;
     P := positions(flatten degrees E, odd);
     Eo:=prune image (E_P);
     T := ring E;
     kk:= coefficientRing T;
     T1 := kk[X_0..X_(numgens T -1)];
     v1 = map(T1, T, DegreeMap => i->{(first i)//2});
     coker v1 presentation Eo
     )

rewriteCompleteIntersection = (f, F) -> (
          {*
     If F = {{g0,..,gn}} is a matrix of 
     minimal generators of a
     complete intersection R, and f is a minimal generator of 
     ideal F, this returns a matrix of (homogeneous) minimal
     generators of ideal F with first entry f.
     *}
     const := map((ring F)/ideal vars ring F, ring F);
     f1 := sub(f, ring F);
     ff := map(target F, (ring F)^1, matrix{{f1}});
     h := flatten entries (ff//F);
     m := first positions(h, x -> 0!=const x);
     map(target F, source F, (i,j)-> if j==m then f1 else F_j_0)
     )

generalize = F ->(
     --Given a 1 x c matrix F whose entries are a homogeneous complete
     --intersection, reorder F if necessary so that the lowest
     --degrees are last, and then make a general triangular
     --transformation, adding multiples of the later elements to
     --the earlier. Return the new matrix G.
     if not isHomogeneous F then error("input should be homogeneous");
     S := ring F;
     G := sort (F, DegreeOrder => Descending);
     change1 := random(source G, source G);
     change := map(source G, source G, (i,j)->
	       if i>j then change1_(i,j) else
	       if i == j then 1_S else
	       0_S);
     G*change)

///
restart
load "completeIntersection.m2"
kk= ZZ/101
S = kk[x,y,z]
f = x^2
F = map(S^1, S^{-2, -3}, matrix"x2, z3")
G = generalize (F|F)
rewriteCompleteIntersection(x^2*z+z^3, F)
///


makeT = method()
makeT(Matrix, ChainComplex,ZZ) := (F,G,i) ->(
     {*
     If F is a 1 x m  matrix and
     G is a resolution of a module at least up to the i-th step,
     over R = S/(ideal F), this returns a map
     G_i\otimes source F \to G_{i-2} giving
     operators corresponding to the entries of F.
     *}
     R := ring G;
     S := ring F;
     if not isHomogeneous F then error("first argument must be homogeneous");
     if S =!= ring presentation R then error("rings don't match");
     d0 := lift(G.dd_i, S);
     d1 := lift(G.dd_(i-1), S);
     allMaps := (d1*d0)//((target d1)**F);
     print isHomogeneous allMaps;
     I := id_(source F);
     ret := map(R,S);
     degs := - degrees source F;
     apply(rank source F,
	  j -> map(R^{degs_j}**G_(i-2), 
	       G_i, ret(((target d1)**I^{j})*allMaps)))
     )

makeT' = method()
makeT'(Matrix, ChainComplex,ZZ) := (F,G,i) ->(
     {*
     If F is a 1 x m  matrix and
     G is a resolution of a module at least up to the i-th step,
     over R = S/(ideal F), this returns a map
     G_i\otimes source F \to G_{i-2} giving
     operators corresponding to the entries of F.
     *}
     R := ring G;
     S := ring F;
     c := numcols F;
     S':= S/ideal F_{0..c-2};
     if not isHomogeneous F then error("first argument must be homogeneous");
     if S =!= ring presentation R then error("rings don't match");
     d0 := lift(G.dd_i, S);
     d1 := lift(G.dd_(i-1), S);
     allMaps := (d1*d0)//((target d1)**F);
     print isHomogeneous allMaps;
     I := id_(source F);
     ret := map(S',S);
     degs := - degrees source F;
     apply(rank source F,
	  j -> map(ret(S^{degs_j}**target(d1)),
	       ret(source d0), ret(((target d1)**I^{j})*allMaps)))
     )

makeT'(Matrix, Matrix, ChainComplex,ZZ) := (F,liftedDifff,G,i) ->(
     {*
     If F is a 1 x m  matrix and
     G is a resolution of a module at least up to the i-th step,
     over R = S/(ideal F), this returns a map
     G_i\otimes source F \to G_{i-2} giving
     operators corresponding to the entries of F.
     The matrix liftedDiff is a specified 
     lifting of the differential
     G_i -> G_(-1) = G.dd_i.
     *}
     R := ring G;
     S := ring F;
     c := numcols F;
     S':= S/ideal F_{0..c-2};
     if not isHomogeneous F then error("first argument must be homogeneous");
     if S =!= ring presentation R then error("rings don't match");
     d0 := liftedDiff;
     d1 := lift(G.dd_(i-1), S);
     allMaps := (d1*d0)//((target d1)**F);
     print isHomogeneous allMaps;
     I := id_(source F);
     ret := map(S',S);
     degs := - degrees source F;
     apply(rank source F,
	  j -> map(ret(S^{degs_j}**target(d1)),
	       ret(source d0), ret(((target d1)**I^{j})*allMaps)))
     )

syzygy = method()
syzygy(ZZ, Module) := (i,M) ->(
     F := res(M, LengthLimit => i);
     prune image F.dd_i)     

highSyzygy = N -> syzygy(1+regularity ExtModule N, N)

CIFiltration1 = method()
CIFiltration1(Module, RingMap) := (M,red) ->(
     {*
     M is a module over a complete intersection R that is a "high" syzygy;
     (means: Ext(M,k) has regularity zero, positive depth, and M is a second syzygy);
     red is a ring homomorphism R' -> R = R'/f;
     --script returns a resolution of M as an R'-module, of the form
     -- G3 --> G_2 --> G1++FF1 --> G0++FF0
     --such that G is a resolution of an R'-module MM
     --on which f is a nonzerodivisor.
     *}
     R := ring M;
     R' := source red;
     F := res (M, LengthLimit => 3);
   --create two steps of "co-resolution" of M.
--     Fminus := R^{2}**dual res (image dual  F.dd_1, LengthLimit => 2);
     Fminus := dual res (image dual  F.dd_1, LengthLimit => 2);
   --test1
     if Fminus.dd_0*F.dd_1!=0 then error "coresolution didn't work";
   --create operators on a lift
     M' := prune pushForward(red, M); -- M as a module over R'
     FF := res(M', LengthLimit => 3);
   --test2
     if rank FF_1 != rank F_1 then error"M needs more relations over R'";
     d1 = FF.dd_1;
     d0 := sub(Fminus.dd_0, R');
     dminus1 := sub(Fminus.dd_(-1), R');
     fmatrix := gens ker red;
     T1 := (d0*d1)//(fmatrix **id_(target d0));
     T0 := (dminus1*d0)//(fmatrix**id_(target dminus1));
   --testT
     if coker T1 != 0 then error"T1 not surjective";
     if coker T0 != 0 then error"T0 not surjective";
     iG0 := syz T0;
     G0 := source iG0;
     iG1 := syz T1;
     G1 := source iG1;
     (pG0,iF0') := splittings(iG0,T0);
     (pG1,iF1') := splittings(iG1,T1);
     dG1 := pG0*FF.dd_1*iG1;

     MM := coker dG1;
     MMToM' := map(M', MM, iG0);
     F1'ToG0 := pG0*FF.dd_1*iF1';
     F1'ToF0' := T0*FF.dd_1*iF1';
     {MMToM', F1'ToG0, F1'ToF0'}
     )

CIFiltration = method()
CIFiltration(Module, RingMap) := (M, red)->(
     --Given a complete intersection morphism red: R_0 -> R_c = R_0/ideal regSeq,
     --of codimension c
     --and an R-module M such that
     --M is a "high syzygy" and regSeq = presentation R is a sufficiently general set of 
     --generators,
     --the script returns a series of maps 
     -- i_c: M_c -> M_(c-1) ... i_1: M_1 -> M_0 = M
     regSeq := gens ker red;
     if min flatten degrees source regSeq < 2 then error "regular sequence must be in square of max ideal";
     c := rank source regSeq;
     R := ring M;
     RList := apply(c, i-> (source red)/ideal(regSeq_{0..i-1})) | {R}; -- R = RList_(c+1).;
     --RList_i = S/(first i elments of regSeq)
     redList := apply(c, i -> map(RList_(i+1), RList_i));
     --redList_i is the projection from RList_i to RList_(i+1).
     M1 := M;
     CIF := null;
     ans :=   apply(c-1, i -> (
	       CIF = CIFiltration1(M1, redList_(c-1-i));
	       M1 = source (CIF_0);
	       CIF)
	  )
     )

testInclusion = (X,R) -> (
     R1 := ring X_0;
     testModule = pushForward(map(R,R1), R^1);
     kernel (testModule**X_0) == 0)
     
     
///
restart
LL = LengthLimit
break
load "completeIntersection.m2"
kk= ZZ/101

S = kk[x,y,z]
regSeq = map(S^1, S^{3:-3}, generalize matrix"x3,y3,z3")
R = S/ideal regSeq
re = map(R,S)
N = coker random(R^2, R^{1:-1,2:-2})

S = kk[x,y,z,w]
regSeq = map(S^1,, generalize matrix"x3,y2,z3,w4")
R = S/ideal regSeq
re = map(R,S)
N = R^1/ideal"x2+w2, xy,xw3,xz"

M = highSyzygy N;
CIF = CIFiltration(M, re);

--something went wrong with these inputs, and I can't figure out what
ii76 : toString regSeq

oo76 = matrix {{42*x^4-31*x^3*y-44*x^2*y^2-44*x*y^3-29*y^4-13*x^3*z-32*x*y^2*z-46*y^3*z+24*y^2*z^2+33*x*z^3-42
       *y*z^3-35*z^4+21*x^3*w-43*x*y^2*w+16*y^3*w-25*y^2*z*w+28*z^3*w-42*y^2*w^2+w^4,
       17*x^3-13*x*y^2-20*y^3-50*y^2*z+z^3-8*y^2*w, x^3+34*x*y^2+6*y^3+14*y^2*z-20*y^2*w, y^2}}

ii74 : toString presentation M

oo74 = matrix {{y, w^2, x^2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, -y, y, x, w^2, x^2,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, y, x, 0, w^2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0}, {0, 0, 0, -y, 0, -x*y, w^2, x^2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0,
       0, -y, y, 0, 0, 0, 0, w^2, x^2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, y, x, 0, 0, 0, 0,
       x^2+w^2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0, y, 0, 0, 0, 0, x*y, 0, -w^2, x^2-w^2, 0, 0,
       0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, y, x, 0, 0, 0, 0, w^2, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0,
       0, 0, 0, -y, x^2, 0, 0, w^2, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -y, y, 0, x, x,
       0, x^2, w^2, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -y, 0, -x, -x, 0, -w^2, 0, 0, 0, 0, 0}, {0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, -y, x^2+w^2, -x*y, 0, w^2, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, -y, -y, x^2, -x*y, 0, w^2, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, y,
       -y, 0, x^2, -w^2, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -y, -x, -w^2, -w^2, 0}, {0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x*y, x^2-w^2}}

ii75 : toString re

oo75 = map(S/(42*x^4-31*x^3*y-44*x^2*y^2-44*x*y^3-29*y^4-13*x^3*z-32*x*y^2*z-46*y^3*z+24*y^2*z^2+33*x*z^3-42*y
       *z^3-35*z^4+21*x^3*w-43*x*y^2*w+16*y^3*w-25*y^2*z*w+28*z^3*w-42*y^2*w^2+w^4,17*x^3-13*x*y^2-20*y^3-50*y
       ^2*z+z^3-8*y^2*w,x^3+34*x*y^2+6*y^3+14*y^2*z-20*y^2*w,y^2),S,{x, y, z, w})






--tests:
moduleList = {M} | CIF/(X -> source X_0);
moduleList/(X -> betti res X)
moduleList/ring
testInclusion(CIF_0, R)
for i from 1 to #CIF-1 do print testInclusion(CIF_i, ring CIF_(i-1)_0)
#CIF

///

///
restart
LL = LengthLimit
break
load "completeIntersection.m2"
kk= ZZ/101

--codim 2 example
S = kk[x,y]
regSeq = generalize map(S^1, S^{2:-5}, matrix"x5, y5")
--codim 3 example.
S = kk[x,y,z]
regSeq = generalize map(S^1, S^{3:-3}, matrix"x3,y3,z3")

R = S/ideal regSeq
N = coker random(R^2, R^{1:-1,3:-4})
re = map (R,S/ideal regSeq_{0..numgens S -2})
ans = CIFiltration1(M = highSyzygy N , re);
betti res (N, LL=> 8)
R' = ring ans_0
ans_0
MM = source ans_0
M' = target ans_0
matrix ans_0
betti res M'
betti res MM
rank source ans_1
rank target ans_2
degrees source ans_1

u = map( R**target ans_0, R**source ans_0, re matrix ans_0)
ker u ==0

///

--the following is NOT a good thing to do, because the operator depends 
--not on f but on the complementary space.
makeT(RingElement, ChainComplex, ZZ) := (f,G,i) ->(
     {*
     If F = {{f,f1, f2,..,fn}} is a matrix of 
     minimal generators of a

     If f is a minimal generator of the defining ideal of a     
     complete intersection R = S/(f, f1...), and 
     G is a resolution of an R-module at least up to the i-th step,
     this returns a map
     G_i \to G_{i-2} giving
     the operator corresponding to f.
    
     *}
     F := presentation ring G;
     S := ring F;
     R := ring G;
     if S =!= ring presentation R then error("rings don't match");
     F1 := rewriteCompleteIntersection(f,F);
     if not isHomogeneous F1 then error("rewritten complete intersection not homogeneous");
     I1 := ideal F1_{1..numgens source F1-1};
     S1 := S/I1;
     d0 := S1**lift(G.dd_i, S);
     d1 := S1**lift(G.dd_(i-1), S);
     ret := map(R,S1);
     degf =  (degrees source F1)_0;     
     map(R^{-degf}**G_(i-2), G_i, ret( (d1*d0)//((target d1)**F1_{0}) ))
     )
///
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y,z]
F = map(S^1, S^{-2,-3}, matrix"x2, z3")
f0 = z^3
f1 = x^2*z+z^3
rewriteCompleteIntersection(f1, F)
R = S/ideal F
M = R^1/ideal gens R
G = res(M,LengthLimit => 5)

pushForward(map(R,S),M)
makeT(F,G,4)
oo/isHomogeneous
makeT(f1,G,4)
isHomogeneous oo
///
--same problem as the previous
isSurj = (f,G,i) ->(
     {*
     Assuming that G is a resolution over a complete intersection,
     f = f1, f2, ...
     returns "true" iff the operator G_i -> G_(i-2)
     corresponding to f is surjective.
     *}
     v := makeT(f,G,i);
     0 == coker v
     )
///
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y,z]
F = map(S^1, S^2, matrix"x2, z3")
f0 = z^3
f1 = x^2*z+z^3
rewriteCompleteIntersection(f1, F)
R = S/ideal F
M = R^1/ideal gens R
G = res(M,LengthLimit => 5)
v = makeT(f0,G,4)
0==coker v
isSurj(f0, G, 1)
G1 = res( coker transpose G.dd_5, LengthLimit => 10)
for i from 2 to 10 list isSurj(f0, G1, i)
for i from 2 to 10 list isSurj(f1, G1, i)
///

splittings = method()
splittings (Matrix, Matrix) := (a,b) -> (
     {*
     Assuming that (a,b) are the maps of a right exact
     sequence 
         a      b
     A ----> B ----> C ----> 0 
     
     with B, C free,
     the script produces a pair of maps sigma, tau
     with tau: C --> B a splitting of b and
     sigma: B --> cover A such that a*sigma+tau*b = 1_B.
     *}
     if not isFreeModule source b then error("source b not free");
     if not isFreeModule target b then error("target b not free");
     (tau,remtau) := quotientRemainder(id_(target b),b);
     if remtau !=0 then error("second map not splittable");
     (sigma,remsigma) := quotientRemainder(id_(source b) - (tau*b),a);
     if remsigma !=0 then error("first map not splittable");
     (sigma,tau)
     )

{*
restart
load "completeIntersection.m2"
kk= ZZ/101
S = kk[x,y,z]
b0 = id_(S^{1,1,0,0})|random(S^4, S^{3:-1})
b = random(target b0, target b0) * b0 * random(source b0, source b0)
a = map(source b, ,syz b)
(s,t) = splittings(a,b)
oo/isHomogeneous
assert(b*t == id_(target b))
assert(s*a ==id_(source a))
*}

decomposeResolution=(f,G,i) ->(
     {*
     Assumes that the operator t corresponding to f is
     surjective in two successive places:
     t_i: G_i --> G_(i-2) and
     t_(i-1): G_(i-1) --> G_(i-3).
     Returns the differntial as the 4 blocks of
     ker t_i ++ G_(i-2) --> ker t_(i-1) ++ G_(i-3)
     *}
     if not (isSurj(f,G,i) and isSurj(f,G, i-1)) then 
	  error("operators not surjective");
     d := G.dd_i;
     d':= G.dd_(i-2);
     t := makeT(f,G,i);
     t' := makeT(f,G,i-1);
     s := map(source t, , syz t);
     s':= map(source t', , syz t');
     (sigma, tau) = splittings(s,t);
     (sigma', tau') = splittings(s',t');
     d00 := sigma'*d*s;
     d10 := map(target t', source s, d'*t*s); -- silly way to write 0
     d01 := sigma'*d*tau;
     d11 = d';
     {d00,d01,d10,d11}
     )

newDifferential = method()
newDifferential(RingElement, ChainComplex, ZZ) := (f, G,i) -> (
     --make the new differential at the i-th step
     L := decomposeResolution(f,G,i);
     (L_0|L_1)||(L_2|L_3)
     )

--the following is unfinished
newComplex = method()
newComplex(RingElement, ChainComplex, ZZ) := (f,G,i) -> (
     --builds the new complex inductively starting from the
     --i th differential.
     len = length G;
     H := new ChainComplex from G;
     H.dd_i = newDifferential(f,G,i);
     H.dd_(i+1) = newDifferential(f,G,i+1);
)     




Lmaps = method()
Lmaps(Matrix, ChainComplex, ZZ) := (F,G,i) -> (
{*   G : Resolution over a complete intersection R = S/(ideal F).
     i : integer such that the map t2: G_i -> G_(i-2)corresponding to F_2 is split surjective
     and the map t1: ker t2 -> G_(i-2) is split injective.
     Computes the maps Ltop, Lbot in the decomposition
     t1^*: G_(i-2)^* -> G_i^*
     t1=
     1   0
     0   Ltop
     0   Lbot
*}
     (t1,t2) := toSequence makeT(F,G,i);
     if coker t2 != 0 then error("t2 not surjective");
     T1 := transpose t1;
     T2 := transpose t2;
     if coker(T1|T2) != 0 then error("G^* not generated in deg i-2");
     cokT2 := coker T2;
     piT2:=map(cokT2, target T2, id_(cokT2)); -- projection to the coker of T2 from the target of T2 (G_i^*)
     V := ker (piT2*T1);
     inV := compress map(source T1, V, gens V);

     (q,remq) := quotientRemainder(id_(target piT2),piT2*T1);
     if remq !=0 then error("p*T2 not splittable");
     --q is the splitting of piT2*T1
     U := image q;
     inU := compress map(source T2, U, gens U);
  
     cokT2U := coker (T2*inU);
     piT2U := map(cokT2U, target T2, id_(cokT2U));-- projection to the coker of T2*inU from the target of T2 (G_i^*)
     cokT2V := coker (T2*inV);
     piT2V := map(cokT2V, target T2, id_(cokT2V));-- projection to the coker of T2*inV from the target of T2 (G_i^*)
--     (L,rem) := quotientRemainder(T1*inV,T2);
--     print L;
     Lbot := (piT2U*T1*inV)//(piT2U*T2*inV);
     Ltop := (piT2V*T1*inV)//(piT2V*T2*inU);
--     print inV;
--     print inU;
--     print cokT2V;
--     print cokT2U;
--     print cokT2;
     (Ltop, Lbot)
     )     
     

///
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y,z]
F = map(S^1, S^2, matrix"x2, z3")
f1 = x^2*y+z^3
R = S/ideal F
M = R^1/ideal gens R
G1 = res(M,LengthLimit => 5)
N = coker transpose G1.dd_5
G = res(N,LengthLimit => 15)
regularity ExtModule N

L=Lmaps(F,G,10)
degrees L_1
degrees L_0


--example where Lbottom cannot be made nilpotent. Also, curious semi-periodicity of the decomposition.
restart
load "completeIntersection.m2"

kk= ZZ/13
--kk = QQ
S = kk[x,y]
f = x^3
ff =matrix"x3,y3"
frandom = ff*(random(source ff, source ff))
g=ff*(random(source ff, S^{-3}))
R = S/(ideal frandom)
M = R^1/x ++R^1/y++R^1/ideal(x,y)
G = res(M, LengthLimit=>30)
makeT(g_0_0,G,6)
isHomogeneous oo
sub(G.dd_5, S)*sub(G.dd_6,S)
char kk
regularity evenExtModule M
g1=(entries g)_0_0
L = decomposeResolution(g1, G, 5)
L/isHomogeneous

D = newDifferential(g1,G,5)
isHomogeneous D
D1 = newDifferential(g1,G,6)
D*D1


netList for i from 2 to 15 list (decomposeResolution(g_0_0,G,2*i))_1
Lmaps(frandom,G,5)
analyzeModule evenExtModule M
DD = for i from 7 to 10 list newDifferential(g_0_0,G,i)
for i from 1 to #DD-1 list (DD_(i-1))*DD_i


use S
Rt = S/ideal(y^3)
Dt = sub(G.dd_5,Rt)
isHomogeneous Dt
Lt = sub(L_0,Rt)
isHomogeneous Lt
betti (F = res (coker Lt, LengthLimit => 10))
betti (F = res (coker Dt, LengthLimit => 10))
F.dd
isHomogeneous Dt


------------------
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y]
F = map(S^1, S^2, matrix"x5, y5")
F = random(S^1, S^{2:-5})
--F = map(S^1, S^2, matrix"x4, y4")
R = S/ideal F
--M = coker random(R^2, R^{3:-4})
--M = coker random(R^2, R^{3:-3})
M = coker random(R^2, R^{3:-2})

reg = regularity ExtModule M
G = res(M,LengthLimit => reg+10)
L=Lmaps(F,G,reg+3)
degrees L_1
for m from 1 to 20 list rank((L_1)^m)
///

analyzeModule = method()
analyzeModule(Module):= E->(
     {*
     Given a module over S = k[x,y], 
     find the decomposition of a high (regularity+1) truncation
     into powers of the maximal ideal and modules of the form
      k[x,y]/f^d where f is an irreducible polynomial.
     The output is of the form 
     {FreeDegs, TorsionComponents}, 
     where
     FreeDegs 
     is a list of the powers of the maximal ideal that are present and
     TorsionComponents 
     is a list of the diagonal entries of 
     a presentation matrix for the torsion part (before truncation);
     Thus 
     {{1,0}, {x^3, x^3, (x-y)^2}) 
     represents the trucation of 
     S(1)++S ++ S/(x^3) ++ S/(x^3) ++ S/(x-y)^2.
     *}
     R := ring E;
     if class R =!= PolynomialRing or numgens R != 2 --or class(coefficientRing R)=!= Field 
     then error("ring of E is not a polynomial ring in 2 vars");
     if E == 0 then return({{},{}});
     F := prune truncate(1+regularity E, E);
     g' := syz transpose presentation F;
     g := map(dual source g', F, transpose g');
     freedegs := degrees target g;
     torsionF := prune ker g;
     f := presentation torsionF;
     r := rank target f;
     fits := apply(r+1, i-> minors(i,f));
     elems := apply(r, j-> fits_(j+1):fits_j); -- elementary divisors
     T = flatten apply(r, j-> if codim elems_j >1 then null else 
	  apply(primaryDecomposition elems_j, I -> factor(gens I)_(0,0)));
     count := #positions(T, t-> t=!=null);
     {freedegs, take(T, -count)}
 )

///
restart
load "completeIntersection.m2"
kk= ZZ/101
S = kk[x,y]
E = directSum(S^1/x^2, S^1/x^2, S^1/y, S^1/(x-y)^3)
R = S/ideal(x^2,x^2*y+y^3)
M = coker((vars R) ++ matrix{{x}} ++ matrix{{y}})
E' = evenExtModule M
E''= oddExtModule M
assert(analyzeModule E == {{}, {(x)^2, (x)^2, (x-y)^3, (y)}})
assert(analyzeModule E' ==  {{{1}, {0}}, {(X_0), (X_1)}})
assert(analyzeModule E'' == {{{0}, {0}}, {(X_0), (X_1)}})
///


needsPackage "ChainComplexExtras"
--take a resolution of a module M annihilated by a reg seq f
--and make the system of higher homotopies

makeHomotopies = method() 


makeHomotopies(ChainComplex, List,ZZ) := (E,f,b) -> (
--inputs:
--E a finite resolution (of a module M)
--(so min E = 0).
--f = {f_1..f_c} a list of elmements of ring E, all of which
--annihilate M.
--output is a hash table whose keys are 
--lists {i,L} where i is an integer and
--L is a sequence of non-neg integers
--of length c adding up to some b' such that i<=b-(2*b'-1), 
--with associated value the
--homotopy of that type, E_i \to E_(i+2*b'-1).

--These satisfy the conditions that 
--for L = 0, the map 
--          s_L is the differential of E;
--for |L| = 1, say a 1 in the i-th place, the map s_L satisfies
--          s_L*s_0 +s_0s_L = f_i
--for each L of degree >1
--          sum_(L=L'+L'') (s_L')*(s_L'') = 0.
--Note: when E is finite, b = max E is the natural value.
     S := ring E;
     c := #f;
     H := new MutableHashTable;
     scan(c, i-> H#{-1, unitIndex i} = map(E_0, S^0,0));
     --in degree 0 we have the differential of E
     scan(b+1, i ->H#(i,{0})=E.dd_i);
     --make the ChainComplexMaps that are multiplication by the f_i
     ff := apply(f, x -> 
	  chainComplexMap(E,E,apply(toList(min E..b), 
		                i->x*id_(E_i))));
     --in degree 1 we have the homotopies for multiplication by the f_i
     scan(c, i->(
     for j from 0 to b-1 do (
	  H#{j,unitIndex i} = 
	      (ff_i_j - H#{j-1, unitIndex i}*E.dd_j)//E.dd_(j+1))));
     --get a list of the indices of the higher homotopies to be constructed
     IL := drop(indexList(c,b), 2); -- this is the list of lists, by degree, of exponents of monomials in c vars.
     --inductive construction of the higher homotopies s_L such 
     scan(IL, Ld -> (
	       d := sum Ld_0;
     	       scan(b-(2*d-1)+1, j->
		    scan(Ld, L -> H#{j,L} =-(sum(properDivisors L, D -> (H#{j+2*sum D -1, L-D})*(H#{j,D})))//E.dd_(j+2*d-1))
		                             )
		    )
	 );
     H)

nonzeroHomotopies = h -> select(pairs h, p -> p_1 !=0)

makeHomotopies(ChainComplex, List) := (E,f) -> (
     b := max E;
     if b == infinity then error "resolution is infinite; give bound";
     makeHomotopies(E,f,b))

makeHomotopies(ChainComplex, Matrix) := (E,f) -> (
     f1 := flatten entries f;
     makeHomotopies(E,f1)
     )
     
commutator = (H,i,j) -> (
     --note: the elements should anti-commute; the commutator has a +.
     ei := unitIndex i;
     ej := unitIndex j;
     m := 0;
     ans := {};
     while H#?{m+1,ei} do (
	  comm := (H#{m+1,ei})*(H#{m,ej}) + (H#{m+1,ej})*(H#{m,ei});
	  ans = append(ans, comm);
	  m = m+1);
     ans)
     
unitIndex = i -> flatten exponents S_i;

--make a list of lists L_0..L_b, where each L_i contains the exponent vectors of the monomials of degree i.
indexList = (c,b) ->(
     x := local x;
     R := ZZ/2[x_0..x_(c-1)];
     B := {};
     apply(b+1, d -> (
	       B = basis (d, R^1/(ideal vars R)^(b+1));
	       flatten ((flatten entries B)/exponents)))
     )

properDivisors = method()
properDivisors RingElement := m ->(
     I := ideal fromDual matrix{{m}};

     L:=flatten entries basis ((ring m)^1/I);
     L1 := select(L, i->i!= 1 and i!=m);
     flatten (L1/exponents)
     )
properDivisors List := L -> (
     x := local x;
     R := ZZ/2[x_0..x_(#L-1)];
     m := product(#L, i -> (R_i)^(L_i));
     properDivisors m)

///
restart
load "completeIntersection.m2"
S = ZZ/101[a,b,c]
E = res coker vars S
f = {a,b,c}
h1 = makeHomotopies(E,{a,b,c},max E)
h = makeHomotopies(E,{a,b,c})
commutator(h,0,1)

pairs h

IL = indexList(3,2)
properDivisors (a^3*b^2)
properDivisors {3,2,1}

///
end
viewHelp HashTable
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y,z]
F = map(S^1, S^2, matrix"x2, z3")
f1 = x^2*y+z^3
R = S/ideal F
M = R^1/ideal gens R
G1 = res(M,LengthLimit => 5)
N = coker transpose G1.dd_5

G = res(N,LengthLimit => 15)
E = ExtModule N;
Ee = evenExtModule N;
Eo = oddExtModule N;
analyzeModule Ee
analyzeModule Eo
describe ring E
describe ring Ee

regularity (E, Weights => {1,1})
regularity E
regularity Ee
regularity Eo


makeT(F,G,4)
makeT(f1,G,4)
netList for i from 0 to 13 list {i, isSurj(f1,G,i)}


restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y]
R = S/ideal(x^2,x^2*y+y^3)
M = coker((vars R) ++ matrix{{x}} ++ matrix{{y}})
G = res(M, LengthLimit=>10)
ExtModule M


------
--What is the relation between even and odd ExtModules
--in codim 2?
installPackage "Style"
viewHelp RandomIdeal

restart
load "completeIntersection.m2"
loadPackage "RandomIdeal"

kk= ZZ/101
S = kk[x,y,z]
R = S/ideal(x^5,y^5)

B3 = gens ((ideal vars R)^3)
g1 = gens randomSparseIdeal(B3,1,5)
g2 = gens randomSparseIdeal(B3,2,5)
m = g1||g2
M= coker m
E0 = evenExtModule(M)
E1 = oddExtModule M
analyzeModule E0
analyzeModule E1

--
kk = ZZ/101
R = kk[x,y,z]/ideal"x5,y5"
matrix {{x*y*z, x^2*z, y^3, x*y^2, x^3}, {y*z^2, y^2*z, x*y^2, x^2*y, x^3}}
M= coker m
E0 = evenExtModule(M)
E1 = oddExtModule M
analyzeModule E0
analyzeModule E1

--
m=random(R^2, R^{4:-2})
M= coker m
E0 = evenExtModule(M)
E1 = oddExtModule M
analyzeModule E0
analyzeModule E1
toString presentation ring M
toString presentation M



--
load "completeIntersection.m2"
loadPackage "RandomIdeal"

kk= ZZ/101
S = kk[x,y]
R = S/ideal(x^5,y^4)
M = R^1/ideal"x3,x2y,y3"
analyzeModule evenExtModule M
analyzeModule oddExtModule M


---------------------------------------------------------
--An example where E0 has a torsion part but E1 does not.
--Also an example where "Lbottom" is not nilpotent. 
restart
load "completeIntersection.m2"
loadPackage "RandomIdeal"

kk= ZZ/101
S = kk[x,y]
F = matrix"x3,y3"
Frandom = matrix"x3,y3" * random(S^2, S^2)
Frandom = matrix"x3+y3,y3"
R = S/ideal(x^3,y^3)
M = R^1/ideal(x^2,x*y)
--M = R^1/ideal((x-y)^2,(x-y)*y)
reg = regularity ExtModule M
analyzeModule evenExtModule M
analyzeModule oddExtModule M
G = res(M, LengthLimit => 10)
L=Lmaps(Frandom,G,6)
G.dd
L_0*L_1
makeT(F,G,5)
L_1^17

dim M
F=res(M, LengthLimit=>5)
G = res (coker transpose F.dd_1, LengthLimit=>10)
analyzeModule evenExtModule M
analyzeModule oddExtModule M
G.dd
L = Lmaps(Frandom,G,7)
makeT(Frandom,G,7)
N = coker transpose G.dd_2
analyzeModule evenExtModule N
analyzeModule oddExtModule N
R^1/(ideal(x,y))
CIgens =toList flatten entries F
ExtL(CIgens, R^1/(ideal(x,y)),M)

methods Ext
code (Ext, Module, Module)


----
restart
load "completeIntersection.m2"
loadPackage "RandomIdeal"

kk= ZZ/7
S = kk[x,y]
M = truncate(3,S^1/ideal(x^2-2*y^2))
use S
M1 = M/x^3
F = matrix"x3,y3"
R = S/ideal F
N = prune coker sub(presentation M1,R)
evenExtModule N
analyzeModule evenExtModule N
FF = res(N, LengthLimit=>10)
FF.dd
sub(FF.dd_8,S)*(sub(FF.dd_9, S))


restart
load "completeIntersection.m2"
loadPackage "RandomIdeal"

kk= ZZ/101
S = kk[x,y]
use S
M = truncate(1,S^1/ideal"x2")
M= coker 
M1 = M/y^4
F = matrix"x4,y4"
R = S/ideal F
N = prune coker sub(presentation M1,R)
evenExtModule N
analyzeModule evenExtModule N

FF = res(N, LengthLimit=>10)
FF.dd
sub(FF.dd_8,S)*(sub(FF.dd_9, S))

newDifferential(y^3, G, 2)

------
--Look for examples where the free rank of evenExt or oddExt is
--just 1. First for monomial ideals, then for binomial ideals.
restart

load "completeIntersection.m2"
loadPackage "RandomIdeal"
--viewHelp RandomIdeal
kk= ZZ/101
S= kk[x,y]
--R = S/ideal"x5-y5,x4y+x3y2+x2y3+xy4"
R = S/ideal"x10,y10"
mR = ideal"x,y"
G = gens (mR^3)
B = flatten entries(G*map(source G,,basis (mR^3)))
time tally for i from 1 to 10000 list(
     N = 3+random 14;
    I = ideal((random B)_{0..N});
    M = R^1/I;
    E0 = evenExtModule M;
    E1 = oddExtModule M;
    e0 = #first analyzeModule E0;
    e1 = #first analyzeModule E1;    
    if e0==1 or e1==1 then print I;
    (e0,e1))        
{*
o10 = Tally{(0, 0) => 285 }
            (2, 2) => 3302
            (3, 3) => 4369
            (4, 4) => 1742
            (5, 5) => 276
            (6, 6) => 25
            (7, 7) => 1

Tally{      (2, 2) => 146}
            (3, 3) => 523
            (4, 4) => 329
            (5, 5) => 2
*}
--viewHelp randomBinomialIdeal


time tally for i from 1 to 10000 list(
    N = 1+random 15;
    L = for i from 0 to N-1 list 2+random(15);
    I = randomBinomialIdeal(L,R);
    M = R^1/I;
    E0 = evenExtModule M;
    E1 = oddExtModule M;
    e0 = #first analyzeModule E0;
    e1 = #first analyzeModule E1;    
    if e0==1 or e1==1 then print I;
    (e0,e1))        

{*o9 = Tally{(0, 0) => 121 }
           (2, 2) => 6048
           (3, 3) => 3572
           (4, 4) => 251
           (5, 5) => 8
*}




------
--Look for a relation between the dim of Ext 
--and the rank (degree) of Ext
restart
load "completeIntersection.m2"
loadPackage "RandomIdeal"
kk= ZZ/101
S= kk[vars(0..3)]
R = S/(ideal vars S)^[5]
mR = ideal vars R
G = gens (mR^2)
B = flatten entries(G*map(source G,,basis (mR^2)))
time tally for i from 1 to 1000 list(
     N = 2+random 10;
    I = ideal((random B)_{0..N});
    M = R^1/I;
    E0 = evenExtModule M;
    dim0 = dim E0;
    deg0 = degree E0;
    if deg0 < dim0 then print I;
    {dim0,deg0})


time tally for i from 1 to 10000 list(
    N = 1+random 15;
    L = for i from 0 to N-1 list 2+random(15);
    I = randomBinomialIdeal(L,R);
    M = R^1/I;
    E0 = evenExtModule M;
    dim0 = dim E0;
    deg0 = degree E0;
    if deg0 < dim0 then print I;
    {dim0,deg0})



-----------
--example to show that the resolution is "standard"
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y]
f = x^3
ff =matrix"x3,y3"
--frandom = ff*(random(source ff, source ff))
frandom = matrix {{48*x^3+28*y^3, -42*x^3-45*y^3}}

--g=ff*(random(source ff, S^{-3}))
--toString g
g = matrix {{-50*x^3-21*y^3}}

R = S/(ideal frandom)
M = R^1/x ++R^1/y++R^1/ideal(x,y)
G = res(M, LengthLimit=>10)
regularity evenExtModule M
regularity oddExtModule M

g1=(entries g)_0_0
makeT(g1
L = decomposeResolution(g1, G, 5)
oo/isHomogeneous
D = (L_0|L_1)||(L_2|L_3)
isHomogeneous D

use S
Rt = S/ideal(y^3)
Dt = sub(D,Rt)
dt = sub(G.dd_5, Rt)
netList degrees Dt 
netList degrees dt
isHomogeneous Dt
Lt = sub(L_0,Rt)
isHomogeneous Lt

betti (H = res (coker Dt, LengthLimit => 10))
betti (H = res (coker dt, LengthLimit => 10))
betti (K = res (coker Lt, LengthLimit => 10))

--codim 3
restart
load "completeIntersection.m2"

kk= ZZ/13
S = kk[x,y,z]
ff =matrix"x3,y3,z3"
frandom = ff*(random(source ff, source ff))
g=ff*(random(source ff, S^{-3}))
R = S/(ideal frandom)
M = R^1/x ++R^1/y++R^1/ideal(x,y)++coker random(R^{-1,-1},R^{-2,-2,-2,-2})
G = res(M, LengthLimit=>10)
--makeT(g_0_0,G,6)
--sub(G.dd_5, S)*sub(G.dd_6,S)
regularity evenExtModule M
regularity oddExtModule M
g
g1=(entries g)_0_0
L= decomposeResolution(g1, G, 3)

Lh1 = map(R^{0,-1,0,0,0,0,0,0,0,0}, R^{2:-1,2:-2,4:-1}, L_1)
isHomogeneous Lh1
Lh3 = map(R^{0,0,-1,0,0}, R^{2:-1,2:-2,4:-1}, L_3)
isHomogeneous Lh3
Lh0 =  map(R^{0,-1,0,0,0,0,0,0,0,0}, R^{-2,-2,10:-1}, L_0)
isHomogeneous Lh0
Lh2 = map(R^{0,0,-1,0,0},  R^{-2,-2,10:-1}, L_2)
isHomogeneous Lh2
D = (Lh0 | Lh1)||(Lh2|Lh3)

isHomogeneous D

use S
Rt = S/ideal(x^3,y^3)
Lt0 = sub(L_0, Rt)
d = sub(G.dd_5, Rt)
betti res (H=coker Lt0, LengthLimit => 10)
betti res (GG = coker d, LengthLimit => 10)

G.dd_2

------
--truncated res of residue fld
restart
load "completeIntersection.m2"

kk= ZZ/13
S = kk[x,y]
f = x^3
ff =matrix"x3,y3"
R = S/(ideal ff)
M = coker syz vars R
G = res(M, LengthLimit=>10)
L = decomposeResolution(f, G, 3)
oo/isHomogeneous
G.dd_3

use S
Rt = S/ideal(y^3)
D = sub(G.dd_3, Rt)
d = sub(L_0, Rt)
betti (F = res (coker D, LengthLimit => 10))
betti (G = res (coker d, LengthLimit => 10))

-----
--truncated res of residue fld
restart
load "completeIntersection.m2"

kk= ZZ/13
S = kk[x,y,z]
f = x^3
ff =matrix"x3,y3,z3"
R = S/(ideal ff)
M = module (ideal vars R)^2
G = res(M, LengthLimit=>10)
L = decomposeResolution(f, G, 3)
L/isHomogeneous
degrees G.dd_3

use S
Rt = S/ideal(y^3,z^3)
D = sub(G.dd_3, Rt)
d = sub(L_0, Rt)
betti (F = res (coker D, LengthLimit => 10))
betti (G = res (coker d, LengthLimit => 10))


---------
--codim 3; apparently "bad" example.
--here the 
restart
load "completeIntersection.m2"

kk= ZZ/13
S = kk[x,y,z]
ff =matrix"x3,y3,z3"
frandom = ff*(random(source ff, source ff))
g=ff*(random(source ff, S^{-3}))
R = S/(ideal frandom)
describe R
dim R
--M1 = R^1/x ++R^1/y++R^1/ideal(x,y)
M2 = coker random(R^2,R^{4:-1})
--M = M1 ++ M2
G2 = res(M2, LengthLimit=>10)
regularity evenExtModule M2
regularity oddExtModule M2
g1=(entries g)_0_0
L= decomposeResolution(g1, G2, 3)


use S
Rt = S/ideal(x^3,y^3)
Lt0 = sub(L_0, Rt)
d = sub(G2.dd_3, Rt)
betti res (H=coker Lt0, LengthLimit => 10)
ƒbetti res (GG = coker d, LengthLimit => 10)





----------
---- A bad case in 2 vars:
restart
load "completeIntersection.m2"

kk= ZZ/101
S = kk[x,y]
f = x^3
ff =matrix"x3,y3"
--frandom = ff*(random(source ff, source ff))
frandom = matrix {{48*x^3+28*y^3, -42*x^3-45*y^3}}

--g=ff*(random(source ff, S^{-3}))
--toString g
g = matrix {{-50*x^3-21*y^3}}

R = S/(ideal frandom)
M1 = R^1/x 
M2 = R^1/y
M3 = R^1/ideal(x,y)
M= M1++M2
M = M3
M = M1++M2++M3
M = coker random(R^2, R^{2:-4})
G = res(M, LengthLimit=>10)
--regularity evenExtModule M
--regularity oddExtModule M

g1=(entries g)_0_0
--check that t2 and t3 are surjective:
prune coker makeT(g1, G, 2)
prune coker makeT(g1, G, 3) 


L = decomposeResolution(g1, G, 3)
D = (L_0|L_1)||(L_2|L_3)

use S
Rt = S/ideal(y^3)
dt = sub(G.dd_3, Rt)
Lt = sub(L_0,Rt)
betti (H = res (coker dt, LengthLimit => 10))
betti (K = res (coker Lt, LengthLimit => 10))



-------------
--Compare the number of relations of a high syzygy over a complete
--intersection and over a complete int of codim one less.
restart
load "completeIntersection.m2"
kk = ZZ/101
n= 2
S = kk[a_0..a_n]
f = ideal (vars S)^[4]
ff = ideal ((vars S)^[4]*random(S^{3:-4}, S^{2:-4}))
R' = S/ff
R = S/f
red = map (R, R')
M = coker random(R^{0,1,2,3}, R^{-2,-4,-4,-4})
ll=5
F= res(M, LengthLimit=> ll)

F1 = res (coker vars R, LengthLimit=> 4)
F =res(coker transpose (F1.dd_4), LengthLimit => 10)

for i from 1 to 10 do(
     print i;
     print betti F.dd_i;
     M' = pushForward(red, coker F.dd_i);
     print betti prune M';
     )


--Redo of the "apparently bad example"

---------
--codim 3; apparently "bad" example, redone
restart
load "completeIntersection.m2"

kk= ZZ/13
S = kk[x,y,z]
ff =matrix"x3,y3,z3"
R = S/(ideal ff)
M = coker random(R^2,R^{4:-1})
F = res(M, LengthLimit=>10)
betti F
betti F.dd_5
regularity evenExtModule M
regularity oddExtModule M

f = generalize ff
T'5 = makeT'(f,F,5)
t'5 = T'5_2
T'6 = makeT'(f,F,6)
t'6 = T'6_2
betti t'6
prune coker t'6
Rt = ring t'6

betti res prune pushForward(map(R,Rt),  coker F.dd_5)



restart
loadPackage "ExtDecomp"

restart
load "completeIntersection.m2"
S = ZZ/101[a,b,c]

E = res coker vars S
f = matrix"a2,b2,c2"
h=makeHomotopies(E,f)
nonzeroHomotopies h
commutator(h,0,1)

E = res minors(2, matrix"a,b,0;0,a,b")
f = matrix"a2,b2,c2"
h=makeHomotopies(E,f)
nonzeroHomotopies h
commutator(h,0,1)



---------------------------------------------------------
--An example where E0 has a torsion part but E1 does not.
--Also an example where "Lbottom" is not nilpotent. 
restart
load "completeIntersection.m2"


kk= ZZ/101
S = kk[x,y]
F = matrix"x3,y3"
Frandom = matrix"x3,y3" * random(S^2, S^2)
--Frandom = matrix"x3+y3,y3"
R = S/ideal(x^3,y^3)
M = R^1/ideal(x^2,x*y)
--M = R^1/ideal((x-y)^2,(x-y)*y)
reg = regularity ExtModule M
analyzeModule evenExtModule M
analyzeModule oddExtModule M
G = res(M, LengthLimit => 10)
L=Lmaps(Frandom,G,6)
G.dd
L_0*L_1
makeT(F,G,5)
L_1^17

dim M
F=res(M, LengthLimit=>5)
G = res (coker transpose F.dd_1, LengthLimit=>10)
analyzeModule evenExtModule M
analyzeModule oddExtModule M
G.dd
L = Lmaps(Frandom,G,7)
makeT(Frandom,G,7)
N = coker transpose G.dd_2
analyzeModule evenExtModule N
analyzeModule oddExtModule N
R^1/(ideal(x,y))
CIgens =toList flatten entries F
ExtL(CIgens, R^1/(ideal(x,y)),M)

methods Ext
code (Ext, Module, Module)

---
restart
load "completeIntersection.m2"

S = ZZ/101[x,y,z]
m = random(S^2, S^{2:-1,3:-2})
betti (G=res(coker m, LengthLimit => 7))
f = (vars S)^[3]*random(S^3, S^3)
f = (vars S)^[4]*random(S^3, S^3)
R = S/ideal f
M = R**coker m
betti (G=res(M, LengthLimit => 7))
regularity ExtModule M
isHomogeneous M

makeT(f,G,5)
