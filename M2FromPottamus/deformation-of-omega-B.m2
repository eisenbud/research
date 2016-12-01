--Implements the obstruction for the flatness of the deformation of Omega
--corresponding to a flat deformation.

testDefOfDifferentials = (g,h) ->(
--here g is a row matrix over a ring S whose entries generate some ideal I,
--and h is a deformation of I, that is (g_i+ \eps h_i) is a flat
--first order deformation of I. Such an h is obtained as a
--homomorphism I --> S^1/I. The result is a map in Hom(S^m, \Omega_R),
-- where m is the number of syzygies of (dg mod g).
--The resulting map is zero zero iff
--the induced deformation of the module of differentials is also flat,
--
--Our eventual goal is to see which linear combinations of a basis
--for the allowable (flat) choices for h give zero in this way; they
--are the Omega-flat deformations.
S := ring g;
I := ideal g;
R := S/I;
Jg := diff(transpose vars S, g);
dg := Jg**R;
Jh := diff(transpose vars S, matrix h);
dh := R**Jh;

psi := syz dg;
psiS := lift(psi,S);
psiTilde := (Jg*psiS)//(g**(target Jg));
alpha := ((matrix h)**(target Jg))*psiTilde;

p := inducedMap((coker Jg)/I, target Jg);
--here's the map that should be zero if we have a good defo:
(p*(Jh*psiS-alpha))-- ;error()
)

representMatrix = (f,M) ->(
     --here f is some procedure that takes elements of
     --a module M -- or more properly, maps from a 
     --rank 1 free module to M -- and returns elements
     --of a module N -- again, actually maps of a rank 1 free module to N.
     --Here both M and N must be modules over a kk-algebra R that are
     --finite dimensional over kk, and 
     --the procedure should be kk-linear. This script
     -- returns a matrix representing f as a kk-linear mapping
     --of vector spaces. The ring in question must not be a tower ring.
     BM := basis M;
     mat := representVector (f BM_{0});
     for i from 1 to rank source BM -1 do(
	mat = mat | (f BM_{i}));
     mat)  

pushToField=method()
pushToField(Module, ZZ) := (M,d) ->(
     --assumes ring M is an algebra over a field kk;
     --and M is a fin dim vspc over k;
     --pushes forward to kk
     kk:=ultimate(coefficientRing, R);
     (RM,f):=flattenRing ring M;
     T =kk[vars(0..numgens RM)]; -- ring with one more variable.
     RtoT=map(T,R,(vars T)_{1..numgens RM});
     A=RtoT presentation M;
     MT = coker homogenize(map(T^(rank target A), T^{rank source A:-d},A),T_0);
     basis(d,MT)
     )

{* homogenization of a map (matrix?) should have two forms: either give
a source and target, with degrees, try to homogenize, complain if not possible;
or set the source degrees (as efficiently as possible) to make the map
homogeneous. The latter is possible using map(free module, , matrix).
the first is implemented above.

  --Maybe the homogenization doc should mention this possibility!
*}

homogenizeToDegree=method()
homogenizeToDegree(ZZ,RingElement,RingElement) := (d,r,z) -> (
     --this codes assumes there's a single grading and z has deg 1.
     r1:=homogenize(r,z);
     dr1:= first degree r1;
     if d<dr1 then error("given degree was too small");
     r1*z^(d-dr1)
     )

homogenizeToDegree(Matrix,RingElement) := (phi,z) -> (
     --this codes assumes there's a single grading and z has deg 1.
     src:=flatten degrees source phi;
     tar:=flatten degrees target phi;
     map(target phi, source phi, (i,j) -> homogenizeToDegree(src_j - tar_i, phi_(i,j), z))
     )

pushToField(ModuleMap) := (phi) ->(
     --assumes phi:M -> N is a map of modules that are finite dim vspc's over a field kk
    --assumes ring M is an algebra over a field kk;
     --and M is a fin dim vspc over k;
     --pushes forward to kk
     kk := ultimate(coefficientRing, R);
     M := source phi;
     N := target phi;
     pM := presentation M;
     pN := presentation N;
     (RM,f) := flattenRing ring M;
     T := kk[vars(0..numgens RM)]; -- ring with one more variable.
     RtoT := map(T,R,(vars T)_{1..numgens RM});
     
     phiTemp := map(T^(numgens N),,homogenize(RtoT matrix phi, T_0));
     d := first max degrees source phiTemp;
     
     pMT := map(T^{numgens M:-d},,homogenize(RtoT pM, T_0));
     pNT := map(T^(numgens N),,homogenize(RtoT pN, T_0));

     MT := coker pMT;
     MT = MT/saturate(0_T*MT, T_0);
     eM := regularity MT;

     NT := coker pNT;
     NT = NT/saturate(0_T*NT, T_0);
     eN := regularity NT;
 
     phiT := homogenizeToDegree(map(target pNT, target pMT, RtoT matrix phi), T_0);

     e := max(eM,eN);     
     BM := basis(e,MT);
     BN := basis(e, NT);

     lift((map(target BN, target BM,(matrix phiT))*BM)//BN,kk) --; error()
     )

representVector = method()
{*
representVector(Matrix) := (phi) ->(
     --assumes phi:R^1->N  where
     --R is an algebra over a field kk. Writes phi(1) in terms
     --of a vector space basis of N.
     --Assumes N is a fin dim vspc over k;
     R := ring phi;
     kk := ultimate(coefficientRing, R);
     M := source phi;
     N := target phi;
     pN := presentation N;
     (RM,f) := flattenRing ring M;
     T := kk[vars(0..numgens RM)]; -- ring with one more variable.
     RtoT := map(T,R,(vars T)_{1..numgens RM});
     
     phiTemp := map(T^(numgens N),,homogenize(RtoT matrix phi, T_0));
     d := first max degrees source phiTemp;
     
     pNT := map(T^(numgens N),,homogenize(RtoT pN, T_0));
     NT := coker pNT;
     NT = NT/saturate(0_T*NT, T_0);
     eN := regularity NT;

     MT := T^{-d};
     eM := d;
     
      
     phiT := homogenizeToDegree(map(target pNT, MT, RtoT matrix phi), T_0);
     e := max(eM,eN);     

     BM := map(MT,T^{-e},{{(T_0)^(e-d)}});
     BN := basis(e, NT);

     vS :=  (map(target BN, target BM,(matrix phiT))*BM)//BN;
     lift(vS,kk) --; error()
     )
*}

--the code for representVector above seems crazy! First, it's going to be
--applied many times, so we ought to compute the basis of N just once.
--second, I don't see why the following isn't enough:

representVector(Matrix,Matrix) := (phi,B) ->phi//B
          --assumes phi:R^1->N  where
	  --R is an algebra over a field kk. Writes phi(1) in terms
	  --of a vector space basis B of N.
	  --Assumes N is a fin dim vspc over k

representVector(Matrix) := (phi) ->(
          --assumes phi:R^1->N  where
	  --R is an algebra over a field kk. Writes phi(1) in terms
	  --of a vector space basis B of N.
	  --Assumes N is a fin dim vspc over k
B = basis N;
phi//B)
	  
			 
toHom = phi -> (
     --here phi: M --> N, and we want to put
     --phi into Hom(M,N).
     --if presentation M = GM --> FM
     -- and presentation N = GN --> FN
     --then Hom(M,N) is defined as a subquotient of
     --dual(FM) ** GM = Hom(FM, GM).
     H:=Hom(source phi, target phi);
     rawmap = adjoint(matrix phi, S^1, target presentation source phi);
     map(H, S^1, rawmap//gens H)
     )

trivialDefs = g -> (
     S := ring g;
     I := ideal g;
     R1 := S^1/I;
     Jg := diff(transpose vars S, g);
     H := Hom(I,R1);
     T:= image toHom map(R1, module I, Jg^{0});
     for i from 1 to rank target Jg -1 do
	  T = T+image toHom map(R1,module I,Jg^{i});
     mm=map(Hom(ideal g, S^1/ideal g), source vars S, gens T//gens H);
     tt=map(target mm, coimage mm, mm);
     ttt=tt*(basis coimage mm);
     for i from 0 to rank source ttt -1 list homomorphism ttt_{i}
     )

OmegaFlatDefs = g ->(
     f := (g,h) -> toHom testDefOfDifferentials(g,homomorphism h);
     BH = basis Hom(ideal g, S^1/ideal g);
     mat = representVector (f (g,BH_{0}));
     for i from 1 to rank source BH  -1 do(
     	  mat = mat | representVector (f(g,BH_{i})));
     K=syz mat;
     KH=BH*K;
     for i from 0 to rank source KH -1 list homomorphism KH_{i}
     )

OmegaFlatDefsModule = g ->(
     f := (g,h) -> toHom testDefOfDifferentials(g,homomorphism h);
     BH = basis Hom(ideal g, S^1/ideal g);
     mat = representVector (f (g,BH_{0}));
     for i from 1 to rank source BH  -1 do(
     	  mat = mat | representVector (f(g,BH_{i})));
     K=syz mat;
     KH=BH*K;
     image KH
     )

report = g -> (
     <<"--Defs from infinitesimal autorphisms" << endl;
     print netList (Ltriv=trivialDefs g);
     <<endl;
     <<"--Omega-flat deformations" << endl;
     print netList (LOmega=OmegaFlatDefs g);
     <<endl;
     <<"-- length of fiber: " << degree ((ring g)^1/ideal g) << endl;
     <<"-- dim of trivial deformations:" << #Ltriv << endl;
     <<"-- dim of Omega-flat deformations: " << #LOmega << endl ;
     <<"-- dim of module gen by  Omega-flat deformations: " << degree OmegaFlatDefsModule g;
     )

TB = (L,S) -> (
     --Produces the ideal with Thom-Boardman symbol L
     n:= numgens S;
     I := ideal 0_S;
     for i from 0 to #L-1 do(
	  I = I+(ideal (vars S)_{0..n-L_i-1})^(i+1)
	  );
     I=trim I;
     print I;
     I)

end

restart
load "deformation-of-omega-A.m2"
kk=ZZ/101
S=kk[x,y]

report matrix"x2,xy,y2"
report matrix"x3,xy,y3"     
report matrix"x3,y3"
report random(S^1, S^{2:-3})
report gens (ideal vars S)^4

n=4
S=kk[vars(0..n-1)]
time report random(S^1,S^{n+1:-2})


S=kk[a,b,c]    
L={3,2,2,0}
report gens TB({3,2,2,1,1,0},S)     

n=7
S=kk[vars(0..n-1)]
i=trim ideal((vars S)^[2] | random(S^1,S^{-2}))
--i = ideal"a2,b2,c2,d2,e2,ab+cd+ae+be"
--70*8-57
--None of the following are general enough to give the required 503 deformations
--i = ideal"a2,b2,c2,d2,e2,f2,g2,ab+cd+ef+g(a+b+c+d+e+f)"
--i = ideal"a2,b2,c2,d2,e2,f2,g2,ab+cd+ef+bc+de+g(a+b+c+d+e+f)"
--i = ideal"a2,b2,c2,d2,e2,f2,g2,ab+cd+ef++ga+bc+de+fg"
degree Hom(i,S^1/i)
report gens i
