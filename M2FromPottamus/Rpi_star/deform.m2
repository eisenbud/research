firstOrderDeformation=(L)->(
     --the  presentation matrix of the first order deformation of the module
     -- L with only positive degree entries in the first and second 
     -- syzygy matrices 
     R:=ring L;
--     kk:=coefficientRing R
     fL:=res( L,LengthLimit=>2);
--fL.dd_1
--fL.dd_2
--betti fL
     --da=-degrees Hom(fL_1,fL_0);
     dfL2:=apply(degrees fL_2,d->d#0);
     dfL1:=apply(degrees fL_1,d->d#0);
     dfL0:=apply(degrees fL_0,d->d#0);
     if max(dfL0)>=min(dfL1) or  max(dfL1)>=min(dfL2) then 
     (<<"expect only positive degree entries in the syzygy matrices" <<endl) else ( 
     r0:=rank fL_0;
     r1:=rank fL_1;
     r2:=rank fL_2;
     A:=kk[join toSequence apply(r0,i-> apply(r1,j->a_(i,j))),Degrees=>join toSequence apply(r0,i->toList apply(r1,j->dfL1_j-dfL0_i))]; 
     mA:=map(A^(-degrees fL_0),A^(-degrees fL_1),
	  matrix apply(r0,i->apply(r1,j->a_(i,j))));
     B:=kk[join toSequence apply(r1,i->apply(r2,j->b_(i,j))),Degrees=>join toSequence apply(r1,i->apply(r2,j->dfL2_j-dfL1_i))];
     mB:=map(B^(-degrees fL_1),B^(-degrees fL_2),
	  matrix apply(r1,i->apply(r2,j->b_(i,j))));
     AB:=A**B;
     AR:=AB**R;
  --   isHomogeneous mA;
     L1:=substitute( fL.dd_1,AR);
     L2:=substitute(fL.dd_2,AR);
     --betti L1
     --betti L2
     mA1:=substitute(mA,AR);
     mB1:=substitute(mB,AR);
     betti(eq1:=flatten( mA1*L2+L1*mB1));
--betti transpose  eq1
betti(eqM:=diff(transpose (flatten mA1|flatten mB1),eq1));
     isHomogeneous eqM;
betti(     sol1:=syz(transpose substitute(eqM,R),DegreeLimit=>0));
--betti sol1
--betti eqM
betti(     sol1A:=sol1^{0..(rank source vars A -1)});
     Cindex1:=toList(set(1..r1)**set(1..r1));
     Cindex:=select(toList Cindex1,ij->dfL1_(ij#0-1)<=dfL1_(ij#1-1));
     C:=kk[apply(Cindex,ij->c_ij),Degrees=>apply(Cindex,ij->dfL1_(ij#1-1)-dfL1_(ij#0-1)+1)]; 
     CR:=C**R;use CR;
     mC:=map(CR^(-degrees fL_1),CR^(-degrees fL_1)**CR^{-1},
	  matrix apply(toList(1..r1),i->apply(toList(1..r1),j->if dfL1_(i-1)<=dfL1_(j-1) then c_(i,j) else 0_CR)));
     mC1:=(substitute(fL.dd_1,CR)*mC);
     trivC:= transpose substitute( diff(transpose substitute(vars C,CR),flatten mC1),R);;
betti sol1A;
betti trivC;
     --isHomogeneous trivC
     Eindex1:=toList(set(1..r0)**set(1..r0));
     Eindex:=select(toList Eindex1,ij->dfL0_(ij#0-1)<=dfL0_(ij#1-1));
     E:=kk[apply(Eindex,ij->e_ij),Degrees=>apply(Eindex,ij->dfL0_(ij#1-1)-dfL0_(ij#0-1)+1)]; 
     ER:=E**R;use ER;
     mE:=map(ER^(-degrees fL_0),ER^(-degrees fL_0)**ER^{-1},
	  matrix apply(toList(1..r0),i->apply(toList(1..r0),j->if dfL0_(i-1)<=dfL0_(j-1) then e_(i,j) else 0_ER)));
     mE1:=mE*substitute(fL.dd_1,ER);
     trivE:=transpose substitute(diff(transpose substitute(vars E,ER),flatten mE1),R);
     betti trivE;
     --betti trivC
     betti (triv:= gb( truncate(-1,image (trivC|trivE)**R^{-1}),DegreeLimit=>0));
     --isHomogeneous trivE
betti truncate(0,image sol1A);
betti(     def:=mingens image (gens truncate(0,image sol1A)%triv));
     tt:=(tally degrees source def)_{0};
     T=kk[t_1..t_tt];
     RT=R**T;
     betti(defT:=((substitute(def,RT))_{0..tt-1})*transpose substitute(vars T,RT));
     MA:=diff(transpose vars A,flatten mA);
     --vars A- ((flatten mA)*MA);
     A1:=substitute(mA,transpose defT*substitute(MA,RT));
     LL:=substitute(fL.dd_1,RT)+A1);
     LL)   
--def=(image sol1A)/(image (triv1|triv2))
--prune def
--hilbertFunction(0,def)

secondOrderDeformation=(L1,T)->(
--     Given a first order deformation represented as the cokernel
--     of the matrix L1 over a base ring T
--     some the second order deformation (assumed unobstructed)
--     is computed and L2=(L2#0,L2#1) the two first matrices
--     of the resolution presentation returned 
     RT:=ring L1;
     kk:=coefficientRing T;
--     T2=substitute((ideal vars T)^2,RT)
--     RT2=RT/T2          
     L0:=substitute(substitute(L1,R),RT);
     L10:=map(target L1,source L1**RT^{-1},L1-L0);
--isHomogeneous L10;
     M0:=syz L0;
     F0:=chainComplex(L0);
     F1:=chainComplex(M0**RT^{-1});
--betti F0;
--betti F1;
     EL1:=extend(F0,F1,L10);
--betti EL1_0;
--betti EL1_1;
     da:=-degrees Hom(F1_0**RT^{-1},F0_0);     
     r0:=rank F0_0;
     r1:=rank F0_1;
     r2:=rank F1_1;
     r01:=r0*r1;
     db:=-degrees Hom(F1_1**RT^{-1},F0_1);
     A:=kk[a_(1,1)..a_(r0,r1),Degrees=>da];
     B:=kk[b_(1,1)..b_(r1,r2),Degrees=>db];
     AB:=A**B;
     ART:=AB**RT;
     use A;
     mA:=map(A^(-degrees F0_0),A^(-degrees F1_0)**A^{-1},genericMatrix(A,a_(1,1),r0,r1));
     a2:=substitute(mA,ART);
     autA:=diff(transpose vars A, flatten mA);
--isHomogeneous a2;
     use B;
     mB:=map(B^(-degrees F0_1),B^(-degrees F1_1)**B^{-1},genericMatrix(B,b_(1,1),r1,r2));
     autB:=diff(transpose vars B,flatten mB);
--isHomogeneous mB;
--isHomogeneous mA;
     b2:=substitute(mB,ART);
     a0:=substitute(F0.dd_1,ART);
     a1:=substitute(EL1_0,ART);
     b0:=substitute(F1.dd_1,ART)**ART^{-1};
     b1:=-substitute(EL1_1,ART)**ART^{-1};    
--     rel=(a0+a1)*(b0+b1);
--betti a0;
--betti a1;
--betti a2;
--betti b0;
--betti b1;
--betti b2;
--betti(a0*b2);
--betti(a2*b0);
--betti(a2*b0);
--     flatten rel%substitute((ideal vars T)^2,ART);
     rel2:=a0*b2+a2*b0;
     betti(drel:=transpose diff(transpose (substitute(vars A,ART)|substitute(vars B,ART)),flatten rel2));
     betti (rel1:=transpose flatten(a1*b1));
E:=(extend(chainComplex(drel),chainComplex(rel1),id_(target rel1)))_1;
aa:=transpose E^{0..r0*r1-1};
bb:=transpose E^{r0*r1..((r0+r2)*r1-1)};
aa2:=substitute(mA,aa*transpose substitute(autA,ART));
bb2:=substitute(mB,bb*transpose substitute(autB,ART));
--(flatten ((a0+a1-aa2)*(b0+b1-bb2)))%substitute((ideal vars T)^3,ART);
(substitute(a0+a1-aa2,RT),substitute(b0+b1-bb2,RT))
)
end

restart
load "deform.m2"
kk=ZZ/101
S=kk[x,y,z]
--m=map(S^{0,1},S^{2:-1},matrix{{x,y-z},{y*z,x^2}})
m=matrix{{x,0,y-z},{y,x,0},{0,z,x}}
m=matrix{{x,y,z+y,0},{0,x,y,z-y},{y,0,x,y},{y,z,0,x}}

-- d=4;m=random(S^d,S^{d:-1})
isHomogeneous m
f=det m
--f=x^3+y^3+z^3
dim  ideal jacobian ideal f ==0
--radical ideal jacobian ideal f
R=S/f
L=coker substitute(m,R)
d=3
use R
L=((prune ((ideal(x,y,z))^d*R^1))**R^{d}) 

betti L
time L1=firstOrderDeformation(L)
vars T
RT1=RT/substitute((ideal vars T)^2,RT)
RT2=RT/substitute((ideal vars T)^3,RT)
load "local.m2"
setMaxIdeal(ideal vars RT1)
L1s=substitute(L1,RT1)
--det L1%substitute((ideal vars T)^2,RT)
fL1s=localResolution(coker L1s,LengthLimit=>2)
--betti fL1s.dd_1
--betti res(L,LengthLimit=>3)

time L2=secondOrderDeformation(L1,T);
substitute(L2#0,RT1)*substitute(L2#1,RT1)
substitute(L2#0,RT2)*substitute(L2#1,RT2)
betti L2#0
L2#0*L2#1
vars T
--det L2#0% substitute((ideal vars T)^3,RT)
load "local.m2"
load "computingRpi_star.m2"
--- test case d=4 only --
A1=kk[gens T,Degrees=>{#gens T:{2,0}}]
S1=kk[gens RT,Degrees=>{3:{1,1},#gens T:{2,0}}]
k=2
A=A1/((ideal gens A1)^k)
setMaxIdeal(ideal vars A)
S=S1/((ideal substitute(vars A1,S1))^k)
setMaxIdeal(ideal vars S)
xx=matrix{{x,y,z}}
localPrune coker gens annihilator coker substitute(L2#0,S)
m=substitute(L2#0,S)
M= coker (m|map(S^6,S^{6:{-6,0}},substitute(f,S)*id_(S^6)))
 annihilator  M:ideal substitute(f,S)
 ideal substitute(f,S):annihilator M
E1=kk[e_0,e_1,e_2,gens A1,Degrees=>{3:{1,1},#gens T:{2,0}},SkewCommutative=>true]
E=E1/((ideal substitute(vars T,E1))^k)
k
setMaxIdeal(ideal vars E)
ee=matrix{{e_0,e_1,e_2}}
d=0
localPrune M
time Md=presentation localPrune((ideal(x,y,z))^d*M)**S^{{0,d}};
betti Md
Md
time N= localPrune coker symmetricToExteriorOverA(Md,ee,xx);
N
bettiT dual chainComplex(presentation N)

res N
time fN=res (N,LengthLimit=>2)[d-1]**E^{{d-1,d}}
bettiT dual fN
bettiT dual chainComplex fN.dd_3
fN.dd_3
Rm=RT/substitute((ideal vars T)^3,RT)
m=substitute(L2#0,Rm)
m0=substitute(substitute(L2#0,R),Rm)
n=m0


vars ring L1
t2=substitute((ideal vars T)^2,RT)
Reps=RT/t2
L0=substitute(presentation(L),Reps)
L1=substitute(L1,Reps)
-- O=Hom(coker L0,coker L1)
--stdio:24:3: expected homogeneous matrix


---------------------------------
--g=6 canonical out of memory

restart
load "formalGroupStructure.m2"
kk=ZZ/101
P=kk[x,y,z]
bs=ideal{x*y-x*z,x*z-y*z}
H=gens intersect(bs,(ideal vars P)^3)
S=kk[v_0..v_5]
J=kernel map(P,S,H)
dim (J+ideal{v_0+v_3,v_1,v_4,v_3+v_5})
m=matrix{{v_0+v_3,v_1},{v_4,v_3+v_5}}
JC=J+ideal det m
betti res JC
R=S/JC
La= coker substitute(m,R)
L=prune truncate(1, La)**R^{1}
--betti res L
time L1=firstOrderDeformation(L)
vars T


