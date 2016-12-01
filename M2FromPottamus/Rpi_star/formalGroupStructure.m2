firstOrderDeformation=(L)->(
     --the  presentation matrix of the first order deformation of the module
     -- L 
     R:=ring L;
--     kk=coefficientRing R
     fL:=res( L,LengthLimit=>2);
--fL.dd_1
--fL.dd_2
--betti fL
     da:=-degrees Hom(fL_1,fL_0);     
     r0:=rank fL_0;
     r1:=rank fL_1;
     r2:=rank fL_2;
     r01:=r0*r1;
     db:=-degrees Hom(fL_2,fL_1);
     A:=kk[a_(1,1)..a_(r0,r1),Degrees=>da];
     B:=kk[b_(1,1)..b_(r1,r2),Degrees=>db];
     AB:=A**B;
     AR:=AB**R;
     mA:=map(A^(-degrees fL_0),A^(-degrees fL_1),genericMatrix(A,a_(1,1),r0,r1));
     L1:=substitute( fL.dd_1,AR);L2=substitute(fL.dd_2,AR);
     mA1:=substitute(mA,AR);
     mB:=map(B^(-degrees fL_1),B^(-degrees fL_2),genericMatrix(B,b_(1,1),r1,r2));
     mB1:=substitute(mB,AR);
     eq1:=flatten( mA1*L2+L1*mB1);
     eqM:=diff(transpose substitute(vars AB,AR),eq1);
     sol1:=syz transpose substitute(eqM,R);
     sol1A:=sol1^{0..r0*r1-1};
--hilbertFunction(-1,image sol1A)
     C:=kk[c_1..c_(r0*r1)];
     CR:=C**R;
     mC:=genericMatrix(C,c_1,r1,r0);
     mC0:=substitute(mC,CR);
     mC1:=(substitute(fL.dd_1,CR)*mC0);
     --triv1:= transpose substitute( diff(transpose substitute(vars C,CR),flatten mC1),R)**R^{-1};
     triv1:= substitute( diff(transpose substitute(vars C,CR),flatten mC1),R)**R^{-1};
--<<vars C<<endl;
--<<flatten mC<<endl;
     mC2:=mC0*substitute(fL.dd_1,CR);
     triv2:=transpose substitute(diff(transpose substitute(vars C,CR),flatten mC2),R)**R^{-1};
     --
     <<betti triv1 <<endl;
     <<betti triv2 <<endl;
     --def0:=mingens image (gens truncate(0,image sol1A)%gb image (triv1|triv2));
     --test new line
     def0:=mingens image (gens truncate(0,image sol1A)%gb image triv1);
     tt:=rank source def0;
     T=kk[t_1..t_tt];
     RT=R**T;
     defT:=substitute(def0,RT)*transpose substitute(vars T,RT);
     A1:=substitute(mA,transpose defT);
     substitute(fL.dd_1,RT)+A1)
     
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
--isHomogeneous a2;
     use B;
     mB:=map(B^(-degrees F0_1),B^(-degrees F1_1)**B^{-1},genericMatrix(B,b_(1,1),r1,r2));
--isHomogeneous mB;
--isHomogeneous mA;
     b2:=substitute(mB,ART);
     a0:=substitute(F0.dd_1,ART);
     a1:=substitute(EL1_0,ART);
     b0:=substitute(F1.dd_1,ART)**ART^{-1};
     b1:=-substitute(EL1_1,ART)**ART^{-1};    
--     rel:=(a0+a1)*(b0+b1);
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
aa2:=substitute(mA,aa);
bb2:=substitute(mB,bb);
--(flatten ((a0+a1-aa2)*(b0+b1-bb2)))%substitute((ideal vars T)^3,ART);
(substitute(a0+a1-aa2,RT),substitute(b0+b1-bb2,RT))
)
end
Hom(Matrix,Matrix):=(m,n)->(
     Rm=ring n;
     n1=syz transpose n;
     n2=transpose syz n1;
     kk=coefficientRing Rm
     da=-degrees Hom(target m,source n2)
     r0=rank source n2
     r1=rank target m
     A=kk[a_(1,1)..a_(r0,r1),Degrees=>da]
     mA=genericMatrix(A,a_(1,1),r0,r1)
     RmA=Rm**A
     mA1=substitute(mA,RmA)     
     hom1=ideal (substitute(m,RmA)*mA1)+ideal( mA1*substitute(n2,RmA));
     betti(hom2=transpose diff(transpose substitute (vars A,RmA),gens hom1))
time      betti(hom3=syz substitute(hom2,Rm))

end
restart
load "formalGroupStructure.m2"
kk=ZZ/101
S=kk[x,y,z]
--m=map(S^{0,1},S^{2:-1},matrix{{x,y-z},{y*z,x^2}})
m=matrix{{x,0,y-z},{y,x,0},{0,z,x}}
m=matrix{{x,y,z+y,0},{0,x,y,z-y},{y,0,x,y},{y,z,0,x}}

-- d=4;m=random(S^d,S^{d:-1})
isHomogeneous m
f=det m
f=x^3+y^3+z^3
dim  ideal jacobian ideal f ==0
--radical ideal jacobian ideal f
R=S/f
L=coker substitute(m,R)
d=2
L=((prune ((ideal(x,y,z))^d*R^1))**R^{d})
annihilator L
L=prune truncate(2,R^1)
annihilator L 
time L1=firstOrderDeformation(L)
--time L2=secondOrderDeformation(L1,T);
vars T
load "local.m2"
load "computingRpi_star.m2"
--- test case d=4 only --
A1=kk[gens T,Degrees=>{3:{2,0}}]
S1=kk[gens RT,Degrees=>{3:{1,1},3:{2,0}}]
k=3
A=A1/((ideal gens A1)^k)
setMaxIdeal(ideal vars A)
S=S1/((ideal substitute(vars A,S1))^k)
setMaxIdeal(ideal vars S)
xx=matrix{{x,y,z}}
m=substitute(L2#0,S)
M= coker m
E1=kk[e_0,e_1,e_2,gens A,Degrees=>{3:{1,1},3:{2,0}},SkewCommutative=>true]
E=E1/((ideal substitute(vars T,E1))^k)
setMaxIdeal(ideal vars E)
ee=matrix{{e_0,e_1,e_2}}
d=2
time Md=presentation localPrune((ideal(x,y,z))^d*M)**S^{{0,d}}
time N=presentation localPrune coker symmetricToExteriorOverA(Md,ee,xx)
time fN=(localResolution(coker N,LengthLimit=>2*d))[d-1]**E^{{d-1,d}}
bettiT dual fN

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


