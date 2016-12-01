restart
idealOfPoints=(pts,R)->(
     r:=rank source pts;
     intersect(apply(r,j->ideal (vars R *(syz(substitute(transpose pts_{j},R)))))))
distinctPoints=(I)->(
     m:=vars ring I;
     dim (minors(2,diff(transpose m,gens I))+I)==0)


kk=ZZ/3
R=kk[a,b,c]
pts=transpose matrix{{1,0,0},{0,1,0},{0,0,1},{1,1,1},{1,1,-1}}
iE=idealOfPoints(pts,R)
random(1,R)
while( while( pts2=random(ZZ^3,ZZ^3 );
     	    iG=idealOfPoints(pts2,R);
     	    not degree iG==3)
       do();
       not dim (iE+iG)==0)
do();

phi1=syz gens iG
m4=ideal symmetricPower(4,vars R);
EG4=gens intersect(iE,iG,m4);
betti EG4
degree coker EG4
m6=ideal symmetricPower(6,vars R);
while (A=ideal(map(R^1,R^{2:-4},EG4*substitute(lift(random((ZZ/3)^7,(ZZ/3)^2),ZZ),R)));
       not distinctPoints(A))
do ();    
degree A
distinctPoints A

phi2=(syz(gens(iG)|gens(A)))^{0..2} 
iEF=minors(3,phi2);
iE2=saturate(iE*iE);
E2F6=gens intersect(iE2,iEF,m6);
while (while (C=ideal(map(R^1,R^{-6},E2F6*substitute(lift(random((ZZ/3)^5,(ZZ/3)^1),ZZ),R)));	  
          not degree(ideal diff(vars R,gens C) +C)== degree iE)
       do ();
       LL1=gens iEF|gens C;
       L1=(syz((gens iEF)| gens C))^{0..3};
       L=L1**R^(min degrees target L1); 
       not dim minors(2,L^{2..3}) == 0 )
do();
------- 
dim minors(2,L^{2..3})
degree(ideal diff(vars R,gens C) +C)== degree iE
betti L
--------
H=gens intersect(ideal symmetricPower(3,vars R),iE);
n=4;
S=(coefficientRing R)[s_0..s_n]; 
iX=ker(map(R,S,H));
r=2;
sr=symmetricPower(r, vars S);
ss=rank source sr;
hr=symmetricPower(r,H);
L1=(syz(L|((hr++hr)++random(R^{(3-1):(-3+2)},R^0)),DegreeLimit=>((r*3))))^{3+1..(2*ss+3)};
betti L
betti L1
L2=substitute(lift(L1,coefficientRing R),S);    
L3=((sr++sr)*(L2**S^{-3+1}));
SX=S/iX;
Fd=presentation prune image substitute(L3,SX);
Ff=res(image transpose Fd,DegreeLimit=>1,LengthLimit=>2);
betti(F=lift(Ff.dd_2,S))
betti(FF =res coker F)
-- total: 8 16 8
--     0: 8 16 8
------------------

E=kk[e_0..e_n,SkewCommutative=>true]
M1=substitute(FF.dd_1,vars E)*substitute(FF.dd_2,vars E);
socle=product(n+1,j->e_j)
M2=diff(M1,socle);
betti(N=syz(M2))
betti res(coker transpose N,LengthLimit=>4)
ET=kk[e_0..e_n,t_1..t_(28),Degrees=>{n+1:1,28:2},SkewCommutative=>true]
T=genericSkewMatrix(ET,t_1,8)
t=matrix{{t_1..t_28}};
SM=transpose  diff(transpose t,flatten(T*substitute(N,ET)));
betti(M1=syz(substitute(SM,E),DegreeLimit=>1))
M=map(E^8,E^{8:-3},substitute(T,vars E|flatten M1));
betti res( coker M,LengthLimit=>3)
----------------------------------
E3= mingens ideal symmetricPower(3,vars E)
transpose  E3
a=symbol a
b=symbol b
c=symbol c
e=symbol e
EP=kk[x_0..x_4,a..j,Degrees=>{5:1,10:3}]
describe EP
rel=matrix{{a-x_0*x_1*x_2,b-x_0*x_1*x_3,c-x_0*x_1*x_4,d-x_0*x_2*x_3,e-x_0*x_2*x_4,
	  f-x_0*x_3*x_4,g-x_1*x_2*x_3,h-x_1*x_2*x_4,i-x_1*x_3*x_4,j-x_2*x_3*x_4}}
transpose rel
MP=substitute(M,matrix{{x_0..x_4}})
PP=EP/ideal rel
MM=lift(substitute(MP,PP),EP)
MM+transpose MM
texMath MM
