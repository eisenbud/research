restart
kk=ZZ/101
R=kk[a,b,c]
pts=transpose matrix{{1,0,0},{0,1,0},{0,0,1},{1,1,1}}

idealOfPoints=(pts,R)->(
     r:=rank source pts;
     intersect(apply(r,j->ideal (vars R *(syz(substitute(transpose pts_{j},R)))))))
distinctPoints=(I)->(
     m:=vars ring I;
     dim (minors(2,diff(transpose m,gens I))+I)==0)

iE=idealOfPoints(pts,R)
distinctPoints(iE)

d=4
Mukailinebundle=(d,iE)->(
     R:=ring iE;
     if (max degrees source gens iE)_0 <= d then (
     	  while (phi1:=random(R^(d-1),R^{d:-1});
	        iG:=minors(d-1,phi1);
	         not distinctPoints(iG) or not dim(iG+iE) == 0)
     	  do ();
     	  EG:=gens intersect(iE,iG);
	  while (A:=ideal(EG*random(source EG, R^{2:(-2*d+2)}));
		not distinctPoints(A))
	  do ();    
	  phi2:=(syz(gens(iG)|gens(A)))^{0..d-1}; 
	  iEF:=minors(d,phi2);
     	  iE2:=saturate(iE*iE);
	  E2F:=gens intersect(iE2,iEF);
	  while (C:=ideal(E2F*random(source E2F,R^{-3*d+3}));
     	       not degree ideal diff(vars R,gens C) == degree iE)
	  do ();
     	  L1:=(syz(gens iEF| gens C))^{0..d};
     	  L1**R^(min degrees target L1) )
     else (<< "degree condition failed"))
L=Mukailinebundle(3,iE)
betti L
degree iE

-------
d=5
betti iE
specialUlrichSheaf=(d,iE,s)->(
     R:=ring iE;
     H:=gens intersect(ideal symmetricPower(d,vars R),iE);
     n:=rank source H - 1 ;
     S:=(coefficientRing R)[s_0..s_n]; 
     iX:=ker(map(R,S,H));
     r:=regularity(coker gens iX)+1;
     -- r should be large enough
     -- I have no argument why this suffices and only experimental evidence
     sr:=symmetricPower(r, vars S);
     ss:=rank source sr;
     hr:=symmetricPower(r,H);
     L:=Mukailinebundle(d,iE);
     L1:=(syz(L|((hr++hr)++random(R^{d-1:(-d+2)},R^0)),DegreeLimit=>((r*d))))^{d+1..(2*ss+d)};
     L2:=substitute(lift(L1,coefficientRing R),S);    
     L3:=((sr++sr)*(L2**S^{-d+1}));
     SX:=S/iX;
     Fd:=presentation prune image substitute(L3,SX);
     Ff:=res(image transpose Fd,DegreeLimit=>1,LengthLimit=>2);
     lift(Ff.dd_2,S))

d=5;e=16;
pts=random(R^3,R^e);
iE=idealOfPoints(pts,R);degree iE
betti(F=specialUlrichSheaf(5,iE,t))
betti res coker F
degree iE
----------
ExistenceOfUlrich=(d,e,R)->(
     pts:=random(R^3,R^e);
     iE:=idealOfPoints(pts,R);
     F=specialUlrichSheaf(d,iE,t);
     dim coker F == 3 and (rank target F == degree coker F)
     )  

ExistenceOfUlrich(5,16,R)
betti F
