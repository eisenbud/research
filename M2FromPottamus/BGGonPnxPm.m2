setupRings=method()
setupRings(Ring,List) := (kk,n) -> (
     t:= #n;
     x:= symbol x;
     xx:=flatten apply(t,i->apply(n_i+1,j->x_(i,j)));
     degs:=flatten apply(t,i->apply(n_i+1,k->apply(t,j->if i==j then 1 else 0)));
     Sloc:=kk[xx,Degrees=>degs];
     e:= symbol e;
     ee:=flatten apply(t,i->apply(n_i+1,j->e_(i,j)));
     Eloc:=kk[ee,Degrees=>degs,SkewCommutative=>true];
     h:=symbol h;
     H:=ZZ[h];
     return(Sloc,Eloc,H))
TEST ///
restart
load("BGGonPnxPm.m2")
n={1,2}
kk=ZZ/101
(S,E,H)=setupRings(kk,n)
scan(#n,i->scan(n_i+1,j->x_(i,j)=S_(sum(i,k->n_k+1)+j)))
scan(#n,i->scan(n_i+1,j->e_(i,j)=E_(sum(i,k->n_k+1)+j)))

m=matrix{{x_(0,0),x_(1,0)},
       {x_(0,1),0},
       {0,x_(1,1)},
       {0,x_(1,2)}}
betti m
mE=symExt(m,E)
///


subMatrix=(m,d,e) -> (
     columns=select(rank source m, i-> degree m_i==e);
     rows=select(rank target m, i-> (degrees target m)_i ==d);
     transpose (transpose m_columns)_rows) 


cohomologyTable=method()
cohomologyTable(ChainComplex,Ring) := (F,H) -> (
     E:= ring F; 
     if not #unique degrees E==2 then error "works only for two factors";
     L1=toList((min F-0)//2..(max F-0)//2);
     matrix apply(L1,i->apply(L1,j->sum(numgens H,p-> H_0^p*(tally degrees F_(i+j-p))_{i,j}))))
cohomologyTable(ChainComplex,Ring,List,List) := (F,H,da,db) -> (
     E:= ring F; 
     if not #unique degrees E==2 then error "works only for two factors";
     matrix apply(toList(da_0..db_0),i->apply(toList(da_1..db_1),j->sum(numgens H,p-> H_0^p*(tally degrees F_(i+j-p))_{i,j}))))
cohomologyTable(ChainComplex,List,List) := (F,da,db) -> (
     E:= ring F; 
     if not #unique degrees E==2 then error "works only for two factors";
     L:=flatten apply(toList(min F..max F),k->apply(degrees F_k,deg->sum deg-k));
     minL:=min L;maxL := max L;
     h:=symbol h;
     H:=ZZ[h];
     matrix apply(toList(da_0..db_0),i->apply(toList(da_1..db_1),j->sum(0..(maxL- minL) ,p-> h^p*(tally degrees F_(i+j-p-minL))_{i,j})))
     )
TEST ///
n={1,2}
kk=ZZ/101
(S,E,H)=setupRings(kk,n)
F=dual res((ker transpose vars E)**E^{{ 2,3}},LengthLimit=>8)
betti F
apply(min F..max F,i->tally degrees F_i)
cohomologyTable(F,H) 

n={1,2}
(S,E,H)=setupRings(ZZ/101,n)
use S
vars S
m=map(S^4,S^{{ -1,0},{0,-1}}, transpose matrix{{S_0,S_1,0,0},{S_2,0,S_3,S_4}})
mE=symExt(m,E)
time fB=dual res(coker transpose mE,LengthLimit=>10)
cohomologyTable(fB,{ -5,-5},{0,0})

deg={ -3,-3}
m= corner(fB,deg);
f= res( ker  m,LengthLimit=> 16)[-sum deg-2]

cohomologyTable(f,{ -5,-5},{ 5,5})
cohomologyTable(f**E^{{ 1,1}},{ -5,-5},{ 5,5})
///

boxDegrees=method()
boxDegrees(Ring) := E -> (
     degs:= unique degrees E;
     t:=#degs;
     n:=apply(t,k->#select(degrees E,d->d==degs_k)-1);
     deg:=0*n;
     box:={deg};
     scan(#n,k->
	  box=flatten apply(box,deg-> apply(n_k+1,i->deg+i*degs_k))
	  );
     box)	    
TEST ///
n={1,2,2}
(S,E,H)=setupRings(ZZ/101, n);
boxDegrees E
///


corner=method()
corner(ChainComplex,List) := (F,deg) ->(
     E:=ring F;
     degsE:= unique degrees E;
     assert(
	  #(degrees E)_0 == # deg
	  );
     box:=boxDegrees E;
     k:=sum deg;
     degsa:=degrees F_k;     
     L1:=flatten apply(box,boxdeg->select(#degsa,i->degsa_i==deg+boxdeg));
     degsb:=degrees F_(k-1);
     L2:=unique flatten apply(degsE,degE-> flatten apply(box,boxdeg->select(#degsb,i->degsb_i==deg+boxdeg-degE)));
     transpose (transpose F.dd_k_L1)_L2
     )
TEST ///
n={1,2}
kk=ZZ/101
(S,E,H)=setupRings(kk,n)
F=dual res((ker transpose vars E)**E^{{ 2,3}},LengthLimit=>10)
betti F
apply(min F..max F,i->tally degrees F_i)

deg={ -2,-1} 
m=corner(F,deg);
tally degrees source m, tally degrees target m
Fm=(res(ker m,LengthLimit=>10))[-sum deg-#n]
betti Fm
quadrant(Fm,H,{4,4},{ -5,-5})
cohomologyTable(Fm,H,deg+{1,1},deg+{5,5})
///

corner(ChainComplex,ZZ,List) := (F,k,deg) ->(
     E:=ring F;
     degsE:= unique degrees E;
     n:=apply(degsE,dege->#select(degrees E,d->d==dege)-1);
     assert(
	  #(degrees E)_0 == # deg
	  );
     degsa:=degrees F_k;     
     L1:=select(#degsa,i->#select(#deg,j->degsa_i_j<=deg_j+n_j)==#deg);
     degsb:=degrees F_(k-1);
     L2:=select(#degsb,i->#select(#deg,j->degsb_i_j<=deg_j+n_j)==#deg);
     transpose (transpose F.dd_k_L1)_L2
     )
TEST///
n={1,1}
(S,E,H)=setupRings(ZZ/101,n)

time fB=dual res(coker random(E^7,E^{13:{ -1,0},11:{0,-1}}),LengthLimit=>10);	 	  
cohomologyTable(fB,H,{ -5,-5},{0,0})
deg={ -3,-3}
m= corner(fB,deg);
f= res( ker  m,LengthLimit=> 16)[-sum deg-2]
betti m, tally degrees target m, tally degrees source m
m= corner(fB,-6,{ -4,-4});
betti m, tally degrees target m, tally degrees source m
deg={3,3}
m=corner(f,deg);
betti m, tally degrees target m, tally degrees source m
m=corner(f,6,deg);
betti m, tally degrees target m, tally degrees source m
///
quadrant=method()
quadrant(ChainComplex,Ring,List,List) := (F,H,deg1,deg2) ->(
     m:=corner(F,deg1);
     n:=apply(unique degrees ring F,e->#select(degrees ring F,d->d==e)-1);
     injRes:=dual res( coker transpose m,LengthLimit=> (sum deg1-sum deg2))[-sum deg1];
     cohomologyTable(injRes,H,deg2,deg1+n+{1,1})
     )

quadrant(ChainComplex,Ring,Sequence) := (F,H,L) ->(
     (k,deg1,deg2):=L;
     m:=corner(F,k,deg1);
     n:=apply(unique degrees ring F,e->#select(degrees ring F,d->d==e)-1);
     injRes:=dual res( coker transpose m,LengthLimit=> (sum deg1-sum deg2))[-sum deg1];
     cohomologyTable(injRes,H,deg2,deg1+n+{1,1})
     )

quadrant(ChainComplex,Sequence) := (F,L) ->(
     (k,deg1,deg2):=L;
     m:=corner(F,k,deg1);
     n:=apply(unique degrees ring F,e->#select(degrees ring F,d->d==e)-1);
     injRes:=dual res( coker transpose m,LengthLimit=> (sum deg1-sum deg2))[-sum deg1];
     cohomologyTable(injRes,deg2,deg1+n+{1,1})
     )

quadrant(ChainComplex,Sequence) := (F,L) ->(
     (k,deg1,deg2):=L;
     m:=corner(F,k,deg1);
     n:=apply(unique degrees ring F,e->#select(degrees ring F,d->d==e)-1);
     injRes:=dual res( coker transpose m,LengthLimit=> (sum deg1-sum deg2))[-sum deg1];
     cohomologyTable(injRes,deg2,deg1+n+{1,1})
     )

tateCut=method()
tateCut(ChainComplex,Sequence):= (F,L)->(
     (k,deg1,deg2,deg3):=L;
     m:=corner(F,k,deg1);
     n:=apply(unique degrees ring F,e->#select(degrees ring F,d->d==e)-1);
     injRes:=dual res( coker transpose m,LengthLimit=> (sum deg1-sum deg2))[-sum deg1];
     projRes:=res(ker m,LengthLimit => (sum deg3-sum deg1))[-sum deg1-2];
     (cohomologyTable(injRes,deg2,deg1+n+{1,1}),cohomologyTable(projRes,deg1+((k-sum deg1)//2)*{1,1}-n,deg3),betti injRes,betti projRes)
     )     



symExt=method()
symExt(Matrix,Ring) := (m,E) -> (
     ev := map(E,ring m,vars E);
     mt := transpose jacobian m;
     jn := ev(syz mt);
     a:=(vars E**E^(rank target m));
--betti a,tally degrees source a, isHomogeneous a     
--betti jn, tally degrees target jn, tally degrees source jn, isHomogeneous jn
--tally(     degrees target jn+degrees source a)
     b:=a*jn;
--betti b, tally degrees target b, tally degrees source b
     c:=map(target b,E^(degrees source jn),b);
     transpose c)

    
TEST ///       
n={1,2}
(S,E,H)=setupRings(ZZ/101,n)
use S
vars S
m=map(S^4,S^{{ -1,0},{0,-1}}, transpose matrix{{S_0,S_1,0,0},{S_2,0,S_3,S_4}})
mE=symExt(m,E)

///
beilinsonWindow=method()
beilinsonWindow(ChainComplex) := C-> (
     E:= ring C;
     length C;
     t:=#unique degrees E;
     n:=apply(unique degrees E,d-> (#select( degrees  E, e-> e==d)-1));
     Ck:=0;sourceCK:=0; tragetCK:=0;d:=0;
     W:=chainComplex apply(min C+1..max C,k-> (Ck=C.dd_k;
	  --source indices and target rows and columns in the Beilison window
	  sourceCK = select(rank source Ck,i-> (d=degree (source Ck)_i;#select(#d,i->d_i>=0 and d_i<=n_i)==#n));	
          targetCK =  select(rank target Ck,i-> (d=degree (target Ck)_i;#select(#d,i->d_i>=0 and d_i<=n_i)==#n));	
     	  (transpose (transpose Ck)_targetCK )_sourceCK));
     return W[-min C]) 

isChainComplex=method()
isChainComplex(ChainComplex) := W -> (
     lengthW:= max W- min W;
     #select(min W+1..max W-1,i->W.dd_i*W.dd_(i+1)==0) ==lengthW-1)

TEST ///
n={3}
(S,E,H)=setupRings(ZZ/101,n)
betti (fE=res coker vars E)
min fE, max fE
length fE
min fE, max fE
W=beilinsonWindow fE
C=chainComplex {fE.dd_2,fE.dd_3 }[-1]
W=beilinsonWindow C
W=beilinsonWindow fE
W=beilinsonWindow fE**E
W=beilinsonWindow(fE**E^{{ 1}})
W=beilinsonWindow fE
apply(min W..max W-1,i->W.dd_i*W.dd_(i+1)==0)
isChainComplex W
betti W
min W, max W
///
outsideBeilinsonRange=method()
outsideBeilinsonRange(Matrix) :=  m -> (
     E:= ring m;
     t:=#unique degrees E;
     n:=apply(unique degrees E,d-> (#select( degrees  E, e-> e==d)-1));
	  --source indices not in the Beilison window
     sourcem = select(rank source m,i-> (d=degree (source m)_i;#select(#d,i->d_i<0 or d_i>n_i)>0));
     m_sourcem)	
          


end
outsideBeilinsonSource=method()
outsideBeilinsonSource(Matrix) :=  m -> (
     E:= ring m;
     t:=#unique degrees E;
     n:=apply(unique degrees E,d-> (#select( degrees  E, e-> e==d)-1));
	  --source indices not in the Beilison window
     d:=0;
     sourcem = select(rank source m,i-> (d:=degree (source m)_i;#select(#d,i->d_i<0 or d_i>n_i)>0));
     m_source m)	

outsideBeilinsonTarget=method()
outsideBeilinsonTarget(Matrix) :=  m -> (
     E:= ring m;
     t:=#unique degrees E;
     n:=apply(unique degrees E,d-> (#select( degrees  E, e-> e==d)-1));
	  --source indices not in the Beilison window
     d:=0;
     targetm := select(rank target m,i-> (d=degree (target m)_i;#select(#d,i->d_i<0 or d_i>n_i)>0));
     transpose (transpose m)_targetm)          

     

tateExtension=method()
tateExtension(ChainComplex) := C -> (
     W:=beilinsonWindow C;
     minW := min W;
     maxW := max W;
     k=minW;
     mk:=W.dd_(k+1)     
     Ck:=(chainComplex transpose syz transpose mk)[-k+1]
     beilinsonWindow Ck
     betti Ck
     coCk=transpose (mingens image transpose (W.dd_k||gens truncate(n,image Ck.dd_k)))
     coCk=outsideBeilinsonTarget (coCk||W.dd_k)
     mk'=outsideBeilinsonSource m
     m=(mingens image (gens truncate(n,image syz coCk)|mk))
	  )|mk
	  )|mk

     betti mk,betti mk'
     betti res coker transpose  mk'
TEST ///
n={3}
(S,E,H)=setupRings(ZZ/101,n)
vars E
vars S
betti (fE=res ideal vars E)
C=chainComplex {fE.dd_2,fE.dd_3 }[3]
W=beilinsonWindow C

///

restart
load "BGGonPnxPm.m2"         
n={1,1}
(S,E,H)=setupRings(ZZ/101,n)



time fB=dual res(coker random(E^7,E^{13:{ -1,0},11:{0,-1}}),LengthLimit=>10);	 	  
cohomologyTable(fB,H,{ -5,-5},{0,0})
deg={ -3,-3}
m= corner(fB,deg);
f= res( ker  m,LengthLimit=> 16)[-sum deg-2]
m=corner(f,{3,3});betti m,tally degrees target m, tally degrees source m
m=corner(f,6,{3,3});betti m,tally degrees target m, tally degrees source m
quadrant(f,H,{3,3},{ -1,-1})
quadrant(f,H,(6,{3,4},{ -1,-1}))
quadrant(f,H,{3,4},{ -1,-1}),quadrant(f,H,{4,4},{ -1,-1})
quadrant(f,H,(6,{3,4},{ -1,-1})),quadrant(f,H,(7,{4,4},{ -1,-1}))
quadrant(f,H,{1,1},{ -1,-1}),quadrant(f,H,{1,2},{ -1,-1}),quadrant(f,H,{2,2},{ -1,-1})
quadrant(f,H,(2,{1,2},{ -1,-1})),quadrant(f,H,(3,{1,3},{ -1,-1})),quadrant(f,H,(4,{2,3},{ -1,-1}))

fBpartB=res(ker m,LengthLimit=>14)[-sum deg-2]
cohomologyTable(fB,H,deg-{1,1},{0,0})
cohomologyTable(fBpartA,H,{ -5,-5},deg+{1,1})
cohomologyTable(fBpartB,H,deg,deg+{8,8})

cohomologyTable(fBpartB,H,{-1,-1},{7,7})
deg1={2,2},deg2={ -3,-3}
F=fBpartB;
betti F

quadrant(F,H,{3,2},{ -3,-3}),quadrant(F,H,{3,3},{ -3,-3})
quadrant(F,H,{3,3},{ -3,-3}),quadrant(F,H,{4,3},{ -3,-3})
m1=corner(fBpartB,deg1);betti m1
fBpartA1=dual res( coker transpose m1,LengthLimit=> 12)[-sum deg1]
betti m1,betti syz m1
fBpartB1=res(ker m1,LengthLimit=>14)[-sum deg1-2]
betti fBpartB1
cohomologyTable(fBpartA1,H,{ -5,-5},deg1+{1,1})
cohomologyTable(fBpartB1,H,deg1,deg1+{8,8})
-- interpretation of the first term
matrix apply(toList(-1..6),i->apply(toList(-1..6),j->hilbertFunction({i,j},ker m1)))
matrix apply(toList(-1..6),i->apply(toList(-1..6),j->hilbertFunction({i,j},coker fBpartB1.dd_3)))-----m1)))


deg1={2,0}
m1=corner(fBpartB,deg1);betti m1
fBpartA1=dual res( coker transpose m1,LengthLimit=> 12)[-sum deg1]
betti m1,betti syz m1
fBpartB1=res(ker m1,LengthLimit=>14)[-sum deg1-2]

cohomologyTable(fBpartA1,H,{ -5,-5},deg1+{1,1}),cohomologyTable(fBpartB1,H,deg1,deg1+{8,8})
cohomologyTable(fBpartB,H,{ -5,-5},deg1+{8,8})


restart
load "BGGonPnxPm.m2"           
n={1,2}
(S,E,H)=setupRings(ZZ/101,n)

time fB=dual res(coker random(E^3,E^{5:{ -1,0},8:{0,-1}}),LengthLimit=>10);	 	  
cohomologyTable(fB,H,{ -5,-5},{0,0})
deg={ -3,-3}
m= corner(fB,deg);
fBpartA=dual res( coker transpose m,LengthLimit=> 7)[-sum deg]

fBpartB=res(ker m,LengthLimit=>14)[-sum deg-2]
cohomologyTable(fB,H,deg-{1,1},{0,0})
cohomologyTable(fBpartA,H,{ -5,-5},deg+{1,1})
cohomologyTable(fBpartB,H,deg,deg+{8,8})
F=fBpartB
quadrant(F,H,{2,2},{ -1,-1}),quadrant(F,H,{3,2},{ -1,-1}),quadrant(F,H,{3,3},{ -1,-1}),
apply(toList(-4..10),k->(k,tally degrees F_k))
tally degrees F_(1), tally degrees F_(2)
degsF1=degrees F_1; degsF2=degrees F_2;
tally degsF1, tally degsF2
L1=select(#degsF1,i->degsF1_i_0==3)
L2=select(#degsF2,i->degsF2_i_0==3)
m=transpose (transpose F.dd_2_L2)_L1
betti res coker m

degsF1=degrees F_1; degsF2=degrees F_2;
tally degsF1, tally degsF2
L1=select(#degsF1,i->degsF1_i_0==2)
L2=select(#degsF2,i->degsF2_i_0==2)
m=transpose (transpose F.dd_2_L2)_L1
betti res coker m
betti F

restart
load "BGGonPnxPm.m2"           
n={1,2}
(S,E,H)=setupRings(ZZ/101,n)
time fB=dual res(coker random(E^2,E^{3:{ -1,0},5:{0,-1}}),LengthLimit=>12);	 	  
cohomologyTable(fB,H,{ -5,-5},{0,0})
deg={ -3,-3}
m= corner(fB,deg);
fBpartA=dual res( coker transpose m,LengthLimit=> 7)[-sum deg]

fBpartB=res(ker m,LengthLimit=>14)[-sum deg-2]
cohomologyTable(fB,H,deg-{1,1},{0,0})
cohomologyTable(fBpartA,H,{ -5,-5},deg+{1,1})
cohomologyTable(fBpartB,H,deg,deg+{7,7})
F=fBpartB
quadrant(F,H,{1,1},{ -2,-2}),quadrant(F,H,{1,2},{ -2,-2}),quadrant(F,H,{1,3},{ -2,-2})
quadrant(F,H,(2,{1,1},{ -2,-2})),quadrant(F,H,(3,{1,2},{ -2,-2})),quadrant(F,H,(4,{1,3},{ -2,-2}))
quadrant(F,H,(1,{1,1},{ -2,-2})),quadrant(F,H,(2,{1,2},{ -2,-2})),quadrant(F,H,(3,{1,3},{ -2,-2}))


quadrant(F,H,{1,4},{ -2,-2}),quadrant(F,H,{1,5},{ -2,-2}),quadrant(F,H,{1,6},{ -2,-2})


 
restart
load("BGGonPnxPm.m2")
n={1,2}
kk=ZZ/101
(S,E,H)=setupRings(kk,n)
scan(#n,i->scan(n_i+1,j->x_(i,j)=S_(sum(i,k->n_k+1)+j)))
scan(#n,i->scan(n_i+1,j->e_(i,j)=E_(sum(i,k->n_k+1)+j)))

m=matrix{{x_(0,0),x_(1,0)},
       {x_(0,1),0},
       {0,x_(1,1)},
       {0,x_(1,2)}}
betti m
mE=symExt(m,E)          
n={1,2}
(S,E,H)=setupRings(ZZ/101,n)
time fB=dual res(coker transpose mE,LengthLimit=>12);	 	  
cohomologyTable(fB,H,{ -5,-5},{0,0})
cohomologyTable(fB,{ -5,-5},{0,0})
deg={ -5,-5}
m= corner(fB,deg);
--fBpartA=dual res( coker transpose m,LengthLimit=> 7)[-sum deg]

time fBpartB=res(ker m,LengthLimit=>18)[-sum deg-2]
--cohomologyTable(fB,H,deg-{1,1},{0,0})
--cohomologyTable(fBpartA,H,{ -5,-5},deg+{1,1})

F=fBpartB
betti F
apply(toList(min F..max F),k->tally degrees F_k)
cohomologyTable(F,H,deg-{2,2},deg+{10,10})
tateCut(F,(0,{0,0},{ -4,-4},{4,4}))
tateCut(F,(-1,{0,0},{ -4,-4},{4,4}))
tateCut(F,(-2,{0,0},{ -4,-4},{4,4}))
tateCut(F,(-3,{0,0},{ -4,-4},{4,4}))
tateCut(F,(1,{0,0},{ -4,-4},{4,4}))
tateCut(F,(2,{0,0},{ -4,-4},{4,4}))

tateCut(F,(1,{1,1},{ -4,-4},{4,4}))
tateCut(F,(2,{1,1},{ -4,-4},{4,4}))
tateCut(F,(3,{1,1},{ -4,-4},{4,4}))
quadrant(F,H,{1,1},{ -2,-2}),quadrant(F,H,{1,2},{ -2,-2}),quadrant(F,H,{1,3},{ -2,-2})
quadrant(F,H,{1,4},{ -2,-2}),quadrant(F,H,{1,5},{ -2,-2}),quadrant(F,H,{1,6},{ -2,-2})
quadrant(F,H,{1,4},{ -2,-2}),quadrant(F,H,{2,4},{ -2,-2}),quadrant(F,H,{3,4},{ -2,-2})
betti F
deg={0,0}
m=corner(F,deg); 
matrix apply(toList(0..4),i->apply(toList(0..6),j->hilbertFunction({i,j}+deg,ker m)))
quadrant(F,H,deg,{ -2,-2})	

deg={0,0}
m=corner(F,2,{1,1}); 
matrix apply(toList(-6..4),i->apply(toList(-6..6),j->hilbertFunction({i,j}+deg,ker m)))
betti F
quadrant(F,(4,{2,2},{ -2,-2}))
quadrant(F,(4,{3,2},{ -2,-2}))
quadrant(F,(4,{3,3},{ -2,-2}))
cohomologyTable(F,H,deg-{2,2},deg+{8,8})
quadrant(F,(4,{5,5},{ -3,-3}))
tateCut(F,(5,{3,3},{-3,-3},{7,7}))
tateCut(F,(6,{3,3},{-3,-3},{7,7}))	  
cohomologyTable(F,{5,5},{ -2,-2})
deg={2,3}
m=corner(F,deg); 
matrix apply(toList(0..4),i->apply(toList(0..6),j->hilbertFunction({i,j}+deg,ker m)))
quadrant(F,H,deg,{ -2,-2})	

restart
load "BGGonPnxPm.m2"           
n={2,2}
(S,E,H)=setupRings(ZZ/101,n)
scan(#n,i->scan(n_i+1,j->x_(i,j)=S_(sum(i,k->n_k+1)+j)))
scan(#n,i->scan(n_i+1,j->e_(i,j)=E_(sum(i,k->n_k+1)+j)))

m=matrix{{x_(0,0),x_(1,0)},
       {x_(0,1),0},
       {x_(0,2),x_(1,1)},
       {0,x_(1,2)}}
mE=symExt(m,E);
time fB=dual res(coker transpose mE,LengthLimit=>12);	 	  
cohomologyTable(fB,H,{ -5,-5},{0,0})
deg={ -2,-2}
m= corner(fB,deg);
fBpartA=dual res( coker transpose m,LengthLimit=> 7)[-sum deg]

fBpartB=res(ker m,LengthLimit=>18)[-sum deg-2]
cohomologyTable(fB,H,deg-{1,1},{0,0})
cohomologyTable(fBpartA,H,{ -5,-5},deg+{1,1})
cohomologyTable(fBpartB,H,deg,deg+{8,8})
F=fBpartB
quadrant(F,H,{1,1},{ -2,-2}),quadrant(F,H,{1,2},{ -2,-2}),quadrant(F,H,{1,3},{ -2,-2})
quadrant(F,H,{1,4},{ -2,-2}),quadrant(F,H,{1,5},{ -2,-2}),quadrant(F,H,{1,6},{ -2,-2})
quadrant(F,H,{1,4},{ -2,-2}),quadrant(F,H,{2,4},{ -2,-2}),quadrant(F,H,{3,4},{ -2,-2})
tateCut(F,(2,{1,1},{-2,-2},{6,6}))


restart
load("BGGonPnxPm.m2")
kk=ZZ/10007
n={1,2}
(S,E,H)=setupRings(kk,n)
scan(#n,i->scan(n_i+1,j->x_(i,j)=S_(sum(i,k->n_k+1)+j)))
scan(#n,i->scan(n_i+1,j->e_(i,j)=E_(sum(i,k->n_k+1)+j)))
degsource={1:{1,1},1:{1,2}}
degtarget={1:{0,0},2:{0,0}}
M=coker random(S^degsource,S^degtarget);
fM=res M
betti fM,apply(min fM..max fM-1,i->tally degrees fM_i)
degsfM=flatten apply(min fM..max fM-1,i->degrees fM_i)
M1=truncate(max degsfM,M)
fM1=res M1
betti fM1 ,apply(min fM1..max fM1-1,i->tally degrees fM1_i)

restart
load("BGGonPnxPm.m2")
kk=ZZ/10007
n={1,1,2}
(S,E,H)=setupRings(kk,n)
scan(#n,i->scan(n_i+1,j->x_(i,j)=S_(sum(i,k->n_k+1)+j)))
scan(#n,i->scan(n_i+1,j->e_(i,j)=E_(sum(i,k->n_k+1)+j)))
degsource={1:{1,1,1},1:{1,1,1}}
degtarget={1:{0,0,0},2:{0,0,-1}}
M=coker random(S^degsource,S^degtarget);
fM=res M
betti fM,apply(min fM..max fM-1,i->tally degrees fM_i)
degsfM=flatten apply(min fM..max fM-1,i->degrees fM_i)
M1=truncate(max degsfM,M);
time fM1=res M1
betti fM1 ,apply(min fM1..max fM1-1,i->tally degrees fM1_i)
betti fM1 ,max flatten apply(min fM1..max fM1-1,i-> degrees fM1_i)-min flatten apply(min fM1..max fM1-1,i-> degrees fM1_i) <= n
unique apply(toList(min fM1..max fM1-1),i-> (totdegs=unique apply(degrees fM1_i,deg->sum deg);#totdegs==1))
regSeq=ideal apply(unique degrees S,deg->random(deg,S))
m1=sub(presentation M1,vars S%regSeq);
betti res coker m1 == betti fM1
