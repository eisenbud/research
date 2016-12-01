carpet=(kk,a,b)->(
     R:=kk[x_0..x_a,y_0..y_b];
     A:=transpose matrix apply(a,i->{x_i,x_(i+1)});
     B:=transpose matrix apply(b,i->{y_i,y_(i+1)});
     I:=minors(2,A)+minors(2,B);
     J:=ideal flatten apply(a-1,i->apply(b-1,j->det(A_{i,i+1}+B_{j,j+1})));
     IJ:=ideal mingens (I+J);
     IJr:=minors(2,A|B);
     (R,A,B,IJ,IJr))

truncate(ChainComplex,ZZ):=(C,t)->(
     l:=length C;
     Ct:=new ChainComplex;
     Ct.ring = C.ring;
     scan(l+2-t,j->(Ct#j=C#(j+t)));
     scan(l-t,j->Ct.dd#(j+1)=C.dd#(j+1+t));
     Ct)

end
viewHelp extend
restart

load "100620 K3 carpet Schreyer.m2"
kk=ZZ/101
L=carpet(kk,3,3);
R = L_0

I=L_3 -- ideal of K3
J=L_4 -- ideal of scroll
betti res J
betti res I
A=L_1
B=L_2
yy=ideal mingens ideal flatten B
C = trim (I+ideal(R_3+R_7))
betti res C

SX = R/I
CX = sub(C,SX)
M=prune ((module (ideal(SX_0,SX_1)+CX))/module CX)
phi = presentation M

E = prune image phi
fitt = minors(3,presentation E);
codim fitt

dim SX

I1=ideal(gens I*syz contract(transpose gens yy^2,gens I));
betti (fI1=res  I1)
codim I1
aut=(vars R)_{4..7}|(vars R)_{0..3} 
I2=substitute(I1,aut)
betti (fI2=res I2)
betti (fI=res (I1+I2))
E1=extend(fI,fI1,matrix{{1_R}})
E2=
fJ=res J
betti(D=Hom(fJ,R^{-9})[-6])
C=truncate(fJ,1)


betti D
E=extend(D,C,map(D#0,C#0,hom0));
E#1
apply(length D,j->betti(E#j))
apply(length C,i->
     tally apply(rank C#i,j->betti trim ideal transpose(C.dd_i_{j})))


