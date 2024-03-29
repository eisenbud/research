restart
kk=ZZ/32003

R1=kk[x,y,z,t_1,t_2]/(ideal(x^2+y^2, y^2+z^2, x^3, z^3))
f=map(R1^2,R1^{-1,-1},matrix{{x,y},{y,z}})
R2=kk[x,y,z,s_1,s_2]
use R1
h=map(R1^1,R1^{3:-1},matrix{{x,y,z}})
g=map(R1,R2,h|((matrix{{t_1,t_2}})*f))
show ker g
ff=res(coker f, LengthLimit=>2)
fff=res (coker transpose ff.dd_2, LengthLimit=>2)
uf=transpose (fff.dd_2)
R1u=kk[x,y,z,t_1..t_4]/(ideal(x^2+y^2, y^2+z^2, x^3, z^3))
fu=map(R1u^2,R1u^{-1,-1},matrix{{x,y},{y,z}})
ffu=res(coker fu, LengthLimit=>2)
fffu=res (coker transpose ffu.dd_2, LengthLimit=>2)
uf=transpose (fffu.dd_2)
h=map(R1u^1,R1u^{3:-1},matrix{{x,y,z}})
uf
h|matrix{{t_1,t_2,t_3,t_4}}*uf
h
g=map(R1u,R2,h|matrix{{t_1,t_2,t_3,t_4}}*uf)
matrix{{x,y,z,t_1,t_2,0,0}}
use R1
specialize=map(R1,R1u,matrix{{x,y,z,t_1,t_2,0_R1,0_R1}})
g2=(specialize*g)
I=ker g
I2=ker g2
betti mingens I
betti mingens I2
---------------------------
restart

--Takes an ideal I in a polynomial ring R, and a matrix f over R,
--and returns the definining ideal (in a new polynomial ring)
--of the Rees ring of the image of f, regarded as a matrix over R/I.

symmetricKernel=(I,f)->(
     R:=ring I;
     nvars:=rank source vars R;
     mtar:=-(min flatten degrees target f)+1;
     msource:=-(min flatten degrees source f)+1;
     deglist:=degrees source vars R | degrees target (f**R^{-mtar});
     Rtar:=kk[vars(100..100+nvars+rank target f-1),Degrees=>deglist];
     ;
     deglist=degrees source vars R | degrees source (f**R^{-msource});
     Rsource:=kk[vars(100..100+nvars+ rank source f-1),Degrees=>deglist];
     ;
     RtoRtar := map(Rtar, R, (vars Rtar)_{0..(rank source vars R)-1});
     nR:=rank source vars R;
     ntarf:=rank target f;
     Itar:= RtoRtar I;
     Rtar=Rtar/Itar;
     ;
     oldvars:=(vars Rtar)_{0..(rank source vars R)-1};
     g:=oldvars|((vars Rtar)_{nR..(nR+ntarf-1)})*(RtoRtar f);
     ;
     ideal mingens ker map(Rtar, Rsource, g)
     )

R=kk[x,y,z]
I=ideal(x^2+y^2, y^2+z^2, x^3, z^3)
f=map(R^{0,1},R^{-1,0},matrix{{x,0},{z^2,y}})
show symmetricKernel(I,f)

--the following takes an ideal I in a polynomial ring R
--and a matrix f over R
--and returns the universal embedding of image (f ** R/I),
--written as a matrix over R

universalEmbedding=(I,f)->(
     R:=ring f;
     Rbar=R/I;
     fbar:=substitute(f, Rbar);
     fres:=res(image fbar, LengthLimit=>2);
     ftres:=res(image transpose fres.dd_1, LengthLimit=>2);
     fnew:=transpose ftres.dd_1;
     fbartot:=fbar||fnew;
     substitute(fbartot, R)
     )

fu=universalEmbedding(I,f)
betti symmetricKernel(I,fu)
betti symmetricKernel(I,f)
--same

--------------
R=kk[x,y,z]
I=ideal(x^2+y^2, y^2+z^2, x^3, z^3)
f=map(R^2,R^{-1,-1},matrix{{x,y},{y,z}})
fu=universalEmbedding(I,f)
show symmetricKernel(I,fu)
show symmetricKernel(I,f)
--same
--------------------
RI=R/I
J=ideal(x,y)
fI=presentation module J
f=substitute(fI,R)
fu=universalEmbedding(I,f)
show symmetricKernel(I,fu)
show symmetricKernel(I,f)
--same


--------------
R=kk[x,y,z]
I=ideal(x^3+y^3, y^2+z^2, x^5, z^5,y^5)
f=map(R^2,R^{-1,-1},matrix{{x,y},{y,z}})
fu=universalEmbedding(I,f)
show symmetricKernel(I,fu)
show symmetricKernel(I,f)
--same
--------------------
R=kk[x]
I=ideal(x^5)
f=map(R^1,R^{-1},matrix{{x}})
fu=universalEmbedding(I,f)
show symmetricKernel(I,fu)
show symmetricKernel(I,f)
--5th power of the maximal ideal in k[x,y]
--same
--------------------
--a universal example 
R=kk[x,y,u,v]
I=ideal(x^2+x*y+y^2, 2*x*u+x*v+y*u+2*y*v, u^2+u*v+v^2)
f=map(R^2,R^{-1,-1},matrix{{x,u},{y,v}})
fu=universalEmbedding(I,f)
show symmetricKernel(I,fu)
show symmetricKernel(I,f)

--
--revised universal example 
R=kk[x,y,u,v]
--I=ideal(x^2+x*y+y^2, 2*x*u+x*v+y*u+2*y*v, u^2+u*v+v^2)
I=ideal(x^2,x*y,y^2,x*u,x*v+y*u,y*v,u^2,u*v,v^2)
f=map(R^2,R^{-1,-1},matrix{{x,u},{y,v}})
fu=universalEmbedding(I,f)
betti (Ju=symmetricKernel(I,fu))
betti (J=symmetricKernel(I,f))

--second revised universal example 
R=kk[a,b,c,x,y,u,v]
--I=ideal(x^2+x*y+y^2, 2*x*u+x*v+y*u+2*y*v, u^2+u*v+v^2)
--I=ideal(x^2,x*y,y^2,x*u,x*v+y*u,y*v,u^2,u*v,v^2)
I=ideal(a*x^2+b*x*y+c*y^2, 2*a*x*u+b*x*v+b*y*u+2*c*y*v, a*u^2+b*u*v+c*v^2)
f=map(R^2,R^{-1,-1},matrix{{x,u},{y,v}})
fu=universalEmbedding(I,f)
betti (Ju=symmetricKernel(I,fu))
betti (J=symmetricKernel(I,f))

