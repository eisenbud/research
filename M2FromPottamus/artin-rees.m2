document{quote artinRees1,
     TT"artinRees(inclusion-map)",PARA,
"Given a map of graded modules f: S--> M over a ring R,
the program outputs the smallest integer q
such that 
m^{n-q}(S\cap m^qM)=S\cap m^nM 
for all large n.
The idea is to form the ring R''=R[y,t]/(yt-x):t^\infty,
and to take the largest degree in y of a generator of
the kernel of M''-->>(M/S)'', where 
X' denotes (R''\otimes X)/(t-torsion).
Note that we can actualy compute the same thing by setting
R' = R[y,t]/(yt-x) and
X'= (R' \otimes X)/(t-torsion). It's not clear which
is better!
     --IN THIS VERSION WE ASSUME THAT
     --R is a graded ring with gens in degree 1
     --   (and thus R'=R[y,t]/saturate(yt-x,t) is obtained
     --   by substituting y for x in the homogeneous equations of R),
     --AND THAT
     --f is a map of free modules 
     --   (so that the target of f**R' has no t-torsion).
     "}

artinRees1= f ->(
     --IN THIS VERSION WE ASSUME THAT
     --R is a graded ring with gens in degree 1
     --   (and thus R'=R[y,t]/saturate(yt-x,t) is obtained
     --   by substituting y for x in the homogeneous equations of R),
     --AND THAT
     --f is a map of free modules 
     --   (so that the target of f**R' has no t-torsion).
     --
     --
     --Form the ring R'=R[y,t]/saturate(yt-x, t)
     --where x are the variables of 
     --R=ring f. Note that R' is the
     --extended Artin-Rees algebra R[t,t^{-1}m], where
     --m=ideal vars R.
     --
     R:= ring f;
     n:= numgens R;
     I:= ideal presentation R;
     kk:= coefficientRing R;
     R0':=kk[y_0..y_(n-1),t, Degrees=>{n:{1,1},{1,-1}}];
     I0'=substitute(I, (vars R0')_{0..n-1});
     R':= R0'/I0';
     --a map to substitute yt for x;
     --the effect is to tensor with R' over R.
     use R';
     armap:= map(R',R,(t*vars R')_{0..n-1});
     --the following function adjusts degrees to keep
     --things homogeneous when we substitute yt for x
     chDegs=L->apply(L,i->{2*i_0,0});
     --Now fetch f to R'
     f'=map(R'^(-chDegs degrees target f),
             R'^(-chDegs degrees source f), 
             armap f);
     L=degrees source mingens saturate(image f',t);
     --return the maximal degree in y of a generator of the quotient:
     max apply(L, i->i_1)
     )


TEST ///
restart
load "artin-rees.m2"
help artinRees1
S=kk[a]
p=7
f=map(S^1,S^{-p},a^p)
artinRees1 f
--gives p as it should!

--------------------------------
R0=kk[x_0..x_3]
I0=ideal(x_0*x_1-x_2*x_3)
R=R0/I0

d=10
FF=res (coker vars R, LengthLimit=>d)
f=FF.dd_d
artinRees1 f
--answer 1 (for d=1..10) 
--is probably correct for the res of the max ideal

--------------------------------
restart
load "artin-rees.m2"

R0=kk[x_0..x_4]
I0=ideal(x_0,x_1)*ideal(x_2,x_3)
R=R0/I0
J=(vars R)_{0..3}
J2=gens (ideal J)^2
d=1
FF=res (coker J, LengthLimit=>d)
f=FF.dd_d
artinRees1 f
--seems always to be 1! also, when we replace J by J^2,
--the number seems to be 2 for the first map, then 1 
--thereafter!
--------------------------------
restart
load "artin-rees.m2"

R0=kk[x_0..x_2]
I0=(ideal(vars R0))^4
R=R0/I0
J=matrix{{x_0^2}}

d=6
FF=res (coker J, LengthLimit=>d)
f=FF.dd_d;
artinRees1 f
--answers for d=1..6:  2,2,2,3,3,3
///

