--error in degrees set by transpose over the exterior alg
HashTable{VERSION => 0.8.54                   }
               architecture => i586
               compile node name => geometry
               compile time => Jul 13 1999 13:01:00
               compiler => gcc 2.91
               dumpdata => true
               factory => true
               factory version => 1.2c
               gc version => 4.14 alpha 1
               libfac version => 0.3.1
               mp => false
               operating system => Linux
               operating system release => 2.2.10
--Evaluate from here
symExt= (m,R) ->(
     ev := map(R,ring m,vars R);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
     n  := ev(q*jn))
--This seems ok in v.58. Previously we had the following extra lines:
--the code above does not produce a truly homogenous matrix; so use
--map(R^(rank target n),R^(apply(rank source n, i->-1)),n))
document {quote symExt,
     TT "symExt(m,R)", "--Takes a matrix m of linear
     --forms over a ring S, and returns a matrix of linear
     --forms over the ring R. If S and R are duals of 
     --one another, then symExt(m,R) is the adjoint of the 
     --of the multiplication map between degrees 0 and 1
     --of the module presented by m over S."}

kk=ZZ/32003
g=3
S=kk[x_1..x_g]
E=kk[x_1..x_g,SkewCommutative=>true]
use S
M=matrix{
     {0,x_1,0,0,x_3},
     {0,0,x_2,x_3,0},
     {0,0,0,x_1,0},
     {0,0,0,0,x_2},
     {0,0,0,0,0}}
M=matrix{{x_1}}
M=map(S^{rank target M:0},S^{rank source M:-1},M-transpose M)
isHomogeneous M
ME=symExt(M,E)
isHomogeneous ME
ME
betti ME

betti transpose ME --- gives an error!!

--But the following, which looks like the same matrix, is ok
use E
X=map(E^{0},E^{-1,-1},matrix{{x_3,x_2}})
betti X
isHomogeneous X
betti transpose X
