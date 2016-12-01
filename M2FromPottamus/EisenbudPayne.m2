needsPackage "Polyhedra"
prefixPath = {"/Users/david/src/M2/trunk/Macaulay2/packages"}|prefixPath
prefixPath
needsPackage ("ToricVectorBundles")--, AbsoluteLinks=>false)


cohoTable = (s1,s2,T) ->(
     T1 := T;
     d:={0,0,0,0};
  apply(toList s1,
       i -> apply(toList s2, 
	    j -> (d={i,0,j,0}; T1= twist(T,d); apply(3, i ->rank HH^i T1)))))

///
cohoTable(-3..3, -3..3, T)
///

deCoh = method() -- decomposed cohomology
deCoh(ToricVectorBundleKlyachko, ZZ,ZZ,ZZ) := (T,d,e,i) ->(
     --computes the d x e matrix whose (p,q) entry is the
     --dimension of the part of the  i-th coho module of 
     --weight congruent mod (d,e) to (p,q)
L := HH^i T;
c1 := map(ZZ^d,ZZ^e, 0);
c :=  mutableMatrix c1;
scan(degrees L,p-> c_((p_0)%d,(p_1)%e) = c_((p_0)%d,(p_1)%e)+1);
matrix c
)
deCoh(ToricVectorBundleKlyachko, ZZ,ZZ) := (T,d,e) ->(
     --lists the matrices produced by the other method of deCoh for all i
     for i from 0 to dim fan T list deCoh(T,d,e,i))

///
deCoh(T,3,3)
///

congCoh = method() --
congCoh(ZZ, ToricVectorBundleKlyachko, List) := (SIZE,T,W) ->(
-- Input (SIZE=ZZ, T= ToricVectorBundleKlyachko, W = {d,e,p,q}).
-- makes a list of lists of lists, where the innermost list
-- of the output is the list of dimensions of the isotypical components
-- of weight congruent to (p,q) mod (d,e) of the cohomology of
-- a twist in (-SIZE,-SIZE) to (SIZE,SIZE).
-- This is equal to the cohomology of the (p,q) factor of the (d,e)-pushforward of T.
--Thus it is the cohomology table of a bundle.
     D:={0,0,0,0};
     d:= W_0;
     e:=W_1;
     p:=W_2;
     q := W_3;
     T1:=T;
  apply(toList(-SIZE..SIZE),
       i -> apply(toList(-SIZE..SIZE),
	    j -> (D={d*i,0,e*j,0}; T1= twist(T,D); apply(deCoh(T1,d,e), m -> m_(p,q)))
	    )
       )
  )
///
cc=congCoh(2,T,{1,1,0,0})
netList cc
///
--test a coho table, in the form of a list of lists of lists, for naturality.
isNatural = L ->(
t := true;
scan(L, LL -> scan (LL, LLL -> if #positions(LLL,i-> i=!=0)>1 then (
	       t = false;
	       break)));
t)
congCohEuler = method() --
congCohEuler(ZZ, ToricVectorBundleKlyachko, List) := (SIZE,T,W) ->(
     L:=congCoh(SIZE, T, W);
     apply(L, LL ->(
	       apply(LL, LLL -> sum (apply(#LLL, i-> (-1)^i*LLL_i))))))

hyperbolaFrom3x3 = L ->(
     u := (L_1)_1;
     t := (L_1)_2-u;
     s := (L_2)_1 -u;
     r := (L_2)_2 -s-t-u;
     if (L_0)_0 =!= r-s-t+u then error("inconsistent");
     {r,s,t,u})
///
restart
load "EisenbudPayne.m2"
F=pp1ProductFan 2
T=cotangentBundle F
netList congCoh(1,T,{1,1,0,0})
netList oo
L2=congCohEuler (1,T,{1,1,0,0})
hyperbolaFrom3x3 L2

///
end


restart
viewHelp ToricVectorBundles
viewHelp Polyhedra

F=pp1ProductFan 2
rays F
T=cotangentBundle F
details T
HH^1 T
hh^1 T
L={matrix{{0,2},{1,3}},matrix{{0,5},{1,7}},matrix{{0,11},{1,13}},matrix{{0,17},{1,23}}}
T1=addBase(T,L)
details T1
L={matrix{{2,0}},matrix{{1,0}},matrix{{2,1}},matrix{{1,1}}}
T1=addFiltration(T1,L)
details T1
apply(3, i -> HH^i T1)
apply(3, i -> HH^i T)
L={matrix{{2,0}},matrix{{1,0}},matrix{{3,1}},matrix{{4,1}}}
T1=addFiltration(T1,L)
apply(3, i -> HH^i T1)
details T1
details T

HH^1 T
HH^2 T

L={matrix{{2,1}},matrix{{2,1}},matrix{{1,0}},matrix{{1,0}}}
T1=addFiltration(T,L)
details T1
apply(3, i -> HH^i T1)

details T
L={matrix{{0,5},{1,7}},matrix{{0,1},{-1,0}},matrix{{-1,2},{0,3}},matrix{{1,0},{0,1}}}
T2=addBase(T,L)
details T2
apply(3, i -> HH^i T2)
rays T
d={1,0,2,0}
T3=twist(T,d)
details T3
----------------------------------------------------------------------------------------------------------------
-- THE NEXT LINE GIVES YOU THE TABLE FOR ALL THE TWISTS
----------------------------------------------------------------------------------------------------------------


isNatural cc
cc=congCoh(2,T,{1,1,0,0})
netList cc
isNatural cc

deCoh(twist(T, {2,0,0,0}),2,2)


T1=randomDeformation (T,-10,10)
details T1
cohoTable(-3..3, -3..3, T1)
details (T2=symmProd(2,T))
T3=randomDeformation(T2,-10,10)


HH^1 twist(T, {1,0,0,0})
netList L
T4=symmProd(2,T2)
L=apply(toList(-5..5), i -> apply(toList(-5..5), j -> (d:={i,0,j,0}; T1:= twist(T4,d); apply(3, i -> HH^i T1))))
netList L


