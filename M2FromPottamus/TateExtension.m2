ringData = method()
ringData Ring := E ->(
differentDegrees = unique last degrees vars E;
varsLists := apply(differentDegrees, deg -> select (gens E, x-> degree x == deg));
t := #varsLists;
maxList := apply(varsLists, L -> ideal(L));
v := varsLists/(L->#L);
n := apply(v, i-> i-1);
(t,v,n,varsLists,maxList)
)
ringData Module := M -> ringData ring M

///
v = {2,3}
E = kk[e_0..e_1, f_0..f_2, Degrees => {v_0:{1,0},v_1:{0,1}}, SkewCommutative => true]
ringData E
///

inWindow = method()
inWindow(List,List) := (D,n) -> 
    #D == #select(#D, i->(0<=D_i and D_i<=n_i))

inWindow(ChainComplex) := W -> (
    (t,v,n,varsList,maxList) := ringData ring W;
    L:=flatten apply(toList(trueMin W.. trueMax W),d-> degrees W_d);
    #select(L, D-> not inWindow(D,n))==0)    

{*aboveWindow = method()
aboveWindow(List,List) := (D,n) -> #D == #select(#D, i-> D_i>n_i)

gensInWindow = method()
gensInWindow(Module) := M ->(
    rd = ringData ring M; 
    #D == #select(#D, i->(0<=D_i and D_i<=n_i)))
*}
///
n = {3,5,4}
D = { -1,4,3}
inWindow (D,n)
aboveWindow (D,n)
///

powers = (D,mL) -> (
m1 := directSum apply(#D, i -> gens trim((mL_i)^(D_i)));
m2 := matrix{toList(#D:1_(ring m1))};
m2*m1)

pushAboveWindow = method()
pushAboveWindow Module := M -> (
    E:= ring M;
(t,v,n,varsLists,maxList) := ringData E;
g := gens M;
degList := last degrees g;
if degList == {} then return M;
directSum apply(degList, D->if inWindow(D,n) 
    then powers(v-D,maxList)**E^{ -D} else id_(E^{ -D}))
)
///
(S,E)=setupRings(ZZ/101,{1,2})
pushAboveWindow(E^{{0,0},-{ -1,0},-{1,2},-{1,3}})
///


pushAboveWindow Matrix := A ->(
    if A==0 then return A;
    mingens image (A*pushAboveWindow source A)
    )

///
(S,E)=setupRings(ZZ/101,{1,2})
A=matrix{{E_0,E_2}}
pushAboveWindow A
///

pushAboveWindow(Matrix,Matrix) := (A,B) ->(
    assert(A*B == 0);
    C := pushAboveWindow syz A;
    mingens image(C % image B)
    )

pushAboveWindow(Matrix,Matrix,Matrix) := (A,B,C) ->(
    B2 := pushAboveWindow(A,B);
    assert((B|B2)*(C||map(source B2, source C, 0))== 0);
    assert(A*(B|B2) == 0);
    (B|B2, C||map(source B2, source C, 0))

)

pushAboveWindow List := L ->(
    --L = List of matrices that make a complex
    len = #L;
    if len == 1 then return append(L,pushAboveWindow syz L_0);
    if len == 2 then return {L_0, L_1|pushAboveWindow(L_0,L_1)};
    BC := null;
    A := L_0; B := L_1; C:= L_2;
    L':= {A};
    i := 2;
    while(   --<<i<<endl;flush;
    	BC = pushAboveWindow (A,B,C);
    	L' = append(L', BC_0);
    	A = BC_0;
    	B = BC_1;
    	assert(source A == target B);
    	i<len-1)
    do(
     	i = i+1;
     	C = L_i;
     	assert(source B == target C)
       );
   append(L',B)
    )

pushAboveWindow ChainComplex := C -> (
    C':=appendZeroMap appendZeroMap prependZeroMap C;
    L := chainComplexData C';
    M := pushAboveWindow L_2;
    chainComplexFromData(min C', M)
    )
///
restart
load "TateOnProducts.m2"
load "TateExtension.m2"

n = {1,2}
(S,E) = setupRings(ZZ/101,n)


A = map(E^1, E^{{0,-1}} ,matrix{{E_0}})
A0 = map(E^0, target A, 0)
betti (C=res coker A)
C1 = prependZeroMap C
D = pushAboveWindow C1
cohomologyTable (C1, -{3,3}, {10,10})
cohomologyTable(D, -{3,3}, {10,10})
tallyDegrees D

apply(degrees(E^0), deg->sum deg -3)
///

chainComplexData = C->(
    minC := min C;
    maxC := max C;
    {minC, maxC, apply(toList(1..maxC-minC), i-> (C[minC]).dd_i)}
)
chainComplexFromData = method()
chainComplexFromData List := L ->(
    --format of L is desired min, desired max, list of 
    --shifted maps
    C := chainComplex L_2;
    assert( min C == 0);
    C[-L_0])

chainComplexFromData(ZZ, List) := (minC,L) ->(
    --minC will become the min of the output complex
    C := chainComplex L;
    assert( min C ==0);
    C[-minC])

prependZeroMap= method()
prependZeroMap ChainComplex := C->(
    L := chainComplexData(C[-1]);
    minC := L_0;
    newd := map((ring C)^0, target L_2_0, 0);
    (chainComplexFromData(minC-1,prepend(newd,L_2)))[1]
    )
    
appendZeroMap= method()
appendZeroMap ChainComplex := C->(
    L := chainComplexData(C);
    minC := L_0;
    newd := map(source last L_2,(ring C)^0, 0);
    chainComplexFromData(minC,append(L_2,newd))
    )    
    
    
///
(S,E)=setupRings(ZZ/101,{1,1})


///
trueMin = method()
trueMin(ChainComplex) := C -> (
    assert( not C==0); 
    m:= min C;
    while C_(m+1)==0 do (m=m+1);
    m)


trueMax = method()
trueMax(ChainComplex) := C -> (
    assert( not C==0); 
    m:= max C;
    while C_m==0 do (m=m-1);
    m)
///
symbol tt
R=ZZ[tt]
C=chainComplex {matrix{{R_0}}}
C1=appendZeroMap prependZeroMap C
trueMax C1,max C1
trueMin C1, min C1
///

removeZeroTrailingTerms = method()
removeZeroTrailingTerms(ChainComplex) := W -> (
    E := ring W;
    mi := trueMin W;
    ma := trueMax W;
    W' := W[mi];
    if mi==ma then (return (chainComplex({map(E^0,W'_0,0),map(W'_0,E^0,0)}))[-mi+1]) else
    (chainComplex apply(toList(1..ma-mi),i->W'.dd_i))[-mi]
    )

///
R=ZZ[tt]
C=chainComplex {matrix{{R_0}}}
C1=appendZeroMap prependZeroMap C
removeZeroTrailingTerms C1
///

minimize = method();
minimize ChainComplex := ChainComplex => C -> (
  complete C;
  lower := trueMin C;
  upper := trueMax C;
  if not all(lower..upper, i -> isFreeModule C_i)
  then error "expected a chain complex of free modules";
  rows := new MutableHashTable; -- row indices in each differential to keep  
  D := new MutableHashTable;    -- differentials 
  E := new MutableHashTable;    -- free modules 
  for i from lower to upper do (
    rows#i = set(0.. rank C_i - 1);
    D#i = mutableMatrix C.dd_i;
    E#i = {});
  for i from lower + 1 to upper do (
    k := 0;  -- column index in i-th differential
    while k < rank C_i do (
      j := 0;  -- row index in i-th differential
      for j in toList rows#(i-1) do (
a := (D#i)_(j,k);
if isUnit a then (
 rows#(i-1) = rows#(i-1) - set{j};
 rows#i = rows#i - set{k};
 for ell in toList rows#(i-1) do (
   b := (D#i)_(ell,k);
   D#i = rowAdd(D#i, ell, -b*a^(-1), j);
   D#(i-1) = columnAdd(D#(i-1), j, b*a^(-1), ell));
 break));
      k = k+1));
  for i from lower to upper do rows#i = toList rows#i;
  E#lower = target submatrix(C.dd_(lower+1), rows#lower, rows#(lower+1));
  for i from lower+1 to upper do (
    E#i = source submatrix(C.dd_i, rows#(i-1), rows#i));
  (chainComplex for i from lower + 1 to upper list (
    (-1)^lower * map(E#(i-1), E#i, submatrix(matrix D#i, rows#(i-1), 
rows#i))))[-lower])






sloppyTateExtension=method()
sloppyTateExtension(ChainComplex) := W -> (
    -- input W : a Beilinson representative of an object in D^b(PP)
    -- output :  an Tate extension in a bounded range
    -- compute the TateExtension in a sloppy way: the Beilinson window of the extension is only
    -- isomorphic, bat not equal W.
    (t,v,n,maxList,idealList) := ringData ring W;
    if not inWindow W then error "expect a complex with terms only in the Beilinson window";
    W1 := removeZeroTrailingTerms W;
    -- W1:= W;    
    TW1:=pushAboveWindow W1;    
    ma:= trueMax TW1; mi:=trueMin TW1; 
    --betti W1,betti TW1
--Bbounds given for the length of the resolution have to be discussed 
--They should come out of the proof of the theorem !!     
    TW1e := res(coker TW1.dd_(ma),LengthLimit=>(3*sum v))[-ma];
    --betti TW1e
    TW1c := cornerComplex(TW1e,2*v);
    --betti TWc
    TW2 := dual res(coker transpose TW1c.dd_(ma+sum v),LengthLimit =>(ma+3*sum v -mi))[-ma-sum v+1];
    --betti TW2
    TW2
    )
///
--Example 1 setup
time T=sloppyTateExtension W
cohomologyTable(T,-{5,5},{5,5})
cohomologyTable(C2,-{5,5},{5,5})
///

end--

restart
loadPackage("TateOnProducts",Reload=>true)
--load "TateExtension.m2"

--Example 1: vector bundle on P^1xP^2 and  cohomology table
--o61 = | 78h  38h  12h 0 2k 18k 48k 92k |
--      | 57h  28h  9h  0 k  12k 33k 64k |
--      | 36h  18h  6h  0 0  6k  18k 36k |
--      | 15h  8h   3h  0 1  0   3k  8k  |
--      | 6h2  2h2  0   0 2  6   12  20  |
--      | 27h2 12h2 3h2 0 3  12  27  48  |
--      | 48h2 22h2 6h2 0 4  18  42  76  |
--      | 69h2 32h2 9h2 0 5  24  57  104 |
-- and Beilinson monad
--o64 = | 0 0  0 0 0 |
--      | 0 3h 0 1 0 |
--      | 0 0  0 2 0 |
--      | 0 0  0 0 0 |
n = {1,2}
t = #n
(S,E)=setupRings(ZZ/101,n)

I=prune (ideal vars E)^2
betti (fI=res(I,LengthLimit=>10))
betti (C= dual fI)
cohomologyTable(C,-{5,5},{5,5})
C1=lastQuadrantComplex(C,{3,3})
cohomologyTable(C1,-{5,5},{5,5})
betti(C2 = (res (coker C1.dd_(-4),LengthLimit=>11))[5])
cohomologyTable(C2,-{4,4},{4,4})
time W=beilinsonWindow (C2);  -- used 14.4797 seconds
W
removeZeroTrailingTerms W

time T=sloppyTateExtension W
cohomologyTable(T,-{5,5},{5,5})
cohomologyTable(C2,-{5,5},{5,5})

--Example 2 a real complex ?
n={1,2}
(S,E)=setupRings(ZZ/101,n)
betti (fE= res(ideal vars E,LengthLimit=>8))

A=transpose mingens truncateInE({1,0},image transpose fE.dd_1)
C=chainComplex {A,fE.dd_2,fE.dd_3,map(source fE.dd_3,E^0,0) }**E^{{ 0,0}}[1]
isChainComplex C
betti C, betti dual C
Cdual= dual C ** E^{{0,0}-n}[-sum n+1]
betti Cdual
W=beilinsonWindow C, betti W
T=sloppyTateExtension(W)
cohomologyTable(T,-{3,3},{3,3})
Wdual=beilinsonWindow Cdual
cohomologyTable(Wdual,-{1,1},n)
cohomologyTable(W,-{1,1},n)
Tdual=sloppyTateExtension Wdual
dualTdual= dual Tdual ** E^{ -n}[-sum n +1]
cohomologyTable(dualTdual,-{3,3},{3,3}),cohomologyTable(T,-{3,3},{3,3})


-- to see the corners in both cases look at the following output
cohomologyTable(dualTdual,-{3,3},{6,6})
cohomologyTable(T,-{6,6},{3,3})
betti T
betti dualTdual

--Example 3 U^a 's


time netList cornerCohomologyTablesOfUas({2,2})


-- Example from introduction

n={1,1}
(S,E)=setupRings(ZZ/101,n)
W=(chainComplex {map(E^0,E^1,0),map(E^1,E^0,0)})[1]
time T=sloppyTateExtension W;
cohomologyTable(T,-{3,3},{3,3})
betti T
W=beilinsonWindow T
a={2,-3}
W2=removeZeroTrailingTerms beilinsonWindow (T**E^{a}[sum a])
cohomologyTable(W2,-{2,2},{2,2})
cohomologyTable(W,-{2,2},{2,2})


