--goal: construct shellable complexes at random

testNewSimplex = method()
testNewSimplex(List, List) := (P, D) ->(
--given a pure, d-dimensional simplicial complex (sc) as a list of ordered lists of d+1 vertices in [n], and
--a simplex D as such a list, tests whether the intersection of D with P is a union of facets of D.
d := #D-1; --dimension
ints := apply(P, D' -> intersectLists(D',D));
facets := unique select(ints, E -> #E==d);
if facets == {} then return false;
smalls := unique select(ints, E -> #E<d);
t := true;
scan(smalls, e ->scan(facets, E -> if #(e-set E) =!= 0 then t = false));
--error();
(t,smalls,facets)
)

intersectLists = (D',D) -> D - set(D-set D')

randomAddition = (n,P) ->(
    --P must be non-empty
    deg := #P;
    d = #P_0 - 1;
    t = false;
    D' = {null};
    while t do (
    	r = random deg;
    	i := random n;
    	     while member(i, P_r) do i = random n;
    	j := random d+1;
    	D := P_r;
    	D' = D -{set D_j} | {i};
    	t = testNewSimplex(P,D'));
    P|D')


///
restart
load "shelling.m2"
P = {{1,2,3},{1,2,4},{1,2,4},{1,3,4},{5,6,7}}
D = {1,3,4}
D' = {3,4,5}
testNewSimplex(P,D)
testNewSimplex(P,D')
randomAddition(5,P)
///

end
viewHelp

restart
uninstallPackage "RandomIdeal"
installPackage "RandomIdeal"

