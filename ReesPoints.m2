needsPackage "Points"
needsPackage "ReesAlgebra"


reesPoints = n->(
po = randomPoints(2,n);
(po,reesIdeal po)
)
statistics = n->(
    m:= 2;
    while binomial(m,2)<= n do m = m+1;
    m = m-1;
    s := n-binomial(m,2);
    t := m-s-1;
    po := randomPoints(2,n);
    B := betti res po;
    Irees := reesIdeal po;
    S = ring Irees;
    (R,RS) = flattenRing S;
    IR = RS Irees;
    Brees = betti (F = res IR);
    dep = 1+max(s,t)+3 - pdim coker gens IR;
    (n, s,t,dep,B,IR_*/degree))
///
n = 17
statistics 11

///
end--
restart
load "ReesPoints.m2"
(po,I) = reesPoints 17;
betti res po
S = ring I
(R,RS) = flattenRing S
IR = RS I;
I_*/degree
netList(I_*)
betti (F = res IR)
kk = coefficientRing ring IR
R1 = kk[W_0..W_3,X_0..X_2, Degrees =>flatten {4:{1,0},3:{0,1}}]
fl = map(R1,R,{W_0..W_3,X_0..X_2})
isHomogeneous fl IR
IR_*/degree
minimalBetti fl IR
F1 = fl F
betti fl(F)
--
for n from 23 to 24 do--21+94 seconds
time print statistics n
--for 23:
netList{{1, 7}, {1, 7}, {1, 8}, {1, 8}, {3, 19}, {3, 19}, {3, 19}, {4, 25}, {4, 25}, {4, 25}, {4, 25}, {5, 30}, {5, 30}, {5, 30}, {6, 36}, {6, 36}, {6, 36}, {6, 36}, {8, 48}, {8, 48}, {8, 48}, {8, 48}, {8, 48}}
--for 24:
netList {{1, 8}, {1, 8}, {1, 8}, {3, 20}, {3, 20}, {3, 20}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {6, 37}, {12, 72}}
