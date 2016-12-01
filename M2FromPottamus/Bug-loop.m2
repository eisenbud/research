restart
version
purePowers=(d,S)->for t from 0 to numgens S - 1 list (S_t)^d
impure=(d,S)->(
     c:=compress(basis(d,S)%map(S^1,S^{numgens S:-d}, matrix{purePowers(d,S)}));
     for i from 0 to rank source c -1 list c_(0,i))
randomBinomialPrimaryIdeal=(d,S,g)->(
     --numgens+g generators; the first chosen with a pure power as half.
     kk=coefficientRing S;
     P:=purePowers(d,S);
     Q:=impure(d,S);
     m:=length Q;
     L:=for t from 0 to numgens S-1 list P_t-(random kk)*Q_(random (m-1));
     L1:=for t from 1 to g list Q_(random (m-1))-(random kk)*Q_(random (m-1));
     ideal mingens ideal(L|L1))
kk=ZZ/101
S=kk[x,y,z]
i=randomBinomialPrimaryIdeal(3,S,4)
