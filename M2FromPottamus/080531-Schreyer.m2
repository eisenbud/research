restart
kk=ZZ/101
k=2
R=kk[a_(0,0)..a_(k,k-1), b_(0,0)..b_(k,k-1)]
A=genericMatrix(R,a_(0,0),k+1,k)
B=genericMatrix(R,b_(0,0),k+1,k)
M=A*(transpose B)
i=trim ideal(M+transpose M)

--time (P=primaryDecomposition i) -- 1672 seconds
o9 = Tally{(7, 96, total: 1 64 387 1040 1562 1431 826 297 62 6) => 1}
                       0: 1  .   .    .    .    .   .   .  . .
                       1: .  6   .    .    .    .   .   .  . .
                       2: .  .  15    .    .    .   .   .  . .
                       3: . 20  96  200  160   51   .   .  . .
                       4: . 24 172  504  786  680 322  72  6 .
                       5: . 14 104  336  616  700 504 225 56 6
                         0  1  2  3  4 5
           (5, 6, total: 1 15 40 45 24 5) => 2
                      0: 1  .  .  .  . .
                      1: . 15 40 45 24 5

o9 : Tally


--betti res i
irrA = ideal A
irrB= ideal B
time betti(iA=i:irrA)
time (P=decompose i) -- 90 seconds; gives two primes, both scrolls.

tally(apply(P, c->(codim c, degree c, betti res c)))
           (5, 6, total: 1 15 40 45 24 5) => 2
                      0: 1  .  .  .  . .
                      1: . 15 40 45 24 5

i9 : tally(apply(P, c->(codim c, degree c, betti res c)))

                          0  1   2    3    4    5   6   7  8 9
P_1 
P_0
radi=trim (intersect(P_1,P_0)) 
(gens (radi^2))%i
ti=top i
ti == radi
iemb=i:radi
iemb == top iemb
--true

---The following code exhibits problems with the primary decomp routines.
viewHelp primaryDecomposition

primaryDecomposition(i)
--returns an error "missed components"
primaryDecomposition(i, Strategy => Hybrid)
--does nothing
primaryDecomposition(i, Strategy => EisenbudHunekeVasconcelos)
--doesn't finish


