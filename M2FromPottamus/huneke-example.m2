S=kk[a..h]
i=ideal(a^3, b^3, c^3, d^3, e^3, f^3, g^3, h^3,
        a*b*c-a*b*d, c*d*e-c*d*f, e*f*g-e*f*h, a*g*h-b*g*h)
betti (F=res i)
betti (G=res (i^2))
betti F
j=trim((ideal vars S)^6*i);
res(j, LengthLimit=>4)
FF=oo
betti FF


i17 : betti F

             0  1  2   3   4   5   6   7  8
o17 = total: 1 12 70 252 586 816 648 272 47
          0: 1  .  .   .   .   .   .   .  .
          1: .  .  .   .   .   .   .   .  .
          2: . 12  .   .   .   .   .   .  .
          3: .  . 12   .   .   .   .   .  .
          4: .  . 58  24   .   .   .   .  .
          5: .  .  .  96  36   .   .   .  .
          6: .  .  . 132 198  56   .   .  .
          7: .  .  .   . 236 296  84   .  .
          8: .  .  .   . 116 408 422 156 17
          9: .  .  .   .   .  56 140 112 28
         10: .  .  .   .   .   .   2   4  2

o17 : BettiTally
i20 : betti (G=res (i^2))

             0  1   2    3    4    5    6    7   8
o20 = total: 1 78 657 2799 6750 9230 7085 2858 472
          0: 1  .   .    .    .    .    .    .   .
          1: .  .   .    .    .    .    .    .   .
          2: .  .   .    .    .    .    .    .   .
          3: .  .   .    .    .    .    .    .   .
          4: .  .   .    .    .    .    .    .   .
          5: . 78   .    .    .    .    .    .   .
          6: .  . 148    8    .    .    .    .   .
          7: .  . 496  430   84    4    .    .   .
          8: .  .  12 1120  764  128    4    .   .
          9: .  .   . 1177 2904 1780  332   12   .
         10: .  .   1   64 2502 4980 3441  996 108
         11: .  .   .    .  496 2118 2712 1326 216
         12: .  .   .    .    .  220  588  508 140
         13: .  .   .    .    .    .    8   16   8