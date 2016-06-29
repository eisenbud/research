restart
needsPackage "MCMApproximations"
needsPackage "CompleteIntersectionResolutions"
n= 3;d=3;
S := ZZ/101[x_0..x_(n-1)]
ff = matrix{apply(n, i->(S_i)^d)}
R = setupRings  ff
use R_n
M = syzygyModule(3,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}})
(MM,kk,p) = setupModules(R,M);
apply(n, i->
    {regularity evenExtModule (MM_(i+1)), 
	regularity oddExtModule(MM_(i+1))}
    )
betti res (MM_2, LengthLimit => 10)
--MM_2 has even and odd ext modules of regularity 0; but is not MCM.

{*
            
      restart
Macaulay2, version 1.9.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition, ReesAlgebra, TangentCone

i1 : needsPackage "MCMApproximations"

o1 = MCMApproximations

o1 : Package

i2 : needsPackage "CompleteIntersectionResolutions"

o2 = CompleteIntersectionResolutions

o2 : Package

i3 : n= 3;d=3;

i5 : S := ZZ/101[x_0..x_(n-1)]

o5 = kk[x , x , x ]
         0   1   2

o5 : PolynomialRing

i6 : ff = matrix{apply(n, i->(S_i)^d)}

o6 = | x_0^3 x_1^3 x_2^3 |

                            1                      3
o6 : Matrix (kk[x , x , x ])  <--- (kk[x , x , x ])
                 0   1   2              0   1   2

i7 : R = setupRings  ff

                         kk[x , x , x ]                    kk[x , x , x ]                                        kk[x , x , x ]
                             0   1   2                         0   1   2                                             0   1   2
o7 = {kk[x , x , x ], --------------------, -------------------------------------------, --------------------------------------------------------------}
          0   1   2        3      3      3        3      3      3       3     3      3         3      3      3       3     3      3     3     3      3
                      - 23x  - 24x  - 27x   (- 23x  - 24x  - 27x , - 41x  - 6x  + 19x )  (- 23x  - 24x  - 27x , - 41x  - 6x  + 19x , 42x  - 2x  + 43x )
                           0      1      2        0      1      2       0     1      2         0      1      2       0     1      2     0     1      2

o7 : List

i8 : use R_n

                             kk[x , x , x ]
                                 0   1   2
o8 = --------------------------------------------------------------
           3      3      3       3     3      3     3     3      3
     (- 23x  - 24x  - 27x , - 41x  - 6x  + 19x , 42x  - 2x  + 43x )
           0      1      2       0     1      2     0     1      2

o8 : QuotientRing

i9 : M = syzygyModule(3,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}})

o9 = cokernel {4} | -x_0x_1-x_2^2 x_0^2-x_1x_2  -x_0x_2      -x_2^2       -x_1^2-x_0x_2 0             0            0            |
              {4} | x_1^2         -x_0x_1+x_2^2 -x_0^2       -x_0x_2      x_1x_2        0             0            0            |
              {4} | x_1x_2        x_1^2-x_0x_2  x_0x_1+x_2^2 x_0^2+x_1x_2 x_2^2         0             0            0            |
              {4} | 0             0             x_1^2+x_0x_2 x_0x_1+x_2^2 0             -x_0^2+x_1x_2 x_2^2        x_0x_2       |
              {4} | 0             0             x_1x_2       x_1^2        0             -x_0x_1+x_2^2 -x_0x_2      -x_0^2       |
              {4} | 0             0             x_2^2        x_1x_2       0             x_1^2-x_0x_2  x_0^2+x_1x_2 x_0x_1+x_2^2 |

                             kk[x , x , x ]                                             /                        kk[x , x , x ]                        \
                                 0   1   2                                              |                            0   1   2                         |6
o9 : ---------------------------------------------------------------module, quotient of |--------------------------------------------------------------|
           3      3      3       3     3      3     3     3      3                      |      3      3      3       3     3      3     3     3      3 |
     (- 23x  - 24x  - 27x , - 41x  - 6x  + 19x , 42x  - 2x  + 43x )                     |(- 23x  - 24x  - 27x , - 41x  - 6x  + 19x , 42x  - 2x  + 43x )|
           0      1      2       0     1      2     0     1      2                      \      0      1      2       0     1      2     0     1      2 /

i10 : (MM,kk,p) = setupModules(R,M);

i11 : apply(n, i->
          {regularity evenExtModule (MM_(i+1)), 
      	regularity oddExtModule(MM_(i+1))}
          )

o11 = {{1, 0}, {0, 0}, {0, 0}}

o11 : List

i12 : betti res (MM_2, LengthLimit => 10)

             0 1 2 3 4 5 6 7 8 9 10
o12 = total: 6 8 3 3 3 3 3 3 3 3  3
          4: 6 . . . . . . . . .  .
          5: . 8 3 . . . . . . .  .
          6: . . . 3 3 . . . . .  .
          7: . . . . . 3 3 . . .  .
          8: . . . . . . . 3 3 .  .
          9: . . . . . . . . . 3  3

o12 : BettiTally

i13 : 
*}

