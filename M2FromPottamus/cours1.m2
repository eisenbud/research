--Example of a nonsaturated codim 2 ideal I in 3 vars
--such that the hilbert poly and hilbert fcn of S/I
--coincide before the regularity.

S=kk[x,y,z]
m1=matrix{{0, x,0,0,z},
     {0,0,y,z,0},
     {0,0,0,x,0},
     {0,0,0,0,y},
     {0,0,0,0,0}}
m=m1-transpose m1
i1=pfaffians(4,m)
f=map(S,S,matrix{{x^2,y^2,z^2}})
i2=f i1
betti res i2
i3= ideal(z^5, (x+y)^5)
betti res i3
I=intersect (i2,i3)
betti res I
o37 = total: 1 5 5 1
          0: 1 . . .
          1: . . . .
          2: . . . .
          3: . . . .
          4: . . . .
          5: . 3 . .
          6: . 2 4 .
          7: . . . 1
          8: . . 1 .
          9: . . . .
transpose gens I
o38 = {-6} | z6                                              |
      {-6} | x5z+5x4yz+10x3y2z+10x2y3z+5xy4z+y5z+10xz5+10yz5 |
      {-6} | x6+4x5y+5x4y2-5x2y4-4xy5-y6                     |
      {-7} | y2z5                                            |
      {-7} | x5y2+5x4y3+10x3y4+10x2y5+5xy6+y7                |
