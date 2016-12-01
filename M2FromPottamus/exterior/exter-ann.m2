res1gen=(nvars,deg)->(
kk:=ZZ/32003;
E=:kk[x_1..x_nvars,SkewCommutative=>true];
m=:random(E^1,E^{-3});
print betti res(coker m, LengthLimit=>2))

E=kk[x_1..x_15,SkewCommutative=>true]
m=random(E^1,E^{-3})
F=res(coker m, LengthLimit=>2)
betti F
E=kk[a..i,SkewCommutative=>true]
n=map(E^1,E^{-3},matrix{{a*b*c+b*c*d+c*d*e+d*e*f+e*f*g+f*g*h+g*h*i+h*i*a+i*a*b}})
betti(F=res(coker n, LengthLimit=>2))

restart
gin1=(nvars, deg)->(
kk:=ZZ/32003;
E:=kk[x_1..x_nvars,SkewCommutative=>true];  --,MonomialOrder=>Lex];
m:=random(E^{0},E^{-deg});
n:=gens gb m;
print betti n;
print transpose gens annihilator ideal leadTerm n;
print transpose leadTerm n;)

gin1(11,3)
hf (0..10,image transpose oo)
binomial(10,3)

o18 = {-3} | x_1x_2x_3          |
      {-4} | x_1x_3x_4x_5       |
      {-4} | x_1x_2x_4x_5       |
      {-4} | x_1x_2x_4x_6       |
      {-5} | x_1x_3x_4x_6x_7    |
      {-5} | x_2x_3x_4x_6x_7    |
      {-5} | x_1x_2x_5x_6x_7    |
      {-5} | x_1x_3x_5x_6x_7    |
      {-5} | x_2x_3x_5x_6x_7    |
      {-5} | x_2x_3x_4x_5x_6    |
      {-5} | x_2x_3x_4x_5x_7    |
      {-5} | x_1x_4x_5x_6x_7    |
      {-5} | x_2x_4x_5x_6x_7    |
      {-5} | x_3x_4x_5x_6x_7    |
      {-6} | x_2x_3x_4x_5x_8x_9 |
      {-6} | x_1x_3x_4x_6x_8x_9 |
      {-6} | x_2x_3x_4x_6x_8x_9 |
      {-6} | x_1x_2x_5x_6x_8x_9 |
      {-6} | x_1x_3x_5x_6x_8x_9 |
      {-6} | x_2x_3x_5x_6x_8x_9 |
      {-6} | x_1x_2x_4x_7x_8x_9 |
      {-6} | x_1x_3x_4x_7x_8x_9 |
      {-6} | x_2x_3x_4x_7x_8x_9 |
      {-6} | x_1x_4x_5x_6x_8x_9 |
      {-6} | x_2x_4x_5x_6x_8x_9 |
      {-6} | x_3x_4x_5x_6x_8x_9 |
      {-6} | x_1x_2x_5x_7x_8x_9 |
      {-6} | x_1x_3x_5x_7x_8x_9 |
      {-6} | x_2x_3x_5x_7x_8x_9 |
      {-6} | x_1x_4x_5x_7x_8x_9 |
      {-6} | x_2x_4x_5x_7x_8x_9 |
      {-6} | x_3x_4x_5x_7x_8x_9 |
      {-6} | x_1x_2x_6x_7x_8x_9 |
      {-6} | x_1x_3x_6x_7x_8x_9 |
      {-6} | x_2x_3x_6x_7x_8x_9 |
      {-6} | x_1x_4x_6x_7x_8x_9 |
      {-6} | x_2x_4x_6x_7x_8x_9 |
      {-6} | x_3x_4x_6x_7x_8x_9 |

              38       1
o18 : Matrix E   <--- E

