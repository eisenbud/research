--two parametrized benchmarks for resolutions.

mrc = (n,d,k,p) -> (
     --k forms of degree d in n vars, char p
     if p == 0 then kk := QQ else kk = ZZ/p;
     S := kk[x_1..x_n];
     I := ideal basis(d+1,S^1)+ideal random(S^1,S^{k:-d});
     time (res I).dd;
     )
mrc1 = (n,d,k,p) -> (
     --k forms of degree d in n vars, char p
     --uses k as the codim of the space of forms of degree d
     k1 := binomial(n-1+d,d)-k;
     if p == 0 then kk := QQ else kk = ZZ/p;
     S := kk[x_1..x_n];
     I := ideal basis(d+1,S^1)+ideal random(S^1,S^{k1:-d});
     time (res I).dd;
     )

mrc1Ideal = (n,d,k,p) -> (
     --k forms of degree d in n vars, char p
     --uses k as the codim of the space of forms of degree d
     k1 := binomial(n-1+d,d)-k;
     if p == 0 then kk := QQ else kk = ZZ/p;
     S := kk[x_1..x_n];
     ideal basis(d+1,S^1)+ideal random(S^1,S^{k1:-d})
     )

///
mrc1(8,2,4,32003) -- 11.1 sec --magma 1.2 sec, now less.
mrc1(8,2,4,32003) -- 11.1 sec
///

fromDualDiff = (f) -> (
         R := ring f;
          d := first max degrees source f;
          g := product apply(generators R, v -> v^d);
          f1 := diff( matrix{{g}},transpose f);
          mingens (
               image (target f1 ** matrix table(1, numgens R, (i,j) -> R_j^(d+1))) 
               : 
               image f1
               );
	  error();
          )

gor = (n,d,k,p) -> (
     if p == 0 then kk=QQ else kk=ZZ/p;
     S=kk[x_1..x_n];
     f = sum(1..k, t ->((random(S^1,S^{-1}))^d));
     I = ideal fromDual(f);
     time betti res I
     )
///
gor(8,3,5,32003) -- 16.1 sec -- magma: 2.7 (now 1.5?) 
gor(6, 3, 3,0) -- 191 sec
gor(6, 3, 3,32003) -- 191 sec

gor(3,2,1,32003)

///

end
restart
load "benchmark-res.m2"
I=trim mrc1Ideal(12,2,5,32003);
S= ring I
betti I
cubes=ideal map(S^1, S^{12:-3}, (i,j) ->(S_j)^3)
time J=cubes:I;
time betti res (J/cubes, LengthLimit => 4) -- to length 2 took only about 20 sec, but length 4 over 27min

S=kk[a,b]
cubes = ideal map(S^1, S^{numgens S:-3}, (i,j) ->(S_i)^3)
(cubes):(ideal(vars S))

betti J
vars S
hilbertSeries(S^1/I)
for i  from 0 to 5 list hilbertFunction(i, S^1/I)


viewHelp hilbertFunction
kk=ZZ/32003
gor(8,3,5,32003) -- 16.1 sec
gor(6, 3, 3,0) -- 191 sec
gor(5,3,2,32003)


S = kk[a,b]
f = matrix{{(a+b)^2}}
diff(a-b,f)
f1 = matrix{{a^2}}
I = ideal fromDualDiff(f)
I1 = ideal fromDualDiff(f1)
betti res I

code fromDual
fromDual(matrix{{a^2*b^3}})
