for n from 2 to 5 do(
kk=ZZ/101;
S = kk[x_1..x_n];
mm = ideal gens S;
R = S^1/mm^2;
for i from 0 to n do(
print numgens (prune  Tor_i(R,R))))
)
loadPackage "BoijSoederberg"
viewHelp BoijSoederberg
viewHelp 
betti res randomSocleModule({0,1,3,4},3)



randomSymmetricSocleModule = method(Options => {CoefficientRing => ZZ/101})
randomSymmetricSocleModule(List, ZZ) := opts -> (L, m) -> (
     c:=#L-1; -- codimension
     r:=last L-first L-c; -- regularity
     s:=c*r; -- socle degree mod (vars)^[r+1]
     kk := opts.CoefficientRing;
     R:=kk[vars(0..c-1)];
     mR := ideal apply(gens R, x -> x^(r+1));
     B:=pureBetti L;
     f:=random(R^(m*B_c), R^{m*B_0:-s+r});
     f = f-transpose f;
     f = map(R^(m*B_c), R^{m*B_0:-s+r}, matrix"0,b2,c2;-b2,0,a2;-c2,-a2,0");
          --matrix"0,bc,ac;-bc,0,ab;-ac,-ab,0"); --Works
	  --matrix"0,a2,b2;-a2,0,c2;-b2,-c2,0"); --Doesn't work
     print f;
     prune (image (f**(R^{s-r}/mR)))
     )
randomSymmetricSocleModule({0,1,3,4},3)
betti res randomSymmetricSocleModule({0,1,3,4},3)



restart
installPackage "BoijSoederberg"
viewHelp BoijSoederberg
viewHelp BettiTally
B =new BettiTally from {(0,{0},0)=>1,
                        (1,{2},2)=>3,
			(1,{3},3)=>2,
			(2,{3},3)=>2,
			(2,{4},4)=>3,
			(3,{6},6)=>1
			}
decompose B

x = 9
B =new BettiTally from {(0,{0},0)=>1,
                        (1,{2},2)=>10,
			(2,{3},3)=>16,
			(3,{4},4) => x,
			(2,{4},4) => x,
			(3,{5},5)=>16,
			(4,{6},6)=>10,
			(5,{8},8)=>1
			}
decompose B

16*(90.0/128)

restart
loadPackage "BoijSoederberg"
S = kk[a,b]
i = ideal"a2,ab,b3"
i = a*ideal"a2,b2"
betti (F = res i)
F.dd
decompose betti res i



S = kk[a,b,c]
i = ideal"a3,a2b,ab2"
decompose betti res i

uninstallPackage "BoijSoederberg"
installPackage "BoijSoederberg"

viewHelp BoijSoederberg

b = matrix"1,0,0,0;
     	   0,6,8,3;
	   3,8,6,0;
	   0,0,0,1"
decompose mat2betti b

b1= matrix"1,0,0,0;
     	   0,3,2,0;
	   0,2,3,0;
	   0,0,0,1"
decompose mat2betti b1
