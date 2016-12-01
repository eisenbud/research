--random search for modules that are extension of
--k^p by k(-1)^q in c variables over a small field
randomExtension = (R,p,q)->(
     c := numgens R;
     mR := ideal apply(gens R, x -> x^(2));     
     f:=random(R^{q:(c-1)},R^p);
     prune (image (f**(R^1/mR)))
     )

end
restart
load "random2RegularResolution.m2"

kk= ZZ/3
S = kk[x_1..x_5]

time for i from 1 to 2400000 do(
	  B = betti res (M=randomExtension(S,3,3));
	  if B#?(3, {3}, 3) and B#(3, {3}, 3) >=9 then (
	       print B;
	       print toString presentation M
	       )
	  )
     
     
time tally apply( 1000, i->(
	  B = betti res randomExtension(S,3,3);
	  if B#?(3, {3}, 3) and B#(3, {3}, 3) >=8 then B
	       print toString presentation M
	       )
	  )

	  



