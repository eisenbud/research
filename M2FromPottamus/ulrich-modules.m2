S=kk[x_0..x_3];
M=coker map( S^3, S^{6:-1},
     transpose matrix{
	  {x_1, -x_0, 0},
	  {0, x_1, -x_0},
	  {x_2, -x_1, 0},
	  {0, x_2, -x_1},
	  {x_3, -x_2, 0},
	  {0, x_3, -x_2}}
     );
betti (F=res M)
E=kk[a..d, SkewCommutative=>true];
toE=map(E,S,matrix{{a..d}});
f1=toE F.dd_1
f2=toE F.dd_2
f1*f2