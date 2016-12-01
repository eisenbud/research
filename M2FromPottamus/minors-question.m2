S=kk[x_1..x_4]
m=matrix{{x_1,1_S,0,1},
         {1_S ,x_2, 1_S, 0},
	 {0,1_S, x_3, 1_S},
	 {1_S,0,1_S, x_4}}
i=minors(3, m)
codim i
m
res i
