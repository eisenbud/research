kk = ZZ/32003
R = kk[a,b,c,x,y,z,t,Degrees=>{{4,3,1},
	  {4,3,1},
	  {4,3,1},
	  {1,1,0},
	  {1,1,0},
	  {1,1,0},
	  {1,0,1}}]
R0 = kk[a,b,c,x,y,z,t,Degrees=>{4,4,4,1,1,1,1}]
I = ideal random(R^1, R^{-{12,9,3},-{4,3,1}});
A = R/I
A0 = R0 / (substitute(I,R0))

G = random(A^2, A^{-{1,0,1},-{1,1,0},-{1,1,0},-{1,1,0},-{4,3,1},-{4,3,1}})
SG = syz G
pos = positions(degrees source SG, d -> d#0 <= 12)
SG0 = SG_pos
ran = random(source SG0, A^{-{12,9,3}})
F = SG0 * ran
J = ideal F
J0 = substitute(J,R0)
codim J0

