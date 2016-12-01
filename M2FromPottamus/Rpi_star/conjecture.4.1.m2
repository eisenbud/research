restart
--check O(8,0,0,0) 
load "computingRpi_star.m2"
load "vectorBundlesOnPP1.m2"

L={1,1,1,9} -- list of twists
kk=ZZ/101 -- the ground field
Lmax=L_(#L-1) -- maximal twist occuring

M=setupDef(L,kk) -- the presentation matrix of the versal deformation of 
--                  O(L_0)+O(L_1)+...+O(L_(#L-1))
betti M

-- the corresponding exterior matrix :
time N=symmetricToExteriorOverA(M,ee,xx); -- used 22.1536 seconds



time fN=res(coker N,LengthLimit=>Lmax)
bettiT dual fN
--    index: -8 -7 -6 -5 -4 -3 -2 -1  0
--       -2: 24 21 18 15 12  9  6  3  .
--       -1:  1  2  3  4  5  6  7  8 12
Rpis1=apply(-Lmax..-2,i-> degreeZeroPart(fN[-i]**E^{{0,-i+1}},A))

-- The following is only for the special case O+O+O+O(8) ie. L={1,1,1,9}
R=kk[x_0..x_6,y_0..y_6,z_0..z_6]
Bs=apply(Rpis1,c->substitute(c.dd_0,vars R))
strata={
J3221=minors(6,Bs#6),
J3311=minors(5,Bs#6),
J4211=minors(5,Bs#5),
J3320=minors(3,Bs#7),
J4220=minors(5,Bs#5)+minors(3,Bs#7),
J4310=minors(5,Bs#5)+minors(4,Bs#6)+minors(3,Bs#7),
J5111=minors(4,Bs#4),
J5210=minors(4,Bs#4)+minors(3,Bs#7),
J4400=minors(2,Bs#7),
J6110=minors(3,Bs#3)+minors(3,Bs#7),
J5300=minors(4,Bs#4)+minors(2,Bs#7),
J6200=minors(3,Bs#3)+minors(2,Bs#7),
J7100=minors(2,Bs#2),
J8000=minors(1,Bs#1)};
time apply(strata,c->(dim c, degree c)) -- used 55.0686 seconds

minors(4,Bs#5)==intersect(J4400,J5111)
minors(3,Bs#6)==intersect(J6110,J4400)
  
time minors(4,Bs#6)==intersect(J5111,J4310) --- used 174.769 seconds
apply(strata,c->(codim c, betti c))


--here we indicate the inclusion between strata closure and their
--codimensions
         codim J8000==21
	 codim J7100==17
	 codim J6200==15
codim J6110==13 and codim J5300==13              
       codim J5210==10 and codim J4400==12
codim J5111==9 and codim J4310==8
                   codim J4220==7
codim J4211==5 and codim J3320==5
         codim J3311==4
         codim J3221==1


time apply(strata,c->(c==radical c))

















