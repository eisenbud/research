restart

--Theorem (Herzog):
--If I is a primary, homog ideal gen in degree d-1 in n vars,
--then (mI)^((d-2)(n-1)) is a power of the maximal ideal.

n=3
deg=5

S=kk[x_1..x_n]
m = ideal vars S
I=ideal frobPower(gens m,deg-1)
mI=m*I

scan((deg-2)*(n-1) ,
         i->(j=i+1;
            j1=deg*j-deg;
            print betti res ((mI^j):(m^j1))))

scan((deg-2)*(n-1) ,
         i->(j=i+1;
            j1=deg*j-deg;
            print linearity (mI^j)))


