m=matrix"1,0,3,2,0;0,1,2,1,0;1,0,2,0,1;0,2,3,0,1"
minors(4,m)
minors(3,m)
           a,b,c,d,e,f,g,h,i
p34=matrix"1,2,1,0,0,0,0,0,0"
p24=matrix"2,3,0,0,0,1,0,0,0"

p14=matrix"1,0,0,0,3,2,0,0,0"
p23=matrix"3,4,0,0,0,0,0,0,1"
p04=matrix"0,0,0,1,2,1,0,0,0"
p13=matrix"1,0,0,0,2,0,0,0,1"
p03=matrix"0,0,0,2,3,0,0,0,1"
p12=matrix"1,0,0,0,0,0,0,4,3"

p02=matrix"0,0,0,1,0,0,0,3,2"
p01=matrix"0,0,0,0,0,0,1,2,1"

m=p34||p24||p14||p23||p04||p13||p03||p12||p02||p01
rank (m18=m^{1..8})
rank(m27=m^{2..7})
(syz m18)_{2,3}
S=ZZ[a,b,c,d,e,f,g]
v=matrix"a,b,0,c,d,e,0,f,g"
m18=substitute(m18,S)
m18*(transpose v)
diff(vars S, oo)


S=kk[a..i]
I=ideal"ab2c, a2b3f, ae3f2, a3b4i, de2f, ae2i, d2e3i, ah4i3, dh3i2, gh2i"
L=flatten (degrees gens I)_1
T=kk[x_1..x_10, Degrees=>L]
phi=map(S,T,gens I)
J=ker phi

restart
S=kk[a..i]
I=ideal"ab2c, a2b3f, ae3f2, a3b4i, de2f, ae2i, d2e3i, ah4i3, dh3i2, gh2i"
I1=ideal((a*b^2*c)^6, (a^2*b^3*f)^4, (a*e^3*f^2)^4, (a^3*b^4*i)^3, (d*e^2*f)^6, (a*e^2*i)^6, (d^2*e^3*i)^4, (a*h^4*i^3)^3, (d*h^3*i^2)^4, (g*h^2*i)^6)
L=flatten (degrees gens I)_1
L1=flatten (degrees gens I1)_1
T=kk[p24,p14,p23,p04,p13,p03,p12,p02, Degrees=>(L_{1..8})]
T1=kk[p24,p14,p23,p04,p13,p03,p12,p02]
phi=map(S,T,(gens I)_{1..8})
phi1=map(S,T1,(gens I1)_{1..8})
J1=ker phi1
transpose gens J1
viewHelp MonomialOrder
