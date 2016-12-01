restart
--------------
kk=ZZ/101
T=kk[a..f]
S=kk[x,y,z]
J1 = intersect(
     ideal"a,b,c", ideal"b,e,f", ideal"c,d,e", ideal"a,d,f"
     )
J=ideal"abc, adf, bef, cde, ae, bd, cf"
J==J1

R=T/J
F=map(R,S, matrix{{a-d+f, c-d+e, b+e-f}})
I=ker F
--------------

