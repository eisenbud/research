I=monomialCurve(R,{1,3,4})
gens I
F=res I
f=F.dd_2
g=transpose((transpose f)_{0,1,3})
j=minors(3,g)
G=res j
codim j
decompose j
betti G
(res coker g).dd_2
---------------------
restart
S=kk[x_1..x_6,y_1..y_15]
sk= genericSkewMatrix(S,y_1,6)
X=(vars S)_{0..5}
alpha=map(S^6,S^{7:-1},(transpose X)|sk)
betti alpha
ran=random(source alpha, S^{5:-1})
phi=alpha*ran

codim (i=minors(1,phi))
codim (i+ideal X)

------------------
restart
S=kk[x_1..x_5,y_1..y_10]
sk= genericSkewMatrix(S,y_1,5)
X=(vars S)_{0..4}
m=X*sk
F=res coker m
transpose F.dd_1
F.dd_1*(transpose X)
F.dd_2
betti F
col1=submatrix (F.dd_2, {0..4},{0})
col25=F.dd_2*random(source F.dd_2,S^{4:-4 })

u4=col1 | col25
V=transpose U
isHomogeneous V

VV=res coker V
f=transpose (F.dd_2*random(source F.dd_2,S^{5:-4}))
WW=res coker f
betti WW
codim ideal transpose WW.dd_2
res (coker transpose f, LengthLimit=>3)
G=oo
betti G -- 5,5,1
codim ideal transpose G.dd_2
codim minors(4,f)
codim minors(1,f)
 --- 8
codim((ideal X)+minors(1,f))
 --- 8
-----------------------
------------------
--same with 6 gens
restart
S=kk[x_1..x_6,y_1..y_15]
sk= genericSkewMatrix(S,y_1,6)
X=(vars S)_{0..5}
m=X*sk
F=res(coker m, LengthLimit=>3)
betti F
F.dd_2*random(source F.dd_2,S^{6:-4 })


transpose F.dd_1
F.dd_1*(transpose X)
F.dd_2
betti F
col1=submatrix (F.dd_2, {0..4},{0})
col25=F.dd_2*random(source F.dd_2,S^{4:-4 })

u4=col1 | col25
V=transpose U
isHomogeneous V

VV=res coker V
f=transpose (F.dd_2*random(source F.dd_2,S^{5:-4}))
WW=res coker f
betti WW
codim ideal transpose WW.dd_2
res (coker transpose f, LengthLimit=>3)
G=oo
betti G -- 5,5,1
codim ideal transpose G.dd_2
codim minors(4,f)
codim minors(1,f)
 --- 8
codim((ideal X)+minors(1,f))
 --- 8
-----------------------
f=random(source gens I, R^{-3,-3})
j1=(gens I)*f
j=j1 | map(R^1, R^{-2},matrix{{b*c-a*d}})
ideal j :I
presentation module I
------------------- 
restart
S=kk[a..f,Degrees=>{2,5:1}]
m=matrix{{a,b^2,c^2,0},{0,d^2,e^2,f^2}}
i=minors(2,m)
n=presentation module i
betti n
p=random(S^1,S^6)
x=p*n
isHomogeneous x
codim ideal x

-------------------
--syz of the generic module
p=7;q=4;
S=kk[x_{1,1}..x_{p,q}]
m=genericMatrix(S,x_{1,1},q,p)
F=res coker m
F.dd_2
f=F.dd_2*random(source F.dd_2, S^{-q-1})
i=ideal transpose f
codim i

---------------
restart
S=kk[a,b,c,d]
e=1
I=monomialCurve(S,{2*e-1,2*e+1,4*e})
betti (F=res I)
degree I
gens I
F.dd_1
F.dd_2
