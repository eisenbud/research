kk=ZZ/32003
S=kk[x,y]
R=S/ideal(x^3, y^3)
use R
K=R^1/ideal(x,y)
Ext(K,K)
methods Ext
code (Ext,ZZ, Module, Module)
code(Hom, Module, Module)
viewHelp Hom
