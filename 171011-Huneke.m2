loadPackage("StableResidual", Reload=>true)
n = #sg
S = kk[x_1..x_n,Degrees => sg]
T = kk[t]
phi = map(T,S, apply(sg,i->t^i))
I = ker phi
free = (S^1/I)
betti res free
omega = Ext^(n-1)(free,S^1)

star = M -> prune Hom(M,free)
ch = M ->prune Hom(M,omega)
en = M->prune Hom(M,M)
end--

restart
kk = ZZ/101
sg = {11,13,17,23}

e1 =  en star omega
ch e1
e2 = en star ch star omega
ch e2
isLocalIso(e2,ch e2)
e3 = en star ch star ch star omega
e4 = en star ch star ch star ch star omega
isLocalIso(e3,Ext^(n-1)(e3,S))
betti res e3
