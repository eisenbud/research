restart
S = kk[a,b,c,d]
T = kk[s,t]
I = ker map(T,S,matrix"s4,s2t2,st3,t4")
S5 = kk[a,b,c,d,e]
J = ker map(T,S5,matrix"s4,s2t2,st3,t4,s3t")
f = map(S5,S)
B=pushForward(f,S5^1/J)
A = S^1/I
g = map(B,A,matrix{{1_S},{0_S}})
ann coker g
viewHelp integralClosure
viewHelp conductor
conductor map(S5/J,S/I)

conductor icMap (S/I)
