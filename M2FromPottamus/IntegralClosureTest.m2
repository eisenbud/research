restart
loadPackage "IntegralClosure"
viewHelp IntegralClosure
code methods makeS2
makeS2
T = kk[s,t]
S=kk[a,b,c,d]
I=kernel map(T,S,{s^4,s^3*t, s*t^3,t^4})
R=S/I
makeS2 R
