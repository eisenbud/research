restart

catalecticant = (R,v,m,n) -> 
                 map(R^m,n,(i,j)-> R_(i+j+v))
R=kk[x_0..x_5,MonomialOrder=>Lex]

m=catalecticant(R,0,2,2)|catalecticant(R,2,2,2)
i=minors(2,m)
J=gin i
ass  J
