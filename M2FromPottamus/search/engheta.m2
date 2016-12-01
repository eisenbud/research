kk = ZZ/32003
R = kk[a..f]
veronese = trim minors(2,genericSymmetricMatrix(R,a,3))
Rbar = R/veronese
S = kk[y_0..y_4]
link = kernel map(Rbar,S,random(Rbar^{1}, Rbar^5))
p1p2 = ideal(mingens link * random(S^7, S^2));
time unmix = p1p2 : link
degrees unmix
fgh = ideal(unmix_0, unmix_1, unmix_2)
betti res fgh
transpose gens fgh

-- Leah's example
R = ZZ/32003[a..e]

betti res ideal(c*d*e+a*b*c,a*d*e+b*c*d,a*b*e+b*c*d )
