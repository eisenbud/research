-- Seiler preprint II, Example 8.7
needs "involutive.m2"
R = QQ[z,y,x]
h1 = z^2+x*y
h2 = y*z-x*z
h3 = y^2+x*z
h4 = x^2*z
h5 = x^2*y

I = ideal(h1, h2, h3, h4, h5)
G = gb I
J = janetBasis G
S = invResolution J
