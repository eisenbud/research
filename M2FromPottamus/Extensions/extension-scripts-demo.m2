needs"Extension-Scripts.m2"

R = QQ[x]
A = coker matrix{{x^5}}
B = coker matrix{{x^4}}
F = complete res A
G = complete res B
E = constructRandomExtensions(3,F,G)
prune HH E

---
R = QQ[x]
A = coker matrix{{x^3}} ++ coker matrix {{x^9}}
B = coker matrix{{x^9}} ++ coker matrix {{x^4}} ++ coker matrix {{x^8}}
F = res A;
G = res B;
E = constructRandomExtensions(5,F,G)
prune HH E

-- try more general example

S = QQ[a,b,c]
A = coker matrix{{a^3,b^4,c^2}}
B = coker matrix{{a^1,b^6,c^3} }
e = constructRandomExtensions(10,res A, res B)
prune HH e

--

C = coker matrix{{a^3,b^4},{c^2,c^9}}
D = coker matrix{{a^3,b^8}}
f = constructRandomExtensions(10, res C, res D)
prune HH f

--
R = QQ[x]
A = coker matrix{{x^5}}
B = coker matrix{{x^4}}
F = complete res A
G = complete res B
G = res B;
B = coker G.dd_1
M = image F.dd_1
Z = Hom(M,B)
numgens Z


isExtensionTrivial({x^4 + x^3},F,G)
isExtensionTrivial({x^4 + x^3}, F, G)
isExtensionTrivial({x^4}, F, G)
isExtensionTrivial({0_R}, F, G)
isExtensionTrivial({x^6}, F, G)
isExtensionTrivial({x^1}, F, G)
isExtensionTrivial({x^2}, F, G)
isExtensionTrivial({x^3}, F, G)
isExtensionTrivial({x^1}, F, G)
isExtensionTrivial({0}, F, G)

-- try more general example

S = QQ[a,b,c]
A = coker matrix{{a^3,b^4,c^2}}
B = coker matrix{{a^1,b^6,c^3} }
F = res A;
G = res B;
B = coker G.dd_1
M = image F.dd_1
Z = Hom(M,B)
numgens Z

isExtensionTrivial({0,0,0,0},F,G)
isExtensionTrivial(flatten entries random(S^1,S^{4:-3}),F,G)

--
