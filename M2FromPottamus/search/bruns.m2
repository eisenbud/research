R = ZZ/32003[a..d]
I = (ideal vars R)^4
C = dual res I
C = C[-4]
-- project C.dd_3
f = random(R^36, R^84) * C.dd_3
syz transpose f
