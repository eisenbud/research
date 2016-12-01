--Example that failed on version 1.0, and hit a seg fault on Erman's machine
-- with version 1.2. Works fine on DE's machine with 1.3.
S=QQ[x_0..x_4];
time for i from 1 to 100 do(
M=matrix{{x_0,x_1,x_2},{x_3,x_4,random(1,S)},{random(1,S),random(1,S),random(1,S)}};
I=minors(2,M);
L=minimalPrimes(I);
)
