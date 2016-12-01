S=kk[u,x,y]
f = u^2-x^3*y^3
R = S/(ideal f)
Rbar = integralClosure R
icFractions R
dim singularLocus Rbar

S=kk[v,w,u,x,y]
J=matrix"2v,0,y3,3y2x;
0,2w,3x2y, x3;
x,y,v,w"

codim minors(2,J)
