R = QQ[a11,a22,a33,a44,a12,a13,a14,a23,a24,a34]   
M = matrix{
      {- a12 ,   a12 ,    0 ,   0 , a11 - a22 , -a23 , -a24 , a13 , a14 , 0},
      {- a13 , 0     ,  a13 ,   0 , -a23 , a11 - a33 , -a34 , a12 , 0 , a14},
      {- a14 , 0     ,    0 , a14 , -a24 , -a34 , a11 - a44 , 0 , a12 , a13},
      {    0 , - a23 ,  a23 ,   0 , -a13 , a12 , 0 , a22 - a33 , -a34 , a24},
      {    0 , - a24 ,    0 , a24 , -a14 , 0 , a12 , -a34 , a22 - a44 , a23},
      {    0 ,     0 , -a34 , a34 , 0 , -a14 , a13 , -a24 , a23 , a33 - a44}} 
     
     
time codim coker M, degree coker M
     
time I = minors(6,M);
time  codim I, degree I
