restart
kk=ZZ/32003
R=kk[x_1..x_4,y_1..y_4]
m1=genericMatrix(R,x_1,2,2)
m2=genericMatrix(R,y_1,2,2)
c=m1*m2-m2*m1
I=ideal flatten entries c
codim I
res I
j=ideal(trace m1, trace m2, det m1, det m2)
K=I+j
codim K
res K
KK = radical K
betti KK
codim KK
res KK
transpose gens KK
%The extra equations say that the rank is 0 (one less than necessary)
%Try the 3x3 case
%first check the ideal of 3x3s with rank sequence 1,0:
restart
kk=ZZ/32003
R=kk[x_1..x_9]
m1=genericMatrix(R,x_1,3,3)
i=ideal(trace m1, trace exteriorPower(2,m1), trace exteriorPower(3,m1))
j=ideal flatten exteriorPower(2,m1)
I=ideal mingens(i+j)
codim I
betti I
II=radical I
betti II

%nilpotent commuting 3x3s
restart
kk=ZZ/32003
R=kk[x_1..x_9,y_1..y_9]
m1=genericMatrix(R,x_1,3,3)
m2=genericMatrix(R,y_1,3,3)
i1=ideal(trace m1,trace m2,trace exteriorPower(2,m1)+trace exteriorPower(2,m2),
     trace exteriorPower(3,m1)+trace exteriorPower(3,m2))
i2=ideal mingens ideal flatten exteriorPower(2,m1*m2)
i3=ideal flatten ((m1*m2)-(m2*m1))

I=ideal mingens(i1+i2+i3)
betti I
--codim I = 10
IR = res I

--Get the following error message FAST
--Virtual memory exceeded in `new'
-- 
--Process M2 exited abnormally with code 255
 ---------------------

--How far can we go -- and how fast -- with just plain commuting matrices? 
 restart
n=4
kk=ZZ/32003
R=kk[x_1..x_(n^2),y_1..y_(n^2)]
m1=genericMatrix(R,x_1,n,n)
m2=genericMatrix(R,y_1,n,n)
c=m1*m2-m2*m1
I=ideal flatten entries c;
time gens gb(I, Algorithm => Homogeneous2, Strategy => LongPolynomial);
betti g
--used 371.512 seconds
-- on DE's mac pro, 090827, used 19560. seconds.
--467 generators

restart
commuting4by4grevlex = (kk) -> (
R = kk[vars(0..31)];
--   	 MonomialSize=>8];
	     I = ideal"
	              -jo+ip-vA+uB-xC+wD,
		      	     -ap+bo+cp-do+kB-lA+mD-nC,
			     	    -aB+bA+eB-fA+pq-or-zC+yD,
				    	   -aD+bC+gD-hC+ps-ot+BE-AF,
					   	  aj-bi-cj+di-qv+ru-sx+tw,
						         jo-ip-lq+kr-ns+mt,
							        -cr+dq+er-fq-iB+jA-sz+ty,
								       -ct+ds+gt-hs-iD+jC-qF+rE,
								       	      av-bu-ev+fu-jk+il-xE+wF,
									      	     cl-dk-el+fk+mF-nE+ov-pu,
										     	    lq-kr+vA-uB-zE+yF,
											    	   -eF+fE+gF-hE+ls-kt+vC-uD,
												   	  ax-bw-gx+hw-jm+in-vy+uz,
													         cn-dm-gn+hm+kz-ly+ox-pw,
														        ez-fy-gz+hy+nq-mr+xA-wB,
															       ns-mt+xC-wD+zE-yF")
I=commuting4by4grevlex(ZZ/32003)
time  gens gb(I, Algorithm => Homogeneous2, Strategy => LongPolynomial);

---------------
