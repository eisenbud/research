max.run.ones=function(v){
  if(sum(v)==0){return(0)}
  dd=diff(append.zero(v))
  plus=which(dd==1)
  minus=which(dd==-1)
  max(minus-plus)
}

multiplicity = function(v,k){
  #Computes the "effective number of runs of length >=k" AND another bit,
  #1 or zero, to say whether there's AT LEAST ONE run of length k+1.
  #a run of length at least k+1. Returns a vector (effective number,
  #if(sum(v)==0){return(0)}
  dd=diff(append.zero(v))
  plus=which(dd==1)
  minus=which(dd==-1)
  diffs=-(plus-minus)
#  print(diffs)
  mult=0
  bigger.than.k=0
  for (i in 1:(length(diffs))){
    m=max(0,diffs[i]-k+1)
    mult = mult+m
    if(m>1){bigger.than.k = 1}
  }
  return(c(mult, bigger.than.k))
}

#test1=c(1,1,1,0,1,1,0,1,1,1,1)
#multiplicity(test1, 4)
#multiplicity(test1, 3)
#m=multiplicity(test1, 2)

exchange = function(x){
	ones = which(x==1)
	if(length(ones)==1){
		one=ones
	}else{
		one=sample(ones,1)
	}
	
	zeros = which(x==0)
	if(length(zeros)==1){
		zero=zeros
	}
	else{
		zero = sample(zeros,1)
	}
	x[zero]=1
	x[one]=0
	x
}

bit.flip = function(x){
	pos = sample(length(x),1)
	x[pos] = (x[pos]+1)%%2
	x
}

size.of.b = function(n,b){
	if((n==b) | (b==0) ){
		return(1)	
	}
	
	2*2^(n-b-1)+(n-b-2)*2^(n-b-2)
}

draw.atleast.b = function(n,b,d){
	start = sample(n-b+1,1)
	y=sample(c( rep(1,d-b), rep(0,n-d) ), n-b)
	if(start==1){
		return(c(rep(1,b),y))
	}
	if(start==n-b+1){
		return(c(y,rep(1,b)))	
	}
	c(y[1:(start-1)],rep(1,b),y[start:(n-b)])
}

## nested sampling conditional on D=d
## for i = 1..d
sim.cond.d = function(n,d,n.sim=1000){
	z=c(rep(0,n+1))

	for(k in 0:(d-1)){
		x=draw.atleast.b(n,k,d)
		for(i in 1:n.sim){
                  #print(x)
			y=exchange(x)
			a=max.run.ones(y)
			if(a>=k){
				x=y
			}
			
			a=max.run.ones(x)
			if(a>=(k+1)){
				z[k+1]=z[k+1]+1
				last.good = x	
			}
		}

	}
	c(1,z/n.sim)
}

next.on.b = function(x,b){
	if(runif()>.5){
		y=bit.flip(x)
	}
	else{
		y=exchange(x)	
	}
	if(max.run.ones(y)==b){
		return(y)	
	}	
	x
}



compute.b.rejection = function(n,b,ntimes){
	x=	c( rep(1,b), 0, rep(0,n-b-1) )
	rejection=0
	for( i in 1:ntimes){
		y=next.on.b(x,b)
		if(sum(y==x)==n){
			rejection=rejection+1	
		}	
	}
	rejection/ntimes
}

             
sim.cond.d1 = function(n,d, n.sim=100){
  #considering length n sequences of zeros and ones, with exactly d ones:
  #outputs P(b >=k | b>=k-1) where b is the maximal run of ones,
  #by uniformly making
  #n.sim random choices of a sequence with d terms and a run of at least k-1,
  #and counting the proportion of choices with a run of at least k.
	z=c(rep(0,(n+1)))

	for(k in 0:(d-1)){
                countk = 0
                countkplus1 = 0
		for(i in 1:n.sim){
			y=draw.atleast.b(n,k,d)
                        m=multiplicity(y,k)
                        countk = countk+1/m[1]
                        if (m[2]>0){countkplus1 = countkplus1+1/m[1]}
		}
                z[k+1]=countkplus1/countk
	}
	c(1,z)
}

#sim.cond.d1(11,1,1000)
#sim.cond.d1(11,6,1000)
#sim.cond.d1(11,11,1000)             



             
to.bin = function(x,n=10){ 
	y=rep(0,n)
	i=1
	while(x>0){
		y[i] = x%%2
		x = (x-y[i])%/%2
		i=i+1	
	}
	y
}


#n=10

sim.random.b1 = function(n,d){
	x=rep(0,n+2)
	y=c(0,rep(1,n),0)
	for(i in 1:d){
		z=sample(which(y==1),1)
		x[z]=1
		y[(z-1):(z+1)]=0
	}
	x[2:(n+1)]	
}

cbd.exact =function(n){
 M= matrix(0,ncol=n+1, nrow=n+1)
for(i in 0:(2^n-1)){
	x=to.bin(i)
	d=sum(x)
	b=max.run.ones(x)
	M[b+1,d+1] = M[b+1,d+1]+1
}
 return(M)
}

#cbd.exact(2)
#sim.cond.d(11,6)

sim.cond.d.exact=function(n,d){
  M=cbd.exact(n)
  ans=c(1,rep(0,(n-1)))
  for(k in 2:(d-1)){
   bigger =sum( M[(k+2):(n+1), d+1] )
   big =sum( M[(k+1):(n+1), d+1] )
   ans[k]=(bigger/big)
  }
  return(ans)
}

#sim.cond.d1(11,6,10000)-sim.cond.d.exact(11,6)    

#SE=sim.cond.d.exact(11,6)    
#S=sim.cond.d1(11,6,1000)             
#S
#SE
#S-SE
#cbd.exact(11)
#cbd.exact(10)

cbd1 = function(n,d,n.sim=100){
-diff(cumprod(sim.cond.d1(n,d,n.sim)))*choose(n,d)
}


compute.all.cbd1 = function(n=10, n.sim=100){
  CBD = matrix(0, ncol=n+1,nrow=n+1)
  for(d in 1:(n-1)){
    CBD[,d+1] = cbd1(n,d,n.sim)
  }

  CBD[1,1]=1
  CBD[n+1,n+1]=1
  CBD
}

compare1 = function(n,n.sim=100){             
M = cbd.exact(n)
N=compute.all.cbd1(n,n.sim)
A=abs((N - M)/M)
print(max(A, na.rm=T))
print(sum(A, na.rm=T))
plot (hist((N-M)/M))
}

#compare1(10,1000)
#system.time(compare1(10,10000)) ##60 sec


cbd = function(n,d,n.sim=100){
	-diff(cumprod(sim.cond.d(n,d,n.sim)))*choose(n,d)
}

compute.all.cbd = function(n=10, n.sim=100){
	CBD = matrix(0, ncol=n+1,nrow=n+1)
	for(d in 1:(n-1)){
		CBD[,d+1] = cbd(n,d,n.sim)
	}

	CBD[1,1]=1
	CBD[n+1,n+1]=1
	CBD
}


fillinKl<-function(n=20,l=10){
        ds=rep(0,n+1)
        for (d in (0:n)){
                      p1=rep(0,n+1)
                    vec1=rep(0,n+1)
                    vec2=rep(0,n+1)
        for (j in 0:n){
                    vec1[j+1]=(1-(2*j/(n+1)))^l
                    vec2[j+1]=0

        for (m in 0:d){
vec2[j+1]=vec2[j+1]+((-1)^m)*choose(d,m)*choose(n-d,j-m)}
                    p1[j+1]=vec1[j+1]*vec2[j+1]
}
                    ds[d+1]=sum(p1)
                        p1=rep(0,n+1)
                    }

                    return(ds)
                    }


#Prob2: Blocks are defined by longest seq of 1's

cbd.true10=cbd.exact(10)
cbd.true20=cbd.exact(20)
cbd.true20


distancefrompi3<-function(cbd.true, n=10,l=10, n.sim=1000)
  {
res=fillinKl(n=n,l=l)
sumBi=0
sumBi1=0
sumBi.exact=0
#cbd.true=cbd.exact(n)
cbd=compute.all.cbd(n,n.sim)
cbd1=compute.all.cbd1(n,n.sim)
#cbd.true=cbd.exact
#cbd=cbd.exact
for (i in 1:n) #go over all blocks except first one
  {
    #cbd[i+1,] is the row for Bi, d=0,1,...,n 
diff2=abs(sum(cbd[i+1,]*(res-1)))
  sumBi=sumBi+diff2

diff21=abs(sum(cbd1[i+1,]*(res-1)))
  sumBi1=sumBi1+diff21  

diff2.exact=abs(sum(cbd.true[i+1,]*(res-1)))
  sumBi.exact=sumBi.exact+diff2.exact  

}
sumBi=(sumBi+abs(res[1]-1))/2^n
sumBi1=(sumBi1+abs(res[1]-1))/2^n
sumBi.exact=(sumBi.exact+abs(res[1]-1))/2^n
return (list(sumBi.exact,sumBi,sumBi1))
}


#provides TV distance up to the L step
#dis2 is based on estimated cbd
#dis2.exact based on exact cbd
cvg.compare3<-function(cbd.true,n=10,L=20,n.sim=100){
    dis2.exact=rep(1,L)
      dis2=rep(1,L)
      dis21=rep(1,L)    
      for (l in 1:L) {
            d2=distancefrompi3(cbd.true,n,l,n.sim)
                dis2.exact[l]=d2[[1]]
                dis2[l]=d2[[2]]
                dis21[l]=d2[[3]]            
          }
    return(list(dis2/2, dis21/2, dis2.exact/2))
  }

n.sim = 50
n=20
L=40
b=cvg.compare3(cbd.true20,n,L,n.sim)

pdf(paste("distance.",n,".",L,".",n.sim,".pdf",sep=""))
plot((1:L),b[[1]],ylim=c(0,1),type="l",xlab="Number of MCMC interations (L)", ylab="d(L)")
lines((1:L),b[[2]],type="l",col="blue")
lines((1:L),b[[3]],type="l",col="red")
dev.off()



n.sim = 50
n=50
L=80
b=cvg.compare3(matrix(0,ncol=51,nrow=51),n,L,n.sim)

pdf(paste("distance.",n,".",L,".",n.sim,".pdf",sep=""))
plot((1:L),b[[1]],ylim=c(0,1),type="l",xlab="Number of MCMC interations (L)", ylab="d(L)")
lines((1:L),b[[2]],type="l",col="blue")
lines((1:L),b[[3]],type="l",col="red")
dev.off()




