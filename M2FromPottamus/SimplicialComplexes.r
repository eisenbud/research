is.subset = function(v1,v2){
	return(setequal(union(v1,v2),v2))}
#Could speed this up by keeping vectors sorted, then comparing
#initial strings.

sort.sets = function(L){
	# returns the list of vectors in L, but sorted by length,
	#longest first
	lengths = sapply(L,length)
	perm = order(lengths, decreasing=TRUE)
	return(L[perm])
	}
#from now on, assume that all lists of sets are sorted by descending length

L=list(1:7, 2:7, 3:8)

make.minimal = function(L){
	#Returns a list of the maximal elements of the list.
	n = length(L)
	Lnew = L
	thingsToDrop = rep(0,n)
	for (i in 1:(n-1)){
		for (j in (i+1):n){
			if (is.subset(L[[j]],L[[i]]))
			       {thingsToDrop[j]=1}
			   	}}
	for(i in n:1){
		if(thingsToDrop[i]==1){
			Lnew = Lnew[-i]}}
			return(Lnew)
			}
			
make.minimal.socle = function(L){
	#Returns a list of the minimal elements of the first list.
	n = length(L)
	Lnew = L
	thingsToDrop = rep(0,n)
	for (i in 1:(n-1)){
		for (j in (i+1):n){
			if (is.subset(L[[j]],L[[i]]))
			       {thingsToDrop[i]=1}
			   	}}
	for(i in n:1){
		if(thingsToDrop[i]==1){
			Lnew = Lnew[-i]}}
			return(Lnew)
			}
			
SC.non.minimal= list(1,2,c(2,3),c(3,4),c(4,1),c(1,3),1,2)
SCs=sort.sets(SC.non.minimal)

#A simplicial complex will be a list of facets, each a vector
SC =list(c(1,2), c(2,3), c(3,4),c(4,1), c(1,3))
#We will work with pairs, a simplicial complex and a list of
#its potential new facets (socle)
SocSC = list(c(1,2,3), c(1,3,4))
#A "simplicial complex pair":
S = list(SC, SocSC)

drop.facet = function(SC,i){
	#Drops the i-th facet from a simplicial complex,puts in
	#all the subsets, returns the minimal version
	SCnew = SC[-i]
	out = SC[[i]]
	for (j in (1:length(out))){
		SCnew = c(SCnew, list(out[-j]))
		}
		return(make.minimal(sort.sets(SCnew)))
	}

drop.facet(SC,1)
c(SC,list(s))

drop.facet.in.pair= function(S,i){
	SC = S[[1]]
	socle = S[[2]]
	SCnew = drop.facet(SC,i)
	out = SC[[i]]
	newSocle = c(socle,list(out))	
	return(list(SCnew,make.minimal.socle(newSocle)))
	}

add.facet = function(SC,simplex){
  #works for any simplex not already contained in the simplicial complex
  #specified by S. "simplex" is of course a vector.
  Snew = make.minimal(sort.sets(c(SC, list(simplex))))
  return(Snew)
}
SC
add.facet(SC,c(1,2,3))

is.element = function(L,v){
  sum(as.numeric(L==v))}

v=c(1:3, 5,7)
is.element(v,3)

L= list(1:2,2:5)
is.element
complement = function(v,n){
  #produces the vector whose elements are the complement of v in 1:n
  w=1:n
  for(i in n:1){
    if(is.element(v,i)){w=w[-i]}
               }
  return(w)
}

v=c(1:3, 5,7)
complement(v,8)

add.facet.in.pair = function(S, i,n){
  #S is a simplicial complex pair on the vertex set 1:n.
  #this function adds the i-th element of socle as a facet,
  #and adjusts the socle accordingly. 
  Socnew = S[[2]]
  out = S[[2]][[i]]
  Snew = add.facet(S[[1]], out)
  not.out = complement(out,n)
  for(i in not.out){
    count = 0
    for(j in out){
     if (is.element(Snew,c(out[-j],i))){count=count+1}
       }
    if(count == length(out)){Socnew = c(Socnew, as.list(c(out,i)))}
  }
  Socnew = make.minimal.socle(sort.sets(Socnew))
  return(c(Snew, Socnew))
}
S
add.facet.in.pair(S, 1,4)

