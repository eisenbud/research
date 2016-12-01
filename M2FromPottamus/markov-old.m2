loadPackage "RandomIdeal"
rsf = randomSquareFreeStep
{*rsf(Ideal, ZZ) := (I,n) ->(
     I1 := rsf I;
     for m from 2 to n do I1 = rsf I1;
     I1)
*}
rsfs = (I,n) ->(
     I1 := rsf I;
     for m from 2 to n do I1 = rsf I1;
     I1)

TV = (I,n,m) -> (
     T :=  tally for c from 1 to  m list first rsfs(I,n);
--     error();
     K := keys T;
     d := #K; 
     (.5)*sum(K, k-> abs((T#k)/m-1/d)))
TVbase = (m) -> (
     T :=  tally for c from 1 to  m list random(6);
--     error();
     K := keys T;
     d := #K; 
     (.5)*sum(K, k-> abs((T#k)/m-1/d)))

end
restart
load "markov.m2"
setRandomSeed currentTime()

S=kk[x,y]
I=ideal{1_S}
rsf I

--tally for c from 1 to 100 list first rsfs(I,10)

TVbase(1000)
for j from 5 to 10 do  print TV(I,j,1000)


S=kk[x,y,z]
I=ideal{1_S}
rsf I

--tally for c from 1 to 100 list first rsfs(I,10)

TVbase(500)
for j from 5 to 10 do  print TV(I,j*5,500)
