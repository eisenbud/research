carpet=(kk,a,b)->(
     R:=kk[x_0..x_a,y_0..y_b,Degrees=>{{1,0,0}..{1,0,a},{0,1,0}..{0,1,b}}, Heft=>{1,1,0}];
     A:=map(R^{{0,0,0},{0,0,1}},R^(apply(a,i->{-1,0,-i})),matrix apply(2,j->apply(a,i->x_(i+j))));
     B:=map(R^{{0,0,0},{0,0,1}},R^(apply(b,i->{0,-1,-i})),matrix apply(2,j->apply(b,i->y_(i+j))));
     I:=minors(2,A)+minors(2,B);
     J:=ideal flatten apply(a-1,i->apply(b-1,j->(x_i*y_(j+2)+y_j*x_(i+2)-2*x_(i+1)*y_(j+1)) ));
     Is:=minors(2,A|B);
     (R,Is,I+J))

cdPart = (c,d,Fp) -> (
     --gets generators for the degree c,d part of the p-th step
     --of the trigraded complex F
     B := basis({c,d},Fp);
     B
)

reps =  sB -> (

     --input:
     --sB: a GL(2) free module, homogeneous with respect to 
     --Z(GL(2)),
     --with last degree being  the weight with respect to
     --G_m ++ 1.

     --output:
     --hash table whose keys are the degrees of the highest
     --weight vectors of the irreducibles, and corresponding
     --values are lists whose first element specifies
     --an irreducible SL(2) representation (d means Sym_d(kk^2))
     --and whose second number is the number of times the
     --irreducible representation appears.

T := tally sort ((degrees sB)/last);
if #keys T == 0 then return hashTable {};
m := min keys T; 
w := max keys T - min keys T ;
c := ceiling(w/2);
LT1 := for i from m to m+c list T#i;
LT := prepend(LT1#0, 
     for i from 1 to #LT1-1 list LT1#i -LT1#(i-1));
--tally reverse sort values new HashTable from Bt;
hashTable for i from 0 to c list (
     i+m => {w-2*(i), LT_i})
)

TEST///
kk=ZZ/101
(R,Is,J) = carpet(kk,3,3)
betti(Fs = res Is)
B = cdPart(3,1,Fs_3);
sB = source B
reps sB
assert(reps source cdPart(2,2,Fs_3) 
     === new HashTable from {3 => {6, 1}, 4 => {4, 2}, 5 => {2, 3}, 6 => {0, 1}})
///
end
restart
load "carpet3.m2"

kk=ZZ/101
(R,Is,J) = carpet(kk,3,3);
(R1,Is1,J1) = carpet(kk,3,2);

betti(Fs = res Is)
betti(Fs1 = res Is1)

reps source cdPart(2,2,Fs_3) 
reps source cdPart(2,2,Fs1_3) 

--
(R,Is,J) = carpet(kk,4,4);
(R1,Is1,J1) = carpet(kk,4,3);


betti(Fs = res Is)
betti(Fs1 = res Is1)

reps source cdPart(3,2,Fs_4) 
reps source cdPart(3,2,Fs1_4) 

betti(F = res J)
betti(F1 = res J1)

reps source cdPart(3,2,F_4) 
reps source cdPart(3,2,F1_4) 




