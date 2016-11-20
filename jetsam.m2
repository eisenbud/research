
The following code is now in CompleteIntersectionResoluttions.m2

BRanks1 = (ff,M) ->(
    --computes the last B-ranks that occur in the Layered resolution. Assumes M is an
    --S-module that is  MCM over R = S/(ideal ff)
    S := ring M;
    f := numcols ff;
    R' := S/ideal(ff_{0..f-2});
    M1' := R'** M;          
   (phi,psi) := approximation M1';
    M1 := pushForward(map(R',S),source phi);
   --note that in our situation both source psi and ker (phi|psi) will be free; thus
   --their ranks should be quick to compute.
   r:= rank ker (phi|psi);
   {M1, rank source psi, r}
    )
BRanks(Matrix,Module) := (ff,N) ->(
    --computes all the B-ranks that occur in the Layered resolution. 
    --as in MF, M is an MCM module over S/(ideal ff)
    S := ring ff;
    p := map(ring N, ring ff);
    M =  pushForward(p,N);
    c := numcols ff;
    N' := BRanks1(ff,M);
    Llast := {N'_1,N'_2};
    L := reverse apply(c-1, j->(
    N' = BRanks1(ff_{0..c-2-j},N'_0);
    {N'_1,N'_2}));
    L|{Llast}
    )
