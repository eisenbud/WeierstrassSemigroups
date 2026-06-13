
-*
. 
With this file we prove the following theorem with a Macaulay2 computation using Pinkham's Theorem:
Section 13 of   
Pinkham, Henry C.: Deformations of algebraic varieties with Gm action.
--     Astérisque 20, 1-131 (1974). 


Theorem. Semigroups of genus < 13 are Weierstrass.


Komeda, On the existence of Weierstrass gap sequences on curves of genus ≤8
   -- J. Pure Appl. Algebra 97, No. 1, 51-71 (1994).
established that every semigroup of genus < 8 is Weierstrass.

The file "smoothingFamiliesGenus89and10.dbm" contains smoothing families for all semigroups of genus 
g<11 which are not yet known to be Weierstrass. Checking flatness and smoothness 
establishes the Theorem.




In the second section we list the semigroups of genus <13 which are not yet known to be Weierstrass by
Komeda: On the existence of Weierstrass points whose first non-gaps are five,
    --                                              Manuscr. Math. 76, No. 2, 193-211 (1992),
Eisenbud, David; Harris, Joe: Existence, decomposition, and limits of certain Weierstrass points.
   -- Invent. Math. 87, 495-515 (1987), 
and
Pflueger, Nathan: On nonprimitive Weierstrass points.
   -- Algebra Number Theory 12, No. 8, 1923-1947 (2018). 
*-
needsPackage("NumericalSemigroups")
all8=findSemigroups 8;
#all8==67
toDoInGenus8=select(all8,L->not isKnownExample L)
#toDoInGenus8==9

all9=findSemigroups 9;
#all9==118
toDoInGenus9=select(all9,L->not isKnownExample L);
#toDoInGenus9==30

all10=findSemigroups 10;
#all10==204
toDoInGenus10=select(all10,L->not isKnownExample L);
#toDoInGenus10==77

all11=findSemigroups 11;
#all11==343

toDoInGenus11=select(all11,L->not isKnownExample L);
#toDoInGenus11==171
tally apply(toDoInGenus11,L->#L)

all12=findSemigroups 12;
#all12==592
toDoInGenus12=select(all12,L->not isKnownExample L);
#toDoInGenus12==345
tally apply(toDoInGenus12,L->#L)

toDoInGenusLessThan13=toDoInGenus8|toDoInGenus9|toDoInGenus10|toDoInGenus11|toDoInGenus12;
#toDoInGenusLessThan13==632
<<" tally of genera = " << tally apply(toDoInGenusLessThan13,L->genus L) <<endl

-*
In the following we read 116 smoothing families and check that these are families
have the desired semigroups.
*-
X="smoothingFamilies.dbm"
Y=openDatabase X
#keys Y==2*632

listOfIdeals=apply(toDoInGenusLessThan13,L->(R=value Y#(toString L|"ring");
	I=value (Y#(toString L|"ideal"))));
close Y
tally apply(listOfIdeals,I->isHomogeneous I)
listedSemigroups=apply(listOfIdeals,J->flatten drop(degrees ring J,-1));


-*
The ListOfIdeals contains a list of ideals fibz in rings R=QQ[x_0,x_i,z] for each semigroup L;

There are #L variables x_i with index as follows.
If m = min L, then the variables are indexed by x_i where i=j%m for j in L and have 
degree x_i=j. The last variables z has degree 1. 

The substitution z=>1 makes fibz into an ideal "fiber" for
which V(fiber) is an affine curve in AA^(#L). 
fibz can recovered from fiber by homogenizing with z. The family
        Spec (R/fibz) -> Spec QQ[z]
is flat.
We claim that the fiber is smooth and that the special fiber defined by fiber0=fibz+ideal z 
is the semigroup ideal.

By Pinkham's theorem 

Pinkham, Henry C.: Deformations of algebraic varieties with Gm action.
--     Astérisque 20, 1-131 (1974). 

this implies that all 345 semigroups are Weierstrass.
So every semigroup of genus 12 is Weierstrass.

To check is flatness is easy:
*-
elapsedTime flatnessTests=apply(listOfIdeals,J->(L=flatten drop(degrees ring J,-1);
	I=semigroupIdeal L;
	correctSpecialFiber = sub(J,vars ring I|matrix{{0}})==I;
	flat = betti res(J,LengthLimit=>2)== betti res(I,LengthLimit=>2);
        correctSpecialFiber and flat)); -- 46.4627s elapsed

<<"all families are flat = " << all flatnessTests <<endl
-- So all 632 families are flat.

-*
To check smoothness is computationally time consuming.
The key difficulty is that if the semigroup has a lot of generators then computing
the singular locus of the fibers requires computing a lot of large size minors of the jacobian matrix.
By semicontinuity, it suffices to compute fibers over fiber of ZZ/p for a sufficiently large prime p.
This helps to avoid the coefficient explosion over QQ. 

We check the smoothness with the functions

*-
smoothnessWithReductions=method(Options=>{Verbose=>0,"BaseField"=>ZZ/nextPrime 10^4})

smoothnessWithReductions(Ideal) := o -> J -> (
    L:= flatten drop(degrees ring J,-1);
    St:= ring J;
    fiber:=sub(J,last gens St =>1);   
    if char St > 0 then kk:=coefficientRing St else kk=o#"BaseField";
    ng:=numgens fiber;
        Sfinite:=kk[support fiber];
    fiberFinite:=sub(fiber,Sfinite);
    jac:=jacobian fiberFinite;
    if o.Verbose > 0 then <<"semigroup = "<< L << flush<<endl;
    I:=semigroupIdeal(L,"BaseField"=>o#"BaseField");
    nL:=#L;
    assert(dim fiberFinite==1);

colum := findCompleteIntersection(I,Strategy=>"front") ;
fewMinors := minors(#L-1,jac_colum,Strategy=>Cofactor);
    singF := trim (fiberFinite +ideal(gens fewMinors %fiberFinite));
if singF == ideal 1_Sfinite then return true;
if o.Verbose>1 then <<"dim and degree singF = "<< (dim singF,degree singF) <<endl;

colum = findCompleteIntersection(I,Strategy=>"back");
    fewMinors = minors(#L-1,jac_colum,Strategy=>Cofactor);
    singF = trim (singF +ideal(gens fewMinors %fiberFinite));
if singF == ideal 1_Sfinite then return true;
if o.Verbose>1 then  <<"dim and degree singF = "<< (dim singF,degree singF) <<endl;
   
colum = findCompleteIntersection(I,Strategy=>"random");
    fewMinors = minors(#L-1,jac_colum,Strategy=>Cofactor);
    singF = trim (singF +ideal(gens fewMinors %fiberFinite));
if singF == ideal 1_Sfinite then return true;
if o.Verbose>0 then
<<"dim and degree singF = "<< (dim singF,degree singF) <<endl;

if dim singF>0 then <<"no reduction to points " <<L <<endl;

if o.Verbose>1 then (
    <<"time to decompose: " <<endl;
    elapsedTime badPoints:=decompose singF;
    <<apply(badPoints,P->degree P)<<endl;
    ) else ( badPoints=decompose singF);
    SP:=null;jacP:=null;cok:=null;
    all(badPoints,P->(
	    if o.Verbose>1 then <<"degree P = " <<degree P <<endl;
	    SP=Sfinite/P;
    jacP=sub(jac,SP);
    cok=prune coker jacP;
    if o.Verbose>2 then (
	<< betti cok<<endl;);
    numgens cok == 1))
)


findCompleteIntersection=method(Options=>{Strategy=>"front"})

findCompleteIntersection(Ideal) := o -> I -> (
    ng:=numgens I;
    cd:=codim I;
    colum := {};
    ci:= ideal (gens I)_colum;ci1:=null;
   
    if o.Strategy=="front" then (
	a:=0;
	for i from 1 to cd do (
            while ( ci1=ci+ideal I_a;
                not codim ci1==i and a <ng-1) do (
		 a=a+1);
	    if a<ng then (colum = append(colum,a);
	    ci=ideal (gens I)_colum;
	    if a <ng-1 then a=a+1;
	    --<<colum<<endl;
	    );
	););

    if o.Strategy=="back" then (
	a=ng-1;
	for i from 1 to cd do (
	    while ( ci1=ci+ideal I_a;
                not codim ci1==i and a>0) do (
		 a=a-1);
	    if a>-1 then ((colum = append(colum,a);
	    ci=ideal (gens I)_colum;);
	    if a>0 then a=a-1;
	    --<<colum<<endl;
	    );
	);
    );
 
    if o.Strategy=="random" then (
       a= random ng;
       testValues:=toList(0..ng-1);
       for i from 1 to cd do (
	   while ( ci1=ci+ideal I_a;
                not codim ci1==i and #testValues >0) do (
		testValues=delete(a,testValues);
	        if #testValues>0 then a=testValues_(random( #testValues));
	    testValues=delete(a,testValues));
	    colum = append(colum,a);
	    ci=ideal (gens I)_colum;
	    --<<colum<<endl;	    
	    );
    );
    colum
    )



setRandomSeed("Want always the same computation")
elapsedTime smoothnessTests=apply(toList(0..#listOfIdeals-1),i->(
	J=listOfIdeals_i;
	--<<"case = " <<i<<endl;elapsedTime 
	smoothnessWithReductions(J,Verbose=>0))
    );

<<" all families are smoothings = " <<all smoothnessTests << endl



end--
restart
-- to load the following file and hence to very its title takes about 15 minutes
elapsedTime load "allSemigroupsOfGenusLessThan13AreWeierstrass.m2"


