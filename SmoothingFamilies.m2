///
restart
needsPackage "SmoothingFamilies"
installPackage "SmoothingFamilies"
viewHelp "SmoothingFamilies"
///

newPackage(
         "SmoothingFamilies",
         Version => "0.1",
         Date => "April 20, 2026",
         Headline => "Compute smoothing families for Weierstrass semigroups",
         Authors => {{ Name => "David Eisenbud", Email => "de@berkeley.edu", HomePage => "http://eisenbud.github.io"},
	             { Name => "Frank-Olaf Schreyer", Email => "schreyer@math.uni-sb.de", HomePage => "https://www.math.uni-sb.de/ag/schreyer"}},
         Keywords => {" Weierstrass points"},
	 PackageExports => {"FastMinors",HomologicalAlgebraPackage,"Permutations","PrimaryDecomposition","AIWeierstrass"},--"NumericalSemigroups"
	 AuxiliaryFiles => false,
         DebuggingMode => true,
         )

     export {
	 "checkSmoothness",
	 "getSmoothingFamily",
	 --"getSmoothingFamilies",
         --"fasterBound",
	 --"produceSmoothingFamilies",
	 "solvingFlatteningRelations",
	 "isSmoothingFamily",
	 "clearDenominators",
	 "makeRange",
	 "appendFamily",
	 "getRangeOfOneParameterFamily",
	 "getParameterFamily",
	 "getOneParameterFamily",
	 "improveFamily",
	 --"isSmoothAffineCurve",
	 "findCompleteIntersection",
	 "smoothnessWithReductions",
	 "testBound",
	 "testCongruences",
	 "testRange",
	 "toDoList",
	 "sieveByBound",
	 "sieveByCongruences",
	 "sieveByRange",
	 -- option keys
	 "CoeffSize",
	 "CoeffBound",
	 "Congruence",
	 "Bound",
	 }

-* Code section *-

smoothnessWithReductions=method(Options=>{Verbose=>0,BaseField=>ZZ/nextPrime 10^4})

smoothnessWithReductions(Ideal) := o -> J -> (
    L:= flatten drop(degrees ring J,-1);
    St:= ring J;
    fiber:=sub(J,last gens St =>1);   
    if char St > 0 then kk:=coefficientRing St else kk=o.BaseField;
    ng:=numgens fiber;
        Sfinite:=kk[support fiber];
    fiberFinite:=sub(fiber,Sfinite);
    jac:=jacobian fiberFinite;
    if o.Verbose > 0 then <<"semigroup = "<< L << flush<<endl;
    I:=semigroupIdeal(L,BaseField=>o.BaseField);
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



-*
isSmoothAffineCurve=method(Options=>{Verbose=>0})

isSmoothAffineCurve(Ideal) := o -> J -> (
    L:= flatten drop(degrees ring J,-1);
    fiber:=sub(J,last gens ring J=>1);
    Sfinite:=(ZZ/nextPrime 15)[support fiber];
    fiberFinite:=sub(fiber,Sfinite);
    assert(dim fiberFinite==1);
    ng:=numgens fiber;
    <<"semigroup = "<< L << flush<<endl;
    jac:=jacobian fiberFinite;
    count:= 2;
    countMax:=min(2*floor(binomial(ng,#L-1)/3),400);
    colum:=toList(ng-#L..ng-1);
    assert(colum==#L-1);
    columSets:={colum};
    mat:=jac_colum;
    fewMinors:=minors(#L-1,mat,Strategy=>Cofactor);
    singF:=trim (fiberFinite+fewMinors);
    while  (
	while (
	    while (
		colum=sort apply(#L-1,i->random(ng));
		#(unique colum) < #L-1)
	    do ();
            member(colum,columSets))
	do ();
	columSets=append(columSets,colum);
	--if o.Verbose then (<<"size of columSets = " << #columSets <<flush<<endl);
	mat=jac_colum;
	fewMinors=minors(#L-1,mat,Strategy=>Cofactor);
	singF=trim(singF+fewMinors);
	columSets=append(columSets,colum);
	dim singF == 1) do (count=count+1);
    -- the while loop terminates
    --       because the the fiber has isolated singularities
    <<"count = " <<count <<endl;
    if singF == ideal 1_Sfinite then return true;
    badPoints:=decompose singF;
    <<"degree of components = " << apply(badPoints, P -> degree P) <<endl;
    SP:=null;jacP:=null;singP:=null;count1:=null;
    all(badPoints,P->(
	count1=count;	    
	SP=Sfinite/P;
	jacP=sub(jac,SP);
	
	singP=trim minors(#L-1,jacP,Strategy=>Cofactor);
	singP==ideal 1_SP)
    )
)
*-



improveFamily=method(Options=>{Verbose=>0})
improveFamily(Ideal) := o -> J -> (
    <<flush <<endl;
    L:= flatten drop(degrees ring J,-1);
    if o.Verbose >0 then << "semigroup = " << L <<endl;
    I:=semigroupIdeal(L,BaseField=>QQ);
    if o.Verbose >1 then elapsedTime (J1,family1):=getParameterFamily J else (
	(J1,family1)=getParameterFamily J);
    SJ := ring family1/sub(J1,ring family1);
    assert(betti syz sub(family1,SJ) == betti syz gens I);-- check flatness
    cJ1:=decompose J1;
    if o.Verbose >1 then <<"number of Components = "<<#cJ1 << endl;
    smooth:=null;fams:=null;fib0:=null;b:=null;
    while (
      fams=for J2 in cJ1 list (
	fib0=getOneParameterFamily(J,J2,family1,10);
	--"p=20 means one out of 20 coefficients is choosen to be nonzero"
	if o.Verbose >1 then (elapsedTime smooth=smoothnessWithReductions(fib0);
	     <<"smooth =" << smooth <<endl;) else (
	     smooth=smoothnessWithReductions(fib0); );
	if smooth then return fib0;
	(smooth,fib0));
      all(fams, (b,fib) ->not b)) do (<<"semigroup = " <<L <<" repeat" <<endl;);
    (b,fib0)=(select(fams,(b,fib)->b))_0;
    if o.Verbose >0 then <<"smooth = "<< b <<endl;
    fib0)

TEST ///
J=ListOfIdeals_169
elapsedTime improveFamily J
///

TEST ///

restart
needsPackage "SmoothingFamilies"
--X=openDatabase "SmoothingFamiliesGenus12.dbm"
W=openDatabase "allSmoothingFamiliesInGenus12.dbm"
--#keys X
--keysX=keys X;
#keys W


LL12=findSemigroups 12;
#LL12
LL12toDo=select(LL12,L->not knownExample L);
#LL12toDo
LL344=select(LL12toDo,L->L != {9, 10, 13, 14, 15, 17});
#LL344


ListOfIdeals=apply(LL344,L->(R=value W#(toString L|"ring");I=value (W#(toString L|"ideal"))));

--ListOfIdeals=for L in LL344 list try (R=value W#(toString L|"ring");I=value (W#(toString L|"ideal")))else continue;
--#oo
-*
elapsedTime tally apply(ListOfIdeals,J->(L=flatten drop(degrees ring J,-1);
   betti res J == betti res semigroupIdeal L))  -- 183.366s elapsed

failures={}
elapsedTime tally apply(#ListOfIdeals,i->(J=ListOfIdeals_i;
	L=flatten drop(degrees ring J,-1);
	elapsedTime (smooth=smoothnessWithReductions J;
	    <<" case = " << i << " semigroup = " << L <<", smooth= " << smooth <<endl;);
	if not smooth then failures = append(failures, i);smooth)) -- 840.458s elapsed
failures
failures1={5, 202, 289}
*-

position(LL344,L->L=={7, 10, 13, 18, 19, 22})
J=ListOfIdeals_62
Sz=ring J
L=flatten drop(degrees  Sz ,-1)
elapsedTime (base2,fam1)=getParameterFamily J;
#support fam1
#support base2+#L
base2
elapsedTime cbase2=decompose base2;
apply(cbase2,c->(codim c, numgens c))
elapsedTime J1=improveFamily J
J1_*/size
J_*/size
J2=improveFamily J1
J2_*/size
(base3,fam2)=getParameterFamily J2;
#support fam1
#support fam2
#support base3+#L
fam2
J=ListOfIdeals_10
getRangeOfOneParameterFamily J


J=ListOfIdeals_300
(J2,fam1)=getParameterFamily J
Sz=ring J
L=flatten drop(degrees  Sz ,-1)
(gens ring J2)/degree

elapsedTime J =  improveFamily J
(J2,fam1)=getParameterFamily improveFamily J
Sz=ring J2
L=flatten drop(degrees  Sz ,-1)
(gens ring J2)/degree
gens ring J2

triples = {}
JJ = ListOfIdeals;
elapsedTime for i from 0 to #JJ -1 do(
--    <<(i,JJ_i)<<endl;
    J := JJ_i;
    elapsedTime (J2,fam) := getParameterFamily J;
    Sz := ring J;
    L := flatten drop(degrees Sz, -1);
    <<(i,L)<<endl<<flush;
    triples = append(triples, {J,J2,fam});
    )

improvedTriples = {}
elapsedTime for i from 0 to #triples -1 do(
    J := JJ_i;
    elapsedTime (J2,fam1) = getParameterFamily improveFamily J;
    Sz = ring J;
    L = flatten drop(degrees Sz, -1);
    <<(i,L,#gens ring triples_i_1, #gens ring J2 )<<endl<<flush;
    improvedTriples = append(improvedTriples, {J,J2,fam1});
    )

netList for i from 0 to length improvedTriples -1 list
t = triples_i;
t1 = improvedTriples_i;
{(gens ring t_1)/degree, (gens ring t1_1)/degree}
--seems no improvements; occasionally the "improved" on is larger.

goodDegrees12 = {}
elapsedTime for i from 0 to #triples -1 do (
    goodDegrees12 = append(goodDegrees12,
	{drop((gens ring t_0)/degree, -1), (gens ring t_1/degree)});
    )
netList goodDegrees12


///

getRangeOfOneParameterFamily=method()
getRangeOfOneParameterFamily(Ideal):= J -> (
    Sz:=ring J;
    L:=flatten drop(degrees  Sz ,-1);
    I:=semigroupIdeal(L,BaseField=>QQ);
    (A,unfolding):=makeUnfolding I;
    SA:=ring unfolding;
    z:=last gens ring J;
    eq:=null;termsOfeq:=null;termsOfEq:=null;usedMonomials:=null;
    varsList:=flatten for i from 0 to rank source unfolding-1 list (
	eq=J_i;
	termsOfeq=transpose (coefficients(eq,Variables=>{z}))_1;
	termsOfEq=termsOfeq_{0..rank source termsOfeq-2};
	usedMonomials=sub((coefficients termsOfEq)_0,SA);
	(entries sub(contract(usedMonomials,unfolding_{i}),A))_0
    );
    sort unique(varsList/degree))


getParameterFamily=method()
getParameterFamily(Ideal):= J -> (
    Sz:=ring J;
    L:=flatten drop(degrees  Sz ,-1);
    I:=semigroupIdeal(L,BaseField=>QQ);
    (A,unfolding):=makeUnfolding I;
    SA:=ring unfolding;
    z:=last gens ring J;
    eq:=null;termsOfeq:=null;termsOfEq:=null;usedMonomials:=null;
    varsList:=flatten for i from 0 to rank source unfolding-1 list (
	eq=J_i;
	termsOfeq=transpose (coefficients(eq,Variables=>{z}))_1;
	termsOfEq=termsOfeq_{0..rank source termsOfeq-2};
	usedMonomials=sub((coefficients termsOfEq)_0,SA);
	(entries sub(contract(usedMonomials,unfolding_{i}),A))_0
    );
   posList:=apply(varsList,a->position(gens A,b->a==b));
   (A1,runf):=restrictedUnfolding(I,posList);
   J1:=trim flatteningRelations(I,A1,runf);
   fam1:=runf%sub(J1,ring runf);
   J2:=ideal prune(A1/J1) ;
   SJ:= ring fam1/sub(J2,ring fam1);
   assert(betti syz sub(fam1,SJ) == betti syz gens I);
   (J2,fam1)
   )

getOneParameterFamily=method(Options=>{CoeffSize=>1, Verbose => 0})
getOneParameterFamily(Ideal,Ideal,Matrix,ZZ) := o -> (J,J2,family1,p) -> (
	 family2:=family1%sub(J2,ring family1);
	 Sz := ring J;
	 c:=1;--o.CoeffSize;
	 SA:=QQ[support family2,Degrees=>apply(support family2,a->degree a)];
	 family2=sub(family2,SA);
	 I':=semigroupIdeal(flatten drop(degrees ring J,-1) ,BaseField=>QQ);
         S:=ring I';
	 if J2 != 0 then (
		
	    J3:=trim flatteningRelations(I',ring family2,family2);
	    if o.Verbose >0 then <<"codim J3 = " << codim J3 <<", numgens J3 = "<< numgens J3 <<endl;        
	    cd:=codim J3;
	    J3a:=ideal (gens J3)_{0..cd-1};
	    avars:=support J3;
	    Lvars:=subsets(avars,cd);
	    Lvarsc:=apply(Lvars, va->select(avars,av->not member(av,va)));
	    pos:=select(Lvarsc,va->gens J3a%sub(ideal va,ring J3a)==0);
	    eq1:=null; eq2:=null;
	    
	    posa:=select(pos,pos1-> (
		    eq1=sub(ideal apply(pos1,m->m-random(2*c-1)-c),ring J3);
		    eq2=ideal (gens J3a%sub(eq1,ring J3));
		    eq2 !=ideal(1_(ring eq2))));
	     <<"#pos = " <<#pos<<", #posa = "<<#posa<<endl;
	     if #posa == 0 then (<<"solving approach did not work" <<endl;return (false,null));
	     j:=0;
	     while (
		 eq1=sub(ideal apply( posa_j,m->m-random(2*c-1)-c),ring J3);
		 eq2=ideal (gens J3%sub(eq1,ring J3));
	         eq:=eq1+eq2;
		not all apply(support J3,m->dim ideal (m%eq)==-1) and j< #posa-1) do j=j+1;
	     if j == #posa then return (null);
	     if not gens J3%eq ==0 or dim eq == -1 then (
	         << "condition 2 of solving approach is not satisfied" <<endl;
		 return null;);
	     fiber1:=family2%sub(eq,ring family2);	    
	     ) else
	 fiber1=family2;
	 --gens ring family2
	 --support fiber1, gens ring family2
	     fiber:=sub(fiber1,vars S|
		    matrix { apply(
			    #gens ring family2 - numgens S
			    ,i->
			    if random(p)>1 then 0 else random(2*c-1)-c)}
		    );

	     fib:=ideal homogenize(sub(fiber, Sz),last gens Sz);
 
             assert(betti res fib == betti res J);
	     fib)

testBound=method(Options=>{Verbose=>0,CoeffSize=>1})
testBound(List,ZZ) := o -> (L,b) -> (
	range:=drop(makeRange(L,{1}),b);
        A:=getSmoothingFamily(L,range,CoeffSize=>o.CoeffSize)
	)

testCongruences=method(Options=>{Verbose=>0,CoeffSize=>1})
testCongruences(List,List) := o -> (L,congruences) -> (
	range:= makeRange(L,congruences);
        A:=getSmoothingFamily(L,range,CoeffSize=>o.CoeffSize)
	)

testRange=method(Options=>{Verbose=>0,CoeffSize=>1})
testRange(List,List) := o -> (L,range) -> (
        A:=getSmoothingFamily(L,range,CoeffSize=>o.CoeffSize)
	)


    
TEST///
toDoInGenus12=toDoList 12;
#toDoInGenus12
L=first toDoInGenus12
elapsedTime testBound(L,12)

L=last toDoInGenus12
elapsedTime A=testBound(L,12);A_0

L=toDoInGenus12_342
elapsedTime A=testBound(L,12);A_0
b=11
elapsedTime while ( A=testBound(L,b); not A_0 and b>0) do (b=b-1)
b

L=toDoInGenus12_244
elapsedTime A=testBound(L,8);A_0

b=12
elapsedTime while ( A=testBound(L,b); not A_0 and b>0) do (b=b-1)
b

L=toDoInGenus12_245
elapsedTime A=testBound(L,6);A_0

///

TEST///
restart
needsPackage "SmoothingFamilies"
LL=toDoList 11;
b=11
--sieveByBound(LL,b,"fam11a","fam11a.dbm")
L=LL_1
A=testBound(L,b)
name="fam11a"
openOutAppend name;
    name<<L;
    name << ", ";
    name<<close;
    dataName="fam11a.dbm"
    familyData:=openDatabaseOut dataName;
    familyData#(toString L|"ring") = toExternalString (ring A_1); 
    familyData#(toString L|"ideal") = toString (A_1);
    close familyData;
X="fam11a.dbm"
Y=openDatabase X
#keys Y
keys Y
R=value Y#((keys Y)_1)
J=value (Y#((keys Y)_0))
betti res J
close Y
X="fam11a.dbm"
Y=openDatabaseOut X
close Y
b=10
elapsedTime sieveByBound(LL,b,"fam11a","fam11a.dbm")

done11=getFromDisk"fam11a";#done11
run "rm fam11a"
run "rm fam11a.dbm"
///

TEST ///
restart
needsPackage "SmoothingFamilies"

LL=toDoList 12;
b=12

--run "rm smoothingFamiliesGenus12.dbm"
--run "rm fam12sieving"
--sieveByBound(LL,b,"fam12sieving","smoothingFamiliesGenus12.dbm")
L=LL_0
A=testBound(L,b)
name="fam12sieving"
openOutAppend name;
    name<<L;
    name << ", ";
    name<<close;
dataName="smoothingFamiliesGenus12.dbm"
    familyData:=openDatabaseOut dataName;
    familyData#(toString L|"ring") = toExternalString (ring A_1); 
    familyData#(toString L|"ideal") = toString (A_1);
    close familyData;

Y=openDatabase dataName
#keys Y
keys Y
R=value Y#((keys Y)_1)
J=value (Y#((keys Y)_0))
betti res J
close Y

///
TEST///
restart
needsPackage "SmoothingFamilies"

LL=toDoList 12;
LL12difficult={{7, 10, 13, 16, 19, 22, 25},{10, 12, 14, 15, 16, 17, 18, 19, 21},
	{10, 11, 14, 15, 16, 17, 18, 19}}
b=12
elapsedTime sieveByBound(LL12difficult,b+3,"fam12sieving","smoothingFamiliesGenus12.dbm")
LL12difficult'={{10, 12, 14, 15, 16, 17, 18, 19, 21},
	{10, 11, 14, 15, 16, 17, 18, 19},{8, 11, 12, 15, 18, 21, 25},{10, 11, 13, 14, 16, 17, 19}}
caseNumber=position(LL,L->L==last LL12difficult')
LL'=drop(LL,caseNumber+1);first LL'
LL'=select(LL,L-> not member(L, LL12difficult));#LL'

b=12
elapsedTime sieveByBound(LL',b,"fam12sieving","smoothingFamiliesGenus12.dbm")
elapsedTime sieveByBound(LL',b-1,"fam12sieving","smoothingFamiliesGenus12.dbm")
elapsedTime sieveByBound(LL',b-2,"fam12sieving","smoothingFamiliesGenus12.dbm")

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{8, 11, 12, 15, 18, 21, 25},{9, 10, 14, 15, 16, 17, 22},
    {9, 12, 14, 15, 16, 17, 19, 20},{9, 10, 11, 16, 17, 23, 24},{9, 10, 12, 14, 17, 25},
    {10, 12, 14, 15, 16, 17, 18, 19, 21}, {10, 11, 14, 15, 16, 17, 18, 19},
    {10, 11, 13, 14, 15, 18, 19},{10, 11, 13, 14, 16, 17, 19},{11, 12, 13, 14, 15, 16, 18, 20, 21}}
caseNumber=position(LL,L->L==last LL12difficult)
LL'=drop(LL,caseNumber+1);first LL'
elapsedTime sieveByBound(LL',b-3,"fam12sieving","smoothingFamiliesGenus12.dbm")

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{6, 9, 17, 19, 20, 22},{6, 9, 16, 19, 20, 23},
    {7, 9, 13, 19, 24},{8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},
    {9, 10, 14, 15, 16, 17, 22},{9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 14, 15, 16, 17, 19, 20}}
caseNumber=position(LL,L->L==last LL12difficult)
LL'=drop(LL,caseNumber+1);first LL'
elapsedTime sieveByBound(LL',b-4,"fam12sieving","smoothingFamiliesGenus12.dbm")

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL'={{9, 11, 12, 14, 16, 19}, {10, 11, 13, 14, 15, 16, 17}}--,{10, 11, 13, 15, 16, 17, 18}
elapsedTime sieveByBound(LL',b+2,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>4)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{8, 11, 12, 15, 18, 21, 25},{9, 10, 11, 16, 17, 23, 24},
    {9, 10, 13, 14, 16, 21},{10, 12, 14, 15, 16, 17, 18, 19, 21},
    {10, 11, 14, 15, 16, 17, 18, 19}}
LL'={{10, 11, 13, 14, 15, 18, 19},{10, 12, 13, 14, 15, 16, 18, 21}}
caseNumber=position(LL,L->L==last LL12difficult)
LL'=drop(LL,caseNumber+1);first LL'
elapsedTime sieveByBound(LL',b-2,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{7, 9, 13, 19, 24}, {7, 11, 15, 16, 17, 19},{8, 9, 14, 15, 20, 21},
    {8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},{8, 11, 12, 15, 17, 21}}
LL'={} --{7, 8, 12, 25}
caseNumber=position(LL,L->L==last LL12difficult)
LL'=drop(LL,caseNumber+1);first LL'
elapsedTime sieveByBound(LL',b-5,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
done=getFromDisk("fam12sieving");#done
X=openDatabase "smoothingFamiliesGenus12.dbm"
#keys X
close X

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{6, 9, 17, 19, 20, 22},{6, 9, 16, 19, 20, 23},{6, 8, 19, 21, 23},
    {7, 9, 13, 19, 24},{7, 11, 15, 16, 17, 19},{8, 9, 14, 15, 20, 21},
    {8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},{8, 11, 12, 15, 17, 21},
    {8, 10, 12, 14, 17, 21, 23},{8, 9, 11, 21, 23},{9, 11, 14, 15, 16, 17, 19},
    {9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 11, 12, 15, 16, 17}, {9, 12, 13, 14, 16, 17, 20},{9, 11, 13, 14, 16, 17, 19},
    {9, 10, 11, 16, 17, 23, 24},{9, 12, 13, 14, 15, 17, 19},{9, 10, 12, 14, 17, 25},
    {9, 10, 12, 15, 16, 23}, {9, 10, 13, 14, 16, 21},{9, 10, 13, 14, 15, 21},
    {10, 12, 14, 15, 16, 17, 18, 19, 21},{10, 11, 14, 15, 16, 17, 18, 19},
    {10, 12, 13, 14, 16, 17, 18, 19},{10, 12, 13, 14, 15, 17, 18, 19},
    {10, 11, 12, 14, 15, 18, 19},{10, 11, 12, 15, 16, 17, 19},{10, 11, 12, 14, 16, 17, 19},
    {10, 11, 13, 14, 15, 17, 19},{10, 11, 12, 14, 15, 17, 19},{10, 11, 13, 15, 16, 17, 18},
    {10, 11, 12, 15, 16, 17, 18},{10, 11, 13, 14, 16, 17, 18},{10, 12, 13, 14, 15, 17, 18, 21},
    {11, 12, 13, 14, 15, 17, 18, 20, 21},{11, 12, 13, 14, 15, 16, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 19, 21},{11, 12, 13, 14, 15, 16, 17, 18, 20}};
#LL12difficult
caseNumber=position(LL,L->L==last LL12difficult)
LL'=drop(LL,caseNumber+1);first LL'
LLnoclearing={{7, 8, 12, 25},{9, 12, 13, 14, 15, 16, 20},{9, 12, 13, 14, 15, 16, 19},
    {10, 11, 12, 13, 16, 17, 18},{10, 11, 12, 14, 15, 16, 17}}
LLrepeat={{8, 9, 12, 13, 19}}
elapsedTime sieveByBound(LL',b-6,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
elapsedTime sieveByBound(LLrepeat,b-6,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>3)
elapsedTime sieveByBound(LLnoclearing,b-6,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>1)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{6, 9, 17, 19, 20, 22},{6, 9, 16, 19, 20, 23},{6, 8, 19, 21, 23},
    {7, 9, 13, 19, 24},{7, 11, 15, 16, 17, 19},{8, 9, 14, 15, 20, 21},
    {8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},{8, 11, 12, 15, 17, 21},
    {8, 10, 12, 14, 17, 21, 23},{8, 9, 11, 21, 23},{8, 9, 12, 13, 23},{9, 11, 14, 15, 16, 17, 19},
    {9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 11, 12, 15, 16, 17}, {9, 12, 13, 14, 16, 17, 20},{9, 11, 13, 14, 16, 17, 19},
    {9, 10, 11, 16, 17, 23, 24},{9, 12, 13, 14, 15, 17, 19},{9, 10, 12, 14, 17, 25},
    {9, 10, 12, 15, 16, 23}, {9, 10, 13, 14, 16, 21},{9, 10, 13, 14, 15, 21},
    {9, 10, 13, 14, 15, 17},{10, 12, 14, 15, 16, 17, 18, 19, 21},{10, 11, 14, 15, 16, 17, 18, 19},
    {10, 12, 13, 14, 16, 17, 18, 19},{10, 12, 13, 14, 15, 17, 18, 19},
    {10, 11, 12, 14, 15, 18, 19},{10, 11, 12, 15, 16, 17, 19},{10, 11, 12, 14, 16, 17, 19},
    {10, 11, 13, 14, 15, 17, 19},{10, 11, 12, 14, 15, 17, 19},{10, 11, 13, 15, 16, 17, 18},
    {10, 11, 12, 15, 16, 17, 18},{10, 11, 13, 14, 16, 17, 18},{10, 12, 13, 14, 15, 17, 18, 21},
    {11, 12, 13, 14, 15, 17, 18, 20, 21},{11, 12, 13, 14, 15, 16, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 19, 21},{11, 12, 13, 14, 15, 16, 17, 18, 20}};
#LL12difficult

LL'=select(LL,L->not member(L,LL12difficult));
elapsedTime sieveByBound(LL',b-7,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
elapsedTime sieveByBound(LL',b-8,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
elapsedTime sieveByBound(LL',b-9,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{6, 9, 17, 19, 20, 22},{6, 9, 16, 19, 20, 23},{6, 8, 19, 21, 23},
    {7, 9, 13, 19, 24},{7, 11, 15, 16, 17, 19},{8, 9, 14, 15, 20, 21},
    {8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},{8, 11, 12, 15, 17, 21},
    {8, 10, 12, 14, 17, 21, 23},{8, 9, 11, 21, 23},{8, 9, 12, 13, 23},{9, 11, 14, 15, 16, 17, 19},
    {9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 11, 12, 15, 16, 17}, {9, 12, 13, 14, 16, 17, 20},{9, 11, 13, 14, 16, 17, 19},
    {9, 10, 11, 16, 17, 23, 24},{9, 12, 13, 14, 15, 17, 19},{9, 10, 12, 14, 17, 25},
    {9, 10, 12, 15, 16, 23}, {9, 10, 13, 14, 16, 21},{9, 10, 13, 14, 15, 21},
    {9, 10, 13, 14, 15, 17},{10, 12, 14, 15, 16, 17, 18, 19, 21},{10, 11, 14, 15, 16, 17, 18, 19},
    {10, 12, 13, 14, 16, 17, 18, 19},{10, 12, 13, 14, 15, 17, 18, 19},
    {10, 11, 12, 14, 15, 18, 19},{10, 11, 12, 15, 16, 17, 19},{10, 11, 12, 14, 16, 17, 19},
    {10, 11, 13, 14, 15, 17, 19},{10, 11, 12, 14, 15, 17, 19},{10, 11, 13, 15, 16, 17, 18},
    {10, 11, 12, 15, 16, 17, 18},{10, 11, 13, 14, 16, 17, 18},{10, 12, 13, 14, 15, 17, 18, 21},
    {11, 12, 13, 14, 15, 17, 18, 20, 21},{11, 12, 13, 14, 15, 16, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 19, 21},{11, 12, 13, 14, 15, 16, 17, 18, 20}};
LL'=LL12difficult;#LL'
LL'12difficult6={{11, 12, 13, 14, 15, 16, 18, 20, 21}}
caseNumber=position(LL',L->L==last LL'12difficult6)
LL'=drop(LL',caseNumber+1);first LL'
congruences={6}
elapsedTime sieveByCongruences(LL',congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
LLnoClearing6={{8, 11, 12, 15, 18, 21, 25}}
LLrepeat6={{9, 12, 13, 14, 16, 17, 20}}
elapsedTime sieveByCongruences(LLnoClearing6,congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>1)
elapsedTime sieveByCongruences(LLrepeat6,congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>6)


restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
b=12
LL12difficult={{6, 9, 17, 19, 20, 22},{6, 9, 16, 19, 20, 23},{6, 8, 19, 21, 23},
    {7, 9, 13, 19, 24},{7, 11, 15, 16, 17, 19},{8, 9, 14, 15, 20, 21},
    {8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},{8, 11, 12, 15, 17, 21},
    {8, 10, 12, 14, 17, 21, 23},{8, 9, 11, 21, 23},{8, 9, 12, 13, 23},{9, 11, 14, 15, 16, 17, 19},
    {9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 11, 12, 15, 16, 17}, {9, 12, 13, 14, 16, 17, 20},{9, 11, 13, 14, 16, 17, 19},
    {9, 10, 11, 16, 17, 23, 24},{9, 12, 13, 14, 15, 17, 19},{9, 10, 12, 14, 17, 25},
    {9, 10, 12, 15, 16, 23}, {9, 10, 13, 14, 16, 21},{9, 10, 13, 14, 15, 21},
    {9, 10, 13, 14, 15, 17},{10, 12, 14, 15, 16, 17, 18, 19, 21},{10, 11, 14, 15, 16, 17, 18, 19},
    {10, 12, 13, 14, 16, 17, 18, 19},{10, 12, 13, 14, 15, 17, 18, 19},
    {10, 11, 12, 14, 15, 18, 19},{10, 11, 12, 15, 16, 17, 19},{10, 11, 12, 14, 16, 17, 19},
    {10, 11, 13, 14, 15, 17, 19},{10, 11, 12, 14, 15, 17, 19},{10, 11, 13, 15, 16, 17, 18},
    {10, 11, 12, 15, 16, 17, 18},{10, 11, 13, 14, 16, 17, 18},{10, 12, 13, 14, 15, 17, 18, 21},
    {11, 12, 13, 14, 15, 17, 18, 20, 21},{11, 12, 13, 14, 15, 16, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 19, 21},{11, 12, 13, 14, 15, 16, 17, 18, 20}};
LL'=LL12difficult;#LL'
LL'12difficult5={{9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 10, 11, 16, 17, 23, 24},{9, 10, 12, 14, 17, 25},{11, 12, 13, 14, 15, 17, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 20, 21}}
caseNumber=position(LL',L->L==last LL'12difficult5)
LL'=drop(LL',caseNumber+1);first LL'
congruences={5}
elapsedTime sieveByCongruences(LL',congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)


restart
needsPackage "SmoothingFamilies"
congruences={5,6,11} -- to be done again
LL=toDoList 12;
b=12
LL12difficult={{6, 9, 17, 19, 20, 22},{6, 9, 16, 19, 20, 23},{6, 8, 19, 21, 23},
    {7, 9, 13, 19, 24},{7, 11, 15, 16, 17, 19},{8, 9, 14, 15, 20, 21},
    {8, 10, 13, 15, 19, 22},{8, 11, 12, 15, 18, 21, 25},{8, 11, 12, 15, 17, 21},
    {8, 10, 12, 14, 17, 21, 23},{8, 9, 11, 21, 23},{8, 9, 12, 13, 23},{9, 11, 14, 15, 16, 17, 19},
    {9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 11, 12, 15, 16, 17}, {9, 12, 13, 14, 16, 17, 20},{9, 11, 13, 14, 16, 17, 19},
    {9, 10, 11, 16, 17, 23, 24},{9, 12, 13, 14, 15, 17, 19},{9, 10, 12, 14, 17, 25},
    {9, 10, 12, 15, 16, 23}, {9, 10, 13, 14, 16, 21},{9, 10, 13, 14, 15, 21},
    {9, 10, 13, 14, 15, 17},{10, 12, 14, 15, 16, 17, 18, 19, 21},{10, 11, 14, 15, 16, 17, 18, 19},
    {10, 12, 13, 14, 16, 17, 18, 19},{10, 12, 13, 14, 15, 17, 18, 19},
    {10, 11, 12, 14, 15, 18, 19},{10, 11, 12, 15, 16, 17, 19},{10, 11, 12, 14, 16, 17, 19},
    {10, 11, 13, 14, 15, 17, 19},{10, 11, 12, 14, 15, 17, 19},{10, 11, 13, 15, 16, 17, 18},
    {10, 11, 12, 15, 16, 17, 18},{10, 11, 13, 14, 16, 17, 18},{10, 12, 13, 14, 15, 17, 18, 21},
    {11, 12, 13, 14, 15, 17, 18, 20, 21},{11, 12, 13, 14, 15, 16, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 19, 21},{11, 12, 13, 14, 15, 16, 17, 18, 20}};
LL'=LL12difficult;#LL'
LL'12difficult56={{9, 12, 14, 15, 16, 17, 19, 20},{9, 12, 13, 15, 16, 17, 19, 23},
    {9, 10, 11, 16, 17, 23, 24},{9, 10, 12, 14, 17, 25},{11, 12, 13, 14, 15, 17, 18, 20, 21},
    {11, 12, 13, 14, 15, 16, 18, 20, 21}}
LL'=select(LL',L->not member(L,LL'12difficult56));#LL'
--LL12difficult56={}
--caseNumber=position(LL',L->L==last LL12difficult56)
--LL'=drop(LL',caseNumber+1);first LL'
congruences={5,6,11}
elapsedTime sieveByCongruences(LL',congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
congruences={7} -- no new cases
LL=toDoList 12;
LL12done=getFromDisk("fam12sieving");
LL12toDo=select(LL,L->not member(L,LL12done))
#LL12toDo
tally apply(LL12toDo,L->min L)
elapsedTime sieveByCongruences(LL12toDo,congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
congruences={8,12} 
LL=toDoList 12;
LL12done=getFromDisk("fam12sieving");
LL12toDo=select(LL,L->not member(L,LL12done))
#LL12toDo
tally apply(LL12toDo,L->min L)
elapsedTime sieveByCongruences(LL12toDo,congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
LL12done=getFromDisk("fam12sieving");
LL12toDo=select(LL,L->not member(L,LL12done))
#LL12toDo
tally apply(LL12toDo,L->min L)
congruences={4}
--{{6, 8, 19, 21, 23}} 
elapsedTime sieveByCongruences(LL12toDo_{30..30},congruences,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>1)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
LL12done=getFromDisk("fam12sieving");
LL12toDo=select(LL,L->not member(L,LL12done))
#LL12toDo
tally apply(LL12toDo,L->min L)
--range=6*toList(1..3)|5*toList(1..4)|{11}
range=4*toList(1..3)|5*toList(1..2)|{9}
elapsedTime sieveByRange(LL12toDo_{0..29},range,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)

restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
LL12done=getFromDisk("fam12sieving");
LL12toDo=select(LL,L->not member(L,LL12done))
#LL12toDo
tally apply(LL12toDo,L->min L)
--range=6*toList(1..3)|5*toList(1..4)|{11}
--range=4*toList(1..3)|5*toList(1..2)|{9}
--elapsedTime sieveByBound(LL12toDo_{0..1},8,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
range=toList(6..23)
range=toList(6,7)|toList(12..14)|toList(18..21)
elapsedTime sieveByRange(LL12toDo_{0..1},range,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
elapsedTime sieveByCongruences(LL12toDo_{0},{5,6,11},"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
elapsedTime sieveByRange(LL12toDo_{0},{3,6,9,12},"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
L={6, 9, 17, 19, 20, 22}
--degreeMatrices L
restart
needsPackage "SmoothingFamilies"
LL=toDoList 12;
LL12done=getFromDisk("fam12sieving");
LL12toDo=select(LL,L->not member(L,LL12done))
#LL12toDo
tally apply(LL12toDo,L->min L)
range=6*toList(1..3)|5*toList(1..4)|{11}
range=6*toList(1..2)|5*toList(1..2)|{11}
elapsedTime sieveByRange(LL12toDo_{2..32},range,"fam12sieving","smoothingFamiliesGenus12.dbm",CoeffSize=>2)
///

sieveByBound=method(Options=>{Verbose=>0,CoeffSize=>1})

sieveByBound(List,ZZ,String,String) := o -> (LL,b,done,doneData) -> (
    alreadyDone := getFromDisk (done);
    LLStillToDo:=select(LL,L->not member(L, alreadyDone));
    A:=null;L:=null;
    apply(#LLStillToDo, i -> (L=LLStillToDo_i;
	    <<endl;
	    << "case " << i <<" from " <<#LLStillToDo <<", semigroup = " << L <<endl;
	    elapsedTime A=testBound(L,b,CoeffSize=>o.CoeffSize);
	    if A_0 then appendFamily(L,A_1,done,doneData)));
    )

sieveByCongruences=method(Options=>{Verbose=>0,CoeffSize=>1})

sieveByCongruences(List,List,String,String) := o -> (LL,congruences,done,doneData) -> (
    alreadyDone := getFromDisk (done);
    LLStillToDo:=select(LL,L->not member(L, alreadyDone));
    A:=null;L:=null;
    apply(#LLStillToDo, i -> (L=LLStillToDo_i;
	    <<endl;
	    << "case " << i <<" from " <<#LLStillToDo <<", semigroup = " << L <<endl;
	    elapsedTime A=testCongruences(L,congruences,CoeffSize=>o.CoeffSize);
	    if A_0 then appendFamily(L,A_1,done,doneData)));
    )

sieveByRange=method(Options=>{Verbose=>0,CoeffSize=>1})

sieveByRange(List,List,String,String) := o -> (LL,range,done,doneData) -> (
    alreadyDone := getFromDisk (done);
    LLStillToDo:=select(LL,L->not member(L, alreadyDone));
    A:=null;L:=null;
    apply(#LLStillToDo, i -> (L=LLStillToDo_i;
	    <<endl;
	    << "case " << i <<" from " <<#LLStillToDo <<", semigroup = " << L <<endl;
	    elapsedTime A=testRange(L,range,CoeffSize=>o.CoeffSize);
	    if A_0 then appendFamily(L,A_1,done,doneData)));
    )

toDoList=method()
toDoList(ZZ) := g -> (
    allg:=findSemigroups g;
    select(allg,L->not knownExample L)
    )



-*
fasterBound=method(Options=>{Verbose=>false,Congruence=>false})
fasterBound(List):= o -> L -> (
    g:=semigroupGenus L;
    ma:=max flatten degrees source gens semigroupIdeal L;
    bound:=g;
    range1:=toList(bound+1..ma);
    if o.Congruence then ( d:= bound+1; range:=select(range1,m->m%d==0) ) else (
	range=range1);
    if testWeierstrassRange(L,range,Verbose=>o.Verbose)==0 then (
	bound=bound-1;
    while ( <<bound<<endl;
	range1=toList(bound+1..ma);
	if o.Congruence then ( d= bound+1; range=select(range1,m->m%d==0) ) else (
	range=range1);
        testWeierstrassRange(L,range,Verbose=>o.Verbose)==0)
	do bound=bound-1;) else (
    bound=bound+1;
    while ( <<bound <<endl;
	range1=toList(bound+1..ma);
	if o.Congruence then ( d= bound+1; range=select(range1,m->m%d==0) ) else (
	range=range1);
        testWeierstrassRange(L,range,Verbose=>o.Verbose)==-1)
	do bound=bound+1; bound=bound-1);
    bound)
*-

-*
produceBounds(List,String) := o -> (LL,name)->(
D:=null;g:=null;L:=null;bound:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
    nameF:=name|"Failure";
    dLbounds:=apply(#LL,i->(
    L=LL_i;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    elapsedTime bound=fasterBound(L,Verbose=>o.Verbose);
    if class bound === Nothing then (
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we write it to a seperate file"<<flush<<endl;
    D = {L," is an example where findPoint failed"};
    openOutAppend nameF;
    nameF<<LL_i;
    nameF << ", ";    nameF<<close;
    ) else (
    D=(L,bound));
    openOutAppend name;
    name<<D;
    name << ", ";    name<<close;
    D));
dLbounds)
*-

-*
solvingFlatteningRelationsWithFieldExtension=method(Options=>{BaseField=> 10^6,CoeffSize=>1,CoeffBound=>10^4, Verbose=>false})
solvingFlatteningRelationsWithFieldExtension(Ideal,Matrix,Ideal) := o -> (J3,family2,I) -> (
	        SJ:= ring J3/J3;
		assert(betti syz sub(family2,SJ) == betti syz gens I);-- check flatness
		cd:=codim J3;
                c:=o.CoeffSize; 
		avars:=support J3;
		Lvars:=subsets(avars,cd);
		Lvarsc:=apply(Lvars, va->select(avars,av->not member(av,va)));
		pos:=select(Lvarsc,va->gens J3%ideal va==0);
		eq1:=null; eq2:=null;
		posa:=select(pos,pos1-> (
			eq1=sub(ideal apply(pos1,m->m-random(2*c-1)-c),ring J3);
		        eq2=ideal (gens J3%sub(eq1,ring J3));
			eq2 !=ideal(1_(ring eq2))));
		<<"#pos = " <<#pos<<", #posa = "<<#posa<<endl;
		posa=reverse posa;
  --if #posa == 0 then (error"solving approach did not work"; <<endl;return (false,null));
                if #posa == 0 then (<<"solving approach did not work" <<endl;return (false,null));
	        j:=0;
		while (
		    eq1=sub(ideal apply( posa_j,m->m-random(2*c-1)-c),ring J3);
		    eq2=ideal (gens J3%sub(eq1,ring J3));
	            eq:=eq1+eq2;
		not all apply(support J3,m->dim ideal (m%eq)==-1) and j< #posa-1) do j=j+1;
	        if j == #posa then return (false,null);
		if not gens J3%eq ==0 or dim eq == -1 then (
		    << "condition 2 of solving approach is not satisfied" <<endl;
		    return (false,null););
		fiber1:=family2%sub(eq,ring family2);
		--error "debug";
		S := ring I;
		fiber1=sub(fiber1,vars S|matrix { apply(#gens ring family2-numgens ring I,i->random(2*c-1)-c)});
		(worked,fiber):=clearDenominators(fiber1,CoeffBound=>o.CoeffBound);
		--error " debug";
		return (worked,fiber)
		)
*-





solvingFlatteningRelations=method(Options=>{Verbose=>0,BaseField=> ZZ/nextPrime 10^7,
	CoeffSize=>1,CoeffBound=>10^4})
solvingFlatteningRelations(Ideal,Matrix,Ideal) := o -> (J3,family2,I) -> (
	        --SJ:= ring J3/J3;
		--assert(betti syz sub(family2,SJ) == betti syz gens I);-- check flatness
		cd:=codim J3;
		J3a:=ideal (gens J3)_{0..cd-1};
                c:=o.CoeffSize; 
		avars:=support J3;
		Lvars:=subsets(avars,cd);
		Lvarsc:=apply(Lvars, va->select(avars,av->not member(av,va)));
		pos:=select(Lvarsc,va->gens J3a%ideal va==0);
		eq1:=null; eq2:=null;
		posa:=select(pos,pos1-> (
			eq1=sub(ideal apply(pos1,m->m-random(2*c-1)-c),ring J3);
		        eq2=ideal (gens J3a%sub(eq1,ring J3));
			eq2 !=ideal(1_(ring eq2))));
		<<"# of coordinate linear subspace of the base = " <<#pos <<endl;
		<<"# of linear subsets which leading to a point ="<<#posa<<endl;
  --		posa=posa;
  --if #posa == 0 then (error"solving approach did not work"; <<endl;return (false,null));
                if #posa == 0 then (<<"solving approach did not work" <<endl;return (false,null));
	        j:=0;
		while (
		    eq1=sub(ideal apply( posa_j,m->m-random(2*c-1)-c),ring J3);
		    eq2=ideal (gens J3%sub(eq1,ring J3));
	            eq:=eq1+eq2;
		not all apply(support J3,m->dim ideal (m%eq)==-1) and j< #posa-1) do j=j+1;
	        if j == #posa then return (false,null);
		if not gens J3%eq ==0 or dim eq == -1 then (
		    << "condition 2 of solving approach is not satisfied" <<endl;
		    return (false,null););
		fiber1:=family2%sub(eq,ring family2);
		--error "debug";
		S := ring I;
		fiber1=sub(fiber1,vars S|matrix { apply(#gens ring family2-numgens ring I,i->random(2*c-1)-c)});
		(worked,fiber):=clearDenominators(fiber1,CoeffBound=>o.CoeffBound);
		--error " debug";
		return (worked,fiber)
		)

clearDenominators=method(Options=>{CoeffBound=> 10^4})
clearDenominators(Matrix) := o -> fiber1 -> (    
    factors:={2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 27, 30, 32, 36, 40, 45, 48, 54, 60, 64, 72, 80, 90, 96, 108, 120, 128,
      135, 144, 160, 180, 192, 216, 240, 256};
    r:=rank source fiber1;g:=null;j:=null;w:=null;ma:=null;g0:=null;
    wgs:=apply(r,i->(g0=fiber1_{i};g=g0;
	    j=0;
	    while (ma=max (apply(entries (coefficients g)_1_0,c->sub(c,ZZ))/abs);
	          ma > o.CoeffBound and j <#factors ) do (g=factors_j*g0; j=j+1);
            if j==#factors then w=false else w=true;
	    (w,ideal g)));
    worked := all apply(wgs,(w,g)->w);
    if not worked then <<"clearing denominators did not work"<<flush<<endl;
    if worked then return (worked,gens sum(wgs,(w,g)->ideal g)) else return (false,gens sum(wgs,(w,g)->ideal g))
    )

isSmoothingFamily=method(Options=>{Verbose=>0})
isSmoothingFamily(List,Ideal,Matrix,Ideal) := o -> (L,I,family1,J2) -> (
    family2:=family1%sub(J2,ring family1);
    J3:=trim flatteningRelations(I,ring family2,family2);
	    --elapsedTime point=findPoint J3;
    if o.Verbose >0 then <<" codim J3 = "<< codim J3 << ", numgens J3 = "<< numgens J3<< endl;
    if o.Verbose >0 then elapsedTime (point:=findPoint J3;<<" time to find a point:"<<endl;) else
                    point = findPoint J3;
    if class point === Nothing then return false;
    fiber1:=sub(family2,(vars ring family2)_{0..#L-1}|
		    point_{#L..rank source point -1});
    z:=symbol z;
    kk:=coefficientRing ring I;
    StFinite:=kk[gens ring I|{z}, Degrees=>L|{1}];	    
    fibFinite:=ideal homogenize(sub(fiber1,StFinite),last gens StFinite);
    assert(betti syz gens fibFinite == betti syz gens I);
    smooth:=smoothnessWithReductions(fibFinite);
    smooth)
-*
getSmoothingFamilies=method(Options=>{Bound=>true, BaseField=> ZZ/(nextPrime 10^7),CoeffSize=>1,Congruence=>false,CoeffBound=>10^4, Verbose=>false})
getSmoothingFamilies(List,ZZ) := o -> (L,b) -> (
    I:=semigroupIdeal(L,BaseField=>o.BaseField);
    S:=ring I;
    z:=symbol z;
    St:=QQ[gens S|{z}, Degrees=>degrees S|{1}];
    kk:=coefficientRing S;
    (A,unfolding):=makeUnfolding I;
    ma:=max flatten unique (gens A/degree);
    range:=toList(b+1..ma);
    restrictionList:=select(flatten gens A, m->member((degree m)_0, range));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);--,Verbose=>o.Verbose);
    cJ1:=reverse decompose J1;
    ccJ1:=apply(cJ1,c->codim c);
    --if o.Verbose then (
    << "number of components = " <<#cJ1 << ", codimension of components = " <<ccJ1 <<endl;
    --);
    fiber:=matrix{{1_S}};fib:=null;fiber1:=null;point:=null;smooth:=null;
    c:=o.CoeffSize;J3:=null;family2:=null; StFinite:=null;fibFinite:=null;J2:=null;
    apply(#cJ1,k->( J2= cJ1_k;	    
		<<flush<<endl;
	    family2=family1%sub(J2,ring family1);
	    J3=trim flatteningRelations(I,ring family2,family2);
	    --elapsedTime point=findPoint J3;
	    elapsedTime (point=findPoint J3;<<" time to find a point"<<endl;);
	    fiber1=sub(family2,(vars ring family2)_{0..#L-1}|
		    point_{#L..rank source point -1});
            StFinite:=kk[gens St, Degrees=>degrees St];	    
	    fibFinite=ideal homogenize(sub(fiber1,StFinite),last gens StFinite);
	    assert(betti syz gens fibFinite == betti syz gens I);
	    
	    elapsedTime smooth=checkSmoothness(fibFinite);
	    <<"time to check smoothness"<<endl;
	    <<"smooth = " <<smooth <<endl;
	    if smooth then (smooth,J3,family2) else (false,J3,family2)))
    )
*-


    
     
getSmoothingFamily=method(Options=>{BaseField=> ZZ/(nextPrime 10^7),CoeffSize=>1,
	CoeffBound=>10^4,Verbose=>0})

getSmoothingFamily(List,ZZ) := o -> (L,b) -> (
    I:=semigroupIdeal(L,BaseField=>o.BaseField);
    S:=ring I;
    z:=symbol z;
    St:=QQ[gens S|{z}, Degrees=>degrees S|{1}];
    kk:=coefficientRing S;
    (A,unfolding):=makeUnfolding I;
    ma:=max flatten unique (gens A/degree);
    range:=toList(b+1..ma);
    restrictionList:=select(flatten gens A, m->member((degree m)_0, range));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);--,Verbose=>o.Verbose);
    if o.Verbose >1 then (<< "time to decompose:" <<endl;
	cJ1:= reverse decompose J1;) else (cJ1= reverse decompose J1;);
    ccJ1:=apply(cJ1,c->codim c);
    if o.Verbose >0 then (
    << "number of components = " <<#cJ1 << ", codimension of components = " <<ccJ1 <<endl;);
    good:=false;
    fiber:=matrix{{1_S}};fib:=null;fiber1:=null;pos:=null;posa:=null;fact1:=null;
    c:=o.CoeffSize;J3:=null;family2:=null; StFinite:=null;fibFinite:=null;J2:=null;
    comps:={}; 
    apply(#cJ1,k->( if not good then ( J2= cJ1_k;
		if o.Verbose>1 then <<flush<<endl;
		if isSmoothingFamily(L,I,family1,J2) then (
	    comps=append(comps,k);
            family2=family1%sub(J2,ring family1);
	    J3=trim flatteningRelations(I,ring family2,family2);
	    if o.Verbose>1 then <<"component number = "<< k <<", codim J3 = "
	    << codim J3 <<", numgens J3 = "<< numgens J3 <<endl;
	    if o.Verbose>1 then (elapsedTime if numgens J3 != 0 then (
		(worked,fiber):=solvingFlatteningRelations(J3,family2,I,CoeffBound=>o.CoeffBound,CoeffSize=>o.CoeffSize) ) else (
		fiber1=sub(family2,(vars ring family2)_{0..#L-1}|
		    matrix{ apply(numgens ring family2-#L,i->random(2*c-1)-c)});
		(worked,fiber)=clearDenominators(fiber1,CoeffBound=>o.CoeffBound));) else (
	        if numgens J3 != 0 then (
		(worked,fiber)=solvingFlatteningRelations(J3,family2,I,CoeffBound=>o.CoeffBound,CoeffSize=>o.CoeffSize) ) else (
		fiber1=sub(family2,(vars ring family2)_{0..#L-1}|
		    matrix{ apply(numgens ring family2-#L,i->random(2*c-1)-c)});
		(worked,fiber)=clearDenominators(fiber1,CoeffBound=>o.CoeffBound)););
            if worked then (
	    fib=ideal homogenize(sub(fiber,St),last gens St);
	    assert(betti syz gens fib == betti syz gens I);
	    StFinite:=kk[gens St, Degrees=>degrees St];
	    fibFinite=sub(fib,StFinite);
	    good=smoothnessWithReductions(fibFinite,Verbose=>o.Verbose);	    
	    );));
	));
    --error "debug";
    if o.Verbose >0 then <<" smoothing components numbers = " << comps <<endl;
    flat:=false;
    if good then if o.Verbose>2 then (elapsedTime flat=(betti syz gens fib==betti syz gens I);
	<<"flat = " << flat << endl;) else (flat=betti syz gens fib==betti syz gens I);
    if good and flat then (true,fib) else (false,null)
    )

getSmoothingFamily(List,List) := o -> (L,range) -> (
    I:=semigroupIdeal(L,BaseField=>o.BaseField);
    S:=ring I;
    z:=symbol z;
    St:=QQ[gens S|{z}, Degrees=>degrees S|{1}];
    kk:=coefficientRing S;
    (A,unfolding):=makeUnfolding I;
    restrictionList:=select(flatten gens A, m->member((degree m)_0, range));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);--,Verbose=>o.Verbose);
    if o.Verbose >0 then elapsedTime (cJ1:=decompose J1;<<"time to decompose J1 : "<<endl;) else
                    cJ1=decompose J1;
    cJ1=reverse cJ1;
    ccJ1:=apply(cJ1,c->codim c);
    if o.Verbose>1 then (
    << "number of components = " <<#cJ1 << ", codimension of components = " <<ccJ1 <<endl;
    );
    good:=false;
    fiber:=matrix{{1_S}};fib:=null;fiber1:=null;pos:=null;posa:=null;fact1:=null;
    c:=o.CoeffSize;J3:=null;family2:=null; StFinite:=null;fibFinite:=null;J2:=null;
    --J2=cJ1_1,c=2
    comps:={};
    apply(#cJ1,k->( if not good then ( J2= cJ1_k;
		if o.Verbose>0 then (<<flush<<endl;
		<<"component number = "<< k <<endl;);
		if isSmoothingFamily(L,I,family1,J2) then (
	    
	    comps=append(comps,k);
            family2=family1%sub(J2,ring family1);
	    if o.Verbose>0 then (
	    << "deformation weights = " << drop(support family2,#L)/degree <<endl;);
	    J3=trim flatteningRelations(I,ring family2,family2);
	    if o.Verbose>1 then (<<"codim J3 = "<< codim J3
		<<", numgens J3 = "<< numgens J3 <<endl;);
	    -*if codim J3 == 2 and numgens J3 ==3 then (
	    --<< "support J3 = " << toString support J3 <<flush <<endl;
	    --<< "ideal J3 = " << toString J3 <<flush<<endl;
	    fJ3:=res J3;
	    <<betti fJ3 <<flush<<endl;
	    << "Hilbert-Burch = " << fJ3.dd_2 << endl;
	    --J3a:=ideal fJ3.dd_2_{0};
	    --J3=trim ideal(gens J3 % J3a);
	    --assert(numgens J3==0);
	    --family2=family2%J3a;
	    );
	    *-
	    --if o.Verbose>1 then (
	             if numgens J3 != 0 then (
		(worked,fiber):=solvingFlatteningRelations(J3,family2,I,CoeffBound=>o.CoeffBound,CoeffSize=>o.CoeffSize) ) else (
		fiber1=sub(family2,(vars ring family2)_{0..#L-1}|
		    matrix{ apply(numgens ring family2-#L,i->random(2*c-1)-c)});
		(worked,fiber)=clearDenominators(fiber1,CoeffBound=>o.CoeffBound));
            if worked then (
	    fib=ideal homogenize(sub(fiber,St),last gens St);
	    assert(betti syz gens fib == betti syz gens I);
	    StFinite:=kk[gens St, Degrees=>degrees St];
	    fibFinite=sub(fib,StFinite);
	    good=smoothnessWithReductions(fibFinite,Verbose=>o.Verbose);	    
	    );));
	));
    --error "debug";
    if o.Verbose >0 then (<<" smoothing components numbers = " << comps <<endl;
    if good then flat:=elapsedTime (betti syz gens fib)==betti syz gens I;
	<<"flat = " << flat << endl) else
                       flat =(betti syz gens fib)==betti syz gens I;
    if good and flat then (true,fib,comps) else (false,null,comps)
    )




    

makeRange=method(Options=>{Verbose=>false})
makeRange(List,List) := o -> (L,congruences) -> (
    I:= semigroupIdeal L;
    ma:= max flatten degrees source gens I;
    rangeall:=toList(1..ma);
    range := select(rangeall,d->not all(congruences, j-> not d%j==0));
    range)

/// -- pseude protocoll do not delete
(L,b)=({6, 9, 13, 16, 20, 23}, 11)
congruences={6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>3)

appendFamily(L,A_1,"fam11","fam11.dbm")
LL11good=getFromDisk("fam11");#LL11good

(L,b)=({6, 8, 13, 23}, 15)
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({7, 10, 12, 13, 18}, 9)
congruences={10,11,12,13}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)= ({7, 10, 12, 15, 18, 23}, 11)
congruences={6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)= ({7, 10, 12, 15, 16}, 7)
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)= ({8, 9, 11, 14, 15}, 13)
congruences={7,15,16}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 9, 10, 14, 15}, 15)
congruences={4,6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>3)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 10, 12, 13, 14, 17}, 5)
congruences={6,8}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 9, 12, 13, 14}, 2)
congruences={3,4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 10, 11, 12, 14}, 15)
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)= ({8, 10, 11, 13, 17}, 10)
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)= ({8, 9, 10, 13}, 9)
congruences={10,11,12}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 10, 11, 12, 17}, 10)
congruences={8,11,12,13}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 10, 11, 14, 15}, 9)
congruences={10,12,22}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({8, 10, 11, 14, 15}, 9)
congruences={5,11,12}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({7, 10, 11, 16, 19}, 12)
congruences={4,6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 10, 11, 15}
degreeMatrices L
congruences={6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 10, 11, 14}
degreeMatrices L
congruences={6,10}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L= {6, 10, 11, 19}
degreeMatrices L
congruences={9,10,11}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 9, 11, 16}
degreeMatrices L
congruences={6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")


L={6, 9, 11, 14}
degreeMatrices L
congruences={1}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 11, 14, 15, 16}
degreeMatrices L
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")


L={6, 11, 13, 14, 16}
degreeMatrices L
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 11, 13, 15, 16}
degreeMatrices L
congruences={4,6,11}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>3)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 8, 17, 19, 21}
degreeMatrices L
congruences={4,5}
range=drop(makeRange(L,congruences),1)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={8, 9, 11, 15, 21}
degreeMatrices L
congruences={5,8}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>4)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={6, 8, 10, 19, 21, 23}
degreeMatrices L
congruences={6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={8, 9, 13, 14, 15, 20}
degreeMatrices L
congruences={5,6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={8, 9, 13, 14, 15, 19}
degreeMatrices L
congruences={1}
range=drop(makeRange(L,congruences),8)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={8, 10, 11, 14, 17, 23}
degreeMatrices L
congruences={1}
range=drop(makeRange(L,congruences),10)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={8, 10, 12, 13, 17, 19}
congruences={1}
range=drop(makeRange(L,congruences),9)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={8, 9, 12, 13, 19, 23}
congruences={7,8,9,10}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={9, 10, 12, 13, 14, 17}
congruences={7,8,9,10}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>3)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={9, 10, 12, 13, 14, 16}
congruences={7,8}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>5)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={9, 10, 12, 13, 14, 15}
congruences={7,8,9,10}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>5)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={9, 10, 12, 14, 15, 16}
congruences={8,9}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>5)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={9, 10, 11, 12, 13, 15}
congruences={8,9}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>5)
appendFamily(L,A_1,"fam11","fam11.dbm")


L={8, 10, 12, 14, 15, 19, 21}
congruences={5,6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")


L={8, 10, 12, 14, 15, 17, 21}
congruences={5,6}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>3)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={10, 11, 12, 13, 14, 16, 18, 19}
congruences={20}
range=makeRange(L,congruences)
range={10,11,12,13,14,15,16}
range={10,12,13,16}
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2) --3
appendFamily(L,A_1,"fam11","fam11.dbm")


L={10, 11, 12, 13, 14, 15, 18, 19}

range={10,11,12,15,16,17}
range={10,11,15}
range=toList(10..19)
elapsedTime A=getSmoothingFamily(L,L,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")



L={10, 11, 12, 13, 15, 16, 17, 19}
--deformation weights = {{11}, {10}, {9}, {9}}
range=toList(9..20)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")


L={10, 11, 12, 13, 14, 16, 17, 19}
range=toList(8..19)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)
appendFamily(L,A_1,"fam11","fam11.dbm")



L= {10, 11, 12, 13, 14, 15, 17, 19}
range=toList(8..11)|toList(16..19)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>3)
appendFamily(L,A_1,"fam11","fam11.dbm")



L= {10, 11, 12, 14, 15, 16, 17, 18}
range=toList(8..12)|toList(17..20)
congruences={5}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")

L={9, 11, 12, 14, 15, 16, 17} 
-- with a 2x3 matrix to solve {4}
congruences={4}
range=makeRange(L,congruences)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")


L={9, 11, 12, 13, 14, 15, 17} 
range={5,6}|toList(10..12)|toList(15..18)|toList(20..24)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")



L={9, 11, 13, 14, 15, 16, 17, 19}
elapsedTime A=getSmoothingFamily(L,L,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")


(L,b)=({10, 11, 12, 13, 14, 15, 16, 17}, 14)
congruences={b+1}
range=makeRange(L,congruences)
range=drop(makeRange(L,{1}),b)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")

(L,b)=({10, 11, 12, 13, 14, 15, 16, 19}, 12)
range=drop(makeRange(L,{1}),b)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")



(L,b)=({10, 11, 12, 13, 14, 15, 16, 18}, 10)
range=drop(makeRange(L,{1}),b)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1) -- 3078.82s elapsed
appendFamily(L,A_1,"fam11","fam11.dbm")



(L,b)=({10, 11, 12, 13, 14, 16, 17, 18}, 9)
range=drop(makeRange(L,{1}),b)
--range=makeRange(L,{b+1,b+2})
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)  -- 505.327s elapsed
appendFamily(L,A_1,"fam11","fam11.dbm")



(L,b)=({10, 11, 12, 13, 14, 15, 17, 18}, 8)
range=drop(makeRange(L,{1}),b)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>2)  -- 672.41s elapsed
appendFamily(L,A_1,"fam11","fam11.dbm")



(L,b)=({10, 11, 12, 13, 15, 16, 17, 18}, 8)
range=drop(makeRange(L,{1}),b)
range = toList(9..22)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)
appendFamily(L,A_1,"fam11","fam11.dbm")

----
(L,b)=({9, 11, 12, 13, 15, 16, 17}, 8)
range=drop(makeRange(L,{1}),b)
elapsedTime A=getSmoothingFamily(L,range,CoeffSize=>1)  -- 481.699s elapsed
appendFamily(L,A_1,"fam11","fam11.dbm")

-- recovery code for "fam11" 
X="fam11.dbm"
Y=openDatabaseOut X
famKeys=keys Y;
#famKeys
newBounds11=getFromDisk("nbounds11");#newBounds11
fam11recovery=apply(newBounds11,(L,b) ->L);
toString select(fam11recovery,L->member((toString L|"ring"),famKeys))
LL11good=getFromDisk("fam11");#LL11good
close Y
--


///

appendFamily=method()

appendFamily(List,Ideal,String,String) := (L, fib, name, dataName) -> (
    openOutAppend name;
    name<<L;
    name << ", ";
    name<<close;    
    familyData:=openDatabaseOut dataName;
    familyData#(toString L|"ring") = toExternalString (ring fib); 
    familyData#(toString L|"ideal") = toString (fib);
    close familyData;
    )
   

     
checkSmoothness=method(Options=>{Verbose=>0})	    
checkSmoothness(Ideal) := o -> fib -> (
    St:=ring fib;
    relJac:=(jacobian fib)^{0..numgens St-2};
    nL:=numgens St-1;
    ng:=numgens fib;
    countMax:=min(2*floor(binomial(ng,nL-1)/3),400);
    colum:=toList(0..nL-2);
    mat:=relJac_colum;
    fewMinors:=minors(nL-1,mat);
    singF:=ideal mingens (fib+fewMinors);
    if o.Verbose==1 then (
	elapsedTime singF=saturate(singF,last gens St);
	<<" numgens singF = " << numgens singF<<flush<<endl;
	) else (singF=saturate(singF,last gens St));
    columSets:={colum};
    count:=0;
    if o.Verbose==1 then (<<"time to check smoothness:"<<endl;
    elapsedTime while (not singF==ideal 1_St) and count<countMax do (
	count=count+1;
	while (
	    while (
		colum=sort apply(nL-1,i->random(ng));
		#(unique colum) < nL-1)
	    do ();
            member(colum,columSets))
	do ();
	columSets=append(columSets,colum);
	--if o.Verbose then (<<"size of columSets = " << #columSets <<flush<<endl);
	mat=relJac_colum;
	fewMinors=minors(nL-1,mat);
	singF=ideal mingens (singF+fewMinors);
	singF=saturate(singF,last gens St);
        if o.Verbose==1 then ( 
	<<" numgens singF = " << numgens singF<<flush<<endl;
	    );
	);) else (
      while (not singF==ideal 1_St) and count<countMax do (
	count=count+1;
	while (
	    while (
		colum=sort apply(nL-1,i->random(ng));
		#(unique colum) < nL-1)
	    do ();
            member(colum,columSets))
	do ();
	columSets=append(columSets,colum);
	--if o.Verbose then (<<"size of columSets = " << #columSets <<flush<<endl);
	mat=relJac_colum;
	fewMinors=minors(nL-1,mat);
	singF=ideal mingens (singF+fewMinors);
	singF=saturate(singF,last gens St);
        if o.Verbose==1 then ( 
	<<" numgens singF = " << numgens singF<<flush<<endl;
	    );
	););
    if singF==ideal 1_St then return true else (
    if numgens singF<=numgens St+1 then (
    singF=trim(singF+minors(nL-1,relJac%singF));
    singF=saturate(singF,last gens St);
    if o.Verbose==2 then <<" numgens singF = " << numgens singF<<flush<<endl;);
    if o.Verbose==1 then <<" numgens singF = " << numgens singF<<flush<<endl;
	if numgens singF ==1 then <<"singF = " <<singF<<endl;	    
        singF==ideal 1_St))
-* 
produceSmoothingFamilies=method(Options=>{Verbose=>false, "KillFile" =>false,CoeffSize=>1,CoeffBound=>10^4})
produceSmoothingFamilies(List,String,String) := o -> (LL,name,dataName)->(
D:=null;g:=null;L:=null;bound:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
    nameF:=name|"Failure";
    dLFamilies:=apply(#LL,i->(
    (L,b):=LL_i;
    g=semigroupGenus L;
    ma:=max flatten (degrees source gens semigroupIdeal L);
    range:=toList(b+1..ma);
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<LL_i <<flush<<endl;    
    elapsedTime (good,fib):=getSmoothingFamily(L,range,CoeffSize=>o.CoeffSize,CoeffBound=>o.CoeffBound,Verbose=>o.Verbose);
    <<"good = " <<good <<flush<<endl;
    if not good then (
    --	<<"example #"<<i<< " with semigroup "<<L
    --	<<" could not find a smoothing family from the bound"<<flush<<endl;
    D = {L,b," a smoothing family from the bound failed"};
    openOutAppend nameF;
    nameF<<LL_i;
    nameF << ", ";    nameF<<close;
    ) else (
    openOutAppend name;
    name<<L;
    name << ", ";
    name<<close;    
    familyData:=openDatabaseOut dataName;
    familyData#(toString L|"ring") = toExternalString (ring fib); 
    familyData#(toString L|"ideal") = toString (fib);
    close familyData;);
    (L,fib)));
dLFamilies)
*-

    -* Documentation section *-
beginDocumentation()

doc ///
Key
  SmoothingFamilies
Headline
  Compute smoothing families for Weierstrass semigroups
Description
  Text
    Compute smoothing families for Weierstrass semigroups
References
     \textit{Pinkham, Henry C.},
       Deformations of algebraic varieties with \(G_m\) action,
       Ast{\'e}risque t\extbf{20} (1974), pp 1 - 131,
       Soci{\'e}t{\'e} Math{\'e}matique de France (SMF), Paris
SeeAlso
   AIWeierstrass

///



doc ///
Key
   smoothnessWithReductions
   (smoothnessWithReductions, Ideal)
   [smoothnessWithReductions,BaseField]
   [smoothnessWithReductions,Verbose]
Headline
   Check smoothness by using reductions to points
Usage
   answer = smoothnessWithReductions J  
Inputs
   J:Ideal
     of a one parameter family 
Outputs
    answer:Boolean
      true if the fiber is smooth
Description
  Text
    Given a homogeneousideal J in S[z]=kk[x,z] which defines a flat family of affine curves
    we check smoothness of the general fiber at z=1.
    The basic idea is to compute some minors of the jacobian matrix which
    intersect the curve in a zero-dimensional scheme singF.
    Then using decompose singF to reduce the check at points of the finitely
    many maximal ideals p. Since Sp=S/p is a field the rank of the jacobian matrix restricted to Sp
    can be computed by checking the number of generators of the cokernel, since cokernel represents the Zariski tangent
    space at p of the original curve.
    This is much cheaper then computing all or enough minors of the jacobian matrix.
  Example
    L={7, 8, 17, 19, 20}
    R=QQ[x_0..x_1, x_3, x_5..x_6, z, Degrees => {7..8, 17, 19..20, 1}]
    J=ideal(x_1^3-x_0*x_3+x_1*z^16+x_0*z^17,x_1*x_5-x_0*x_6+x_0^2*z^13+x_1*z^19-x_0*z^20,x_0^4-x_1*x_6+x_0*x_1*z^13
      +x_0^2*z^14-x_1*z^20,x_1^2*x_3-x_0^2*x_5-x_5*z^14+x_3*z^16+x_1^2*z^17+x_0*x_1*z^18+x_0^2*z^19,x_3^2-x_0^2*x_6
      +x_0^3*z^13-x_6*z^14+x_1^2*z^18+2*x_0*x_1*z^19-x_0^2*z^20+x_0*z^27-2*z^34,x_3*x_5-x_1^2*x_6+x_0*x_1^2*z^13-x_
      6*z^16-x_5*z^17+x_3*z^19-x_1^2*z^20+x_0*z^29-2*z^36,x_0^3*x_1^2-x_3*x_6+x_0*x_3*z^13+x_0*x_1^2*z^14+x_0^3*z^
      16+x_6*z^17-x_3*z^20+z^37,x_0^3*x_3-x_5^2+x_0^2*x_1*z^16+x_0^3*z^17+x_6*z^18-x_0*z^31+2*z^38,x_0^2*x_1*x_3-x_
      5*x_6+x_0*x_5*z^13+x_0*x_1^2*z^16+x_0^2*x_1*z^17+x_0^3*z^18+x_6*z^19-x_5*z^20+z^39,x_0^3*x_5-x_6^2+2*x_0*x_6*
      z^13+x_0*x_5*z^14+x_0^3*z^19-2*x_6*z^20-x_0^2*z^26+3*x_0*z^33-z^40);
    elapsedTime smoothnessWithReductions(J,Verbose=>1)
  Text
    The intermediate output dim and degree singF = (0, 17) says that after computing some
    minors of the jacobian matrix, we detect that the curve is smooth away
    from the zero dimensional scheme defined by singF of degree 17.
  Example
    elapsedTime checkSmoothness J
  Text
    The function checkSmoothness takes longer, some times much longer.
    
SeeAlso
    checkSmoothness

///

doc ///
Key
   findCompleteIntersection
   (findCompleteIntersection,Ideal)
   [findCompleteIntersection,Strategy]
Headline
   Find complete intersection defined by some of the generators
Usage
   column = findCompleteIntersection I  
Inputs
   I:Ideal
     a semigroup ideal
Outputs
    column:List
      a list of codim I generators of the ideal I which defines a complete intersection 
Description
  Text
    We pick positions one by one generators of I, which increase the codimension by one until reached codim I.
    
  Example   
    L={7, 8, 17, 19, 20}
    I=semigroupIdeal L
    numgens I
    columnFront=findCompleteIntersection I
    ci=ideal (gens I)_columnFront
    codim ci == codim I
  Text
    There are three startegies "front", "back" and "random".
  Example
    columnBack=findCompleteIntersection(I,Strategy=>"back")
    ci2=ideal (gens I)_columnBack
    codim ci2 == codim I
    columnRandom=findCompleteIntersection(I,Strategy=>"random")
    ci3=ideal (gens I)_columnRandom
    codim ci3 == codim I

SeeAlso
   semigroupIdeal

Caveat
  It is possible that the function does not find a complete intersection of generators.
  In that case a too short List is returned.
///


doc ///
Key
   improveFamily
   (improveFamily,Ideal)
   [improveFamily,Verbose]
Headline
   Find a 1-parameter smoothing family with of perhaps smaller number of terms and coefficients
Usage
   J1 = improveFamily J  
Inputs
   J:Ideal
     a one-parameter smoothing family of a semigroup ideal
Outputs
   J:Ideal
     a one-parameter smoothing family of a semigroup ideal
Description
  Text
    We first compute the flat family of ideals which uses the same terms as J
    using getParameterFamily.
    We then choose a point in a smoothing component of the base which uses hopefully fewer terms and
    smaller coefficients by using getOneParameterFamily
    
  Example
    R=QQ[x_0..x_1, x_3, x_5..x_6, z, Degrees => {7..8, 17, 19..20, 1}]
    J=ideal(x_1^3-x_0*x_3+x_1*z^16+x_0*z^17,x_1*x_5-x_0*x_6+x_0^2*z^13+x_1*z^19-x_0*z^20,x_0^4-x_1*x_6+x_0*x_1*z^13
      +x_0^2*z^14-x_1*z^20,x_1^2*x_3-x_0^2*x_5-x_5*z^14+x_3*z^16+x_1^2*z^17+x_0*x_1*z^18+x_0^2*z^19,x_3^2-x_0^2*x_6
      +x_0^3*z^13-x_6*z^14+x_1^2*z^18+2*x_0*x_1*z^19-x_0^2*z^20+x_0*z^27-2*z^34,x_3*x_5-x_1^2*x_6+x_0*x_1^2*z^13-x_
      6*z^16-x_5*z^17+x_3*z^19-x_1^2*z^20+x_0*z^29-2*z^36,x_0^3*x_1^2-x_3*x_6+x_0*x_3*z^13+x_0*x_1^2*z^14+x_0^3*z^
      16+x_6*z^17-x_3*z^20+z^37,x_0^3*x_3-x_5^2+x_0^2*x_1*z^16+x_0^3*z^17+x_6*z^18-x_0*z^31+2*z^38,x_0^2*x_1*x_3-x_
      5*x_6+x_0*x_5*z^13+x_0*x_1^2*z^16+x_0^2*x_1*z^17+x_0^3*z^18+x_6*z^19-x_5*z^20+z^39,x_0^3*x_5-x_6^2+2*x_0*x_6*
      z^13+x_0*x_5*z^14+x_0^3*z^19-2*x_6*z^20-x_0^2*z^26+3*x_0*z^33-z^40)
    L=flatten drop(degrees R,-1)
    J1=improveFamily(J)
    J_*/size
    J1_*/size
    (M,C)=coefficients gens J;
    unique (entries flatten C)_0
    (M1,C1)=coefficients gens J1;
    unique (entries flatten C1)_0
Caveat
  It is possible that the function does not find a smooth fiber, which results in a message
  that these example needs to be repeated.
    
SeeAlso
   getParameterFamily
   getOneParameterFamily

///

doc ///
Key
   getParameterFamily
   (getParameterFamily,Ideal)
Headline
   Compute the parametric family which uses the same terms as J
Usage
   (base,family) = getParameterFamily J  
Inputs
   J:Ideal
     of a one-parameter smoothing family of a semigroup ideal
Outputs
   base:Ideal
     of flatteness relations
   family:Matrix
     a matrix containing the generators of the parametric family   
Description
  Text
    We compute the flat family of ideals which uses the same terms as J.
    The ideal base contains the flattness relations for the coefficents of the family.        
  Example
    R=QQ[x_0..x_1, x_3, x_5..x_6, z, Degrees => {7..8, 17, 19..20, 1}]
    J=ideal(x_1^3-x_0*x_3+x_1*z^16+x_0*z^17,x_1*x_5-x_0*x_6+x_0^2*z^13+x_1*z^19-x_0*z^20,x_0^4-x_1*x_6+x_0*x_1*z^13
      +x_0^2*z^14-x_1*z^20,x_1^2*x_3-x_0^2*x_5-x_5*z^14+x_3*z^16+x_1^2*z^17+x_0*x_1*z^18+x_0^2*z^19,x_3^2-x_0^2*x_6
      +x_0^3*z^13-x_6*z^14+x_1^2*z^18+2*x_0*x_1*z^19-x_0^2*z^20+x_0*z^27-2*z^34,x_3*x_5-x_1^2*x_6+x_0*x_1^2*z^13-x_
      6*z^16-x_5*z^17+x_3*z^19-x_1^2*z^20+x_0*z^29-2*z^36,x_0^3*x_1^2-x_3*x_6+x_0*x_3*z^13+x_0*x_1^2*z^14+x_0^3*z^
      16+x_6*z^17-x_3*z^20+z^37,x_0^3*x_3-x_5^2+x_0^2*x_1*z^16+x_0^3*z^17+x_6*z^18-x_0*z^31+2*z^38,x_0^2*x_1*x_3-x_
      5*x_6+x_0*x_5*z^13+x_0*x_1^2*z^16+x_0^2*x_1*z^17+x_0^3*z^18+x_6*z^19-x_5*z^20+z^39,x_0^3*x_5-x_6^2+2*x_0*x_6*
      z^13+x_0*x_5*z^14+x_0^3*z^19-2*x_6*z^20-x_0^2*z^26+3*x_0*z^33-z^40)
    L=flatten drop(degrees R,-1)
    (base,family)=getParameterFamily J;
    numgens base
    cbase=decompose base
    J_0
    family_(0,0)
    J_*/size
    (ideal family)_*/size
    J_4
    family_(0,4)
    support family
    support family/degree 
SeeAlso
   improveFamily
   getOneParameterFamily
///

doc ///
Key
   getOneParameterFamily
   (getOneParameterFamily,Ideal,Ideal,Matrix,ZZ)
   [getOneParameterFamily,CoeffSize]
Headline
   Compute a one parameter smoothing family
Usage
   fib = getParameterFamily(J,base,family,p)  
Inputs
   J:Ideal
     of a one-parameter smoothing family of a semigroup ideal
   family:Matrix
     a parametric family which uses the same terms as J
   base:Ideal
      flattening relations
   p:ZZ
    about 1 out of p free parameters are choosen nonzero
Outputs
   fib:Ideal
      of a one-parameter smoothing family  
Description
  Text
    We compute a one-parameter smoothing family  which uses the same terms asthe matrix family.
  Example
    R=QQ[x_0..x_1, x_3, x_5..x_6, z, Degrees => {7..8, 17, 19..20, 1}]
    J=ideal(x_1^3-x_0*x_3+x_1*z^16+x_0*z^17,x_1*x_5-x_0*x_6+x_0^2*z^13+x_1*z^19-x_0*z^20,x_0^4-x_1*x_6+x_0*x_1*z^13
      +x_0^2*z^14-x_1*z^20,x_1^2*x_3-x_0^2*x_5-x_5*z^14+x_3*z^16+x_1^2*z^17+x_0*x_1*z^18+x_0^2*z^19,x_3^2-x_0^2*x_6
      +x_0^3*z^13-x_6*z^14+x_1^2*z^18+2*x_0*x_1*z^19-x_0^2*z^20+x_0*z^27-2*z^34,x_3*x_5-x_1^2*x_6+x_0*x_1^2*z^13-x_
      6*z^16-x_5*z^17+x_3*z^19-x_1^2*z^20+x_0*z^29-2*z^36,x_0^3*x_1^2-x_3*x_6+x_0*x_3*z^13+x_0*x_1^2*z^14+x_0^3*z^
      16+x_6*z^17-x_3*z^20+z^37,x_0^3*x_3-x_5^2+x_0^2*x_1*z^16+x_0^3*z^17+x_6*z^18-x_0*z^31+2*z^38,x_0^2*x_1*x_3-x_
      5*x_6+x_0*x_5*z^13+x_0*x_1^2*z^16+x_0^2*x_1*z^17+x_0^3*z^18+x_6*z^19-x_5*z^20+z^39,x_0^3*x_5-x_6^2+2*x_0*x_6*
      z^13+x_0*x_5*z^14+x_0^3*z^19-2*x_6*z^20-x_0^2*z^26+3*x_0*z^33-z^40);
    L=flatten drop(degrees R,-1)
    (base,family)=getParameterFamily J;
    J1=getOneParameterFamily(J,base,family,4)
    J_*/size
    J1_*/size
SeeAlso
   improveFamily
   getParameterFamily
///

doc ///
Key
   getRangeOfOneParameterFamily
   (getRangeOfOneParameterFamily,Ideal)
Headline
   Compute the range of degrees of a one parameter family
Usage
   range = getRangeOfOneParameterFamily J
Inputs
   J:Ideal
     of a one-parameter smoothing family of a semigroup ideal
Outputs
   range:List
      range of degrees of the 1-parameter family
Description
  Text
    We compute range of degrees of a one parameter family
  Example
    R=QQ[x_0..x_1, x_3, x_5..x_6, z, Degrees => {7..8, 17, 19..20, 1}]
    J=ideal(x_1^3-x_0*x_3+x_1*z^16+x_0*z^17,x_1*x_5-x_0*x_6+x_0^2*z^13+x_1*z^19-x_0*z^20,x_0^4-x_1*x_6+x_0*x_1*z^13
      +x_0^2*z^14-x_1*z^20,x_1^2*x_3-x_0^2*x_5-x_5*z^14+x_3*z^16+x_1^2*z^17+x_0*x_1*z^18+x_0^2*z^19,x_3^2-x_0^2*x_6
      +x_0^3*z^13-x_6*z^14+x_1^2*z^18+2*x_0*x_1*z^19-x_0^2*z^20+x_0*z^27-2*z^34,x_3*x_5-x_1^2*x_6+x_0*x_1^2*z^13-x_
      6*z^16-x_5*z^17+x_3*z^19-x_1^2*z^20+x_0*z^29-2*z^36,x_0^3*x_1^2-x_3*x_6+x_0*x_3*z^13+x_0*x_1^2*z^14+x_0^3*z^
      16+x_6*z^17-x_3*z^20+z^37,x_0^3*x_3-x_5^2+x_0^2*x_1*z^16+x_0^3*z^17+x_6*z^18-x_0*z^31+2*z^38,x_0^2*x_1*x_3-x_
      5*x_6+x_0*x_5*z^13+x_0*x_1^2*z^16+x_0^2*x_1*z^17+x_0^3*z^18+x_6*z^19-x_5*z^20+z^39,x_0^3*x_5-x_6^2+2*x_0*x_6*
      z^13+x_0*x_5*z^14+x_0^3*z^19-2*x_6*z^20-x_0^2*z^26+3*x_0*z^33-z^40);
    range=getRangeOfOneParameterFamily J
SeeAlso
   getParameterFamily
///

doc ///
Key
   testBound
   testCongruences
   testRange
   (testBound,List,ZZ)
   (testCongruences,List,List)
   (testRange,List,List)
   [testBound,Verbose]
   [testBound,CoeffSize]
   [testCongruences,CoeffSize]
   [testRange,CoeffSize]
Headline
   Test whether b is bound for the semigroup L and compute a 1-parameter smoothing family if yes
Usage
   (answer,J,comp) = testBound(L,b)
Inputs
   L:List
     a of generators of a semigroup
   b:ZZ
    bound for the degrees of the parameters
Outputs
   answer:Boolean
      true if a smoothing family was found
   J:Ideal
     ideal of a 1-parameter smoothing family of the semigroup ring of L
   comp: List
     of component numbers which are smoothing families
Description
  Text
    We check whether there exists a smoothing component for the resticted unfolding with variables
    of degree >b (or degree congruent 0 mod d for some d in congruences
	or variable with degree in the range).
    If the answer is yes, then we compute such smoothing family over QQ.
    This however might fail if the coefficient size is too small or the random choices in
    solvingFlatteningRelations are bad. In that case J will be null.        
  Example  
    L={7,8,17,19,20}
    (answer,J,comp)=testBound(L,12)
    range=drop(flatten getRangeOfOneParameterFamily J,-5)    
    (answer1,J1,comp)=testRange(L,range,CoeffSize=>2)
    J_*/size
    J1_*/size
    congruences={6}
    (answer,J,comp)=testCongruences(L,congruences,Verbose=>2)
SeeAlso
   solvingFlatteningRelations
   
///

doc ///
Key
   solvingFlatteningRelations
   (solvingFlatteningRelations,Ideal,Matrix,Ideal)
   [solvingFlatteningRelations,CoeffBound]
   [solvingFlatteningRelations,CoeffSize]
   [solvingFlatteningRelations,BaseField]
   [solvingFlatteningRelations,Verbose]
   
Headline
   Solving the flatttening ralations over QQ
Usage
   (worked,fiber)=solvingFlatteningRelations(base,family,I)
Inputs
   base:Ideal
     irreducible ideal of flattening relations
   family:Matrix
    matrix of generators of the family
   I:Ideal
     semigroup ideal
Outputs
   worked:Boolean
      true if a smoothing family was found
   fiber:Ideal
     ideal of a 1-parameter smoothing family 
Description
  Text
    We look for subsets of the source consisting of all but codim base many elements
    which define a linear subspace of the base. Substituting random small values for these
    variables, might lead to an ideal which defines a point in the base.
    There is some intermediate output. 
  Example  
    L={7,8,17,19,20}
    I=semigroupIdeal L;
    (answer,J,comp)=testBound(L,12);
    (base1,family1)=getParameterFamily J;
    base=last decompose base1;
    family=family1%sub(base,ring family1);
    (worked,fiber)=solvingFlatteningRelations(base,family,I)
SeeAlso
   clearDenominators
   
///

doc ///
Key
   clearDenominators
   (clearDenominators, Matrix)
   [clearDenominators, CoeffBound]
Headline
   Clear denominators
Usage
   (worked,fiber)=clearDenominators(family)
Inputs
   family:Matrix
     a family over a finite large prime field
Outputs
   worked:Boolean
      true if clearing denominators worked
   fiber:Matrix
     matrix of generators of a 1-parameter smoothing family over QQ
Description
  Text
    Since we work at this point over a large prime field we might detect denominators
    for a lift to QQ by multiplying each equation by a factor such that the naive lifts
    are still small.
    The factors we try are have 2,3 and 5 as the only prime factors and are not so small.
  Example  
    L={7,8,17,19,20}
    semigroupGenus L
    I=semigroupIdeal(L,BaseField=>QQ);
    (answer,J,comp)=testBound(L,12,Verbose=>1);
    (base1,family1)=getParameterFamily J;
    base=last decompose base1
    family=family1%sub(base,ring family1);
    (worked,fiber)=solvingFlatteningRelations(base,family,I);
    p=nextPrime 10^5
    kk=ZZ/p;
    SzFinite=kk[support J, Degrees=>apply(support J,m->degree m)]
    fibF=sub(fiber,SzFinite);
    fiber=fibF*diagonalMatrix({1/2_kk,2/3_kk,1/5_kk,4/3_kk,1/30_kk,2/5_kk,1/2_kk,1/3_kk,1/2_kk,1/3_kk})
    (worked,fiber1)=clearDenominators fiber
SeeAlso
   solvingFlatteningRelations
   
///


doc ///
Key
   isSmoothingFamily
   (isSmoothingFamily,List,Ideal,Matrix,Ideal)
   [isSmoothingFamily,Verbose]
Headline
   Is the family a smoothing family?
Usage
   smooth=isSmoothingFamily(L,I,family,base) -> (
Inputs
   L:List
     list of generators of a semigroup
   I:Ideal
     semigroup ideal (of L)
   family:Matrix
     a family over a finite large prime field
   base: Ideal
     ideal of flattening relations
Outputs
   smooth:Boolean
      true if the family is a smoothing family
Description
  Text
    Given a irrdeducible parameteric family over a (large) finite field, the functions
    picks a random point in the base and checks whether the corresponding fiber is a smooth.
  Example  
    L={6,8,9,11}
    semigroupGenus L
    I=semigroupIdeal(L,BaseField=>ZZ/nextPrime 10^4);
    (answer,J,comp)=testBound(L,2,Verbose=>1);
    (base1,family1)=getParameterFamily J;
    family=family1%sub(base1,ring family1);
    base=(decompose base1)_2;
    kk=coefficientRing ring I;
    SAFinite=kk[gens ring family,Degrees=>degrees ring family]
    AF=kk[gens ring base,Degrees=>degrees ring base]
    baseF=sub(base,AF)
    familyF=sub(family,SAFinite);
    isSmoothingFamily(L,I,familyF,baseF)
  Text
    The intermediate output gives the codimension and number of generators of J3, the final system of equations to solve,
    and the timing for finding a point.
SeeAlso
   getParameterFamily
   testBound
///

doc ///
Key
   sieveByBound
   sieveByCongruences
   sieveByRange
   (sieveByBound,List,ZZ,String,String)
   (sieveByCongruences,List,List,String,String)
   (sieveByRange,List,List,String,String)
   [sieveByBound,CoeffSize]
   [sieveByBound,Verbose]
   [sieveByCongruences,CoeffSize]
   [sieveByRange,CoeffSize]
Headline
   Sieve the list by bound (or congruences or range)
Usage
   sieveByBound(LL,b,done,doneData)
   sieveByRange(LL,b,range,doneData)
   sieveByCongruences(LL,b,congruences,doneData)
Inputs
   LL:List
     list of semigroups
   bound:ZZ
     degree bound
   done:String
     name of a file of done examples
   doneData:String
     name of the dataFile with name doneData.dbm

Outputs

Description
  Text
    We sieve the list LL of semigroups L by those which pass testBound(L,b).
    We record the successes ba appending them to the file done and by recording
    the corresponding data for the smoothing families in doneData
    on the hard disk.
  Example  
    LL=(toDoList 8)_{0..2}
    X="fam8"
    Xdbm="fam8.dbm"
    "sieveByBound(LL,6,X,Xdbm)";
    range=toList(6..8)
    LL=(toDoList 8)_{4,5}
    "sieveByRange(LL,range,X,Xdbm)";
  Text
    Reading and writing to the disk does not work in the documentation.
    Hence we give the command in quotes.
    
SeeAlso
   toDoList
   testBound
///





doc ///
Key
   getSmoothingFamily
   (getSmoothingFamily,List,ZZ)
   (getSmoothingFamily,List,List)
   [getSmoothingFamily,CoeffBound]
   [getSmoothingFamily,CoeffSize]
   [getSmoothingFamily,BaseField]
   [getSmoothingFamily,Verbose]
Headline
   Get a smoothing family for the semigroup L
Usage
   (smooth,fib)=getSmoothingFamily(L,b)
   (smooth,fib,comps)=getSmoothingFamily(L,range)
Inputs
   L:List
     list of generators of a semigroups
   bound:ZZ
     degree bound
   range:List
     range of degrees
 
Outputs
   smooth: Boolean
     true is a smoothing family was found
   fib: Ideal
     ideal of a one-parameter smoothing family or null
   comps: List
     list of component numbers of the smoothing components discovered
Description
  Text
    We first test whether by the bound b or the range of degrees the 
    restricted unfolding leads to a smoothing family over a finite field.
    If yes and with Verbose>0 then the degrees of the parameters of the parameters
    of the smoothing family are printed.
    In a second step we try to lift the example to characteristic 0 and check smoothness again.
  Example  
    L=(toDoList 8)_0
    (smooth,fib)=getSmoothingFamily(L,12,Verbose=>1)
    (smooth,fib)=getSmoothingFamily(L,11,Verbose=>1)
    range=makeRange(L,{4})
    (smooth,fib, comps)=getSmoothingFamily(L,range,Verbose=>1)
    (smooth,fib, comps)=getSmoothingFamily(L,range,Verbose=>2)
SeeAlso
   makeRange
///

doc ///
Key
   makeRange
   (makeRange,List,List)
   [makeRange,Verbose]
Headline
   Make a range of degrees for getSmoothingFamily
Usage
   range=makeRange(L,congruences)
Inputs
   L:List
     list of generators of a semigroups
   congruences:List
     ;list of congruences
 
Outputs
   range: List
     a range of degrees
Description
  Text
  Example  
    L=(toDoList 8)_0
    congruences={4,6}
    range1=makeRange(L,{4,6})
    elapsedTime (smooth,fib, comps)=getSmoothingFamily(L,range1,Verbose=>1)
  Text
    The range are degrees r which congruent 0 mod d for some d in the list congruences.
    To get a degree bound rane one can use the following.
  Example
    range2=drop(makeRange(L,{1}),11)
    elapsedTime (smooth,fib, comps)=getSmoothingFamily(L,range2,Verbose=>1)
SeeAlso
   makeRange
   getSmoothingFamily
///


--doc ///
///
Node
  Key
   degreeMatrices
   (degreeMatrices, Complex)
   (degreeMatrices, Ideal)
   (degreeMatrices, List)
  Headline
   degree matrices of the maps in a complex
  Usage
   degmats = degreeMatrices F
   degmats = degreeMatrices I   
   degmats = degreeMatrices L
  Inputs
   F:Complex
   I:Ideal
   L:List
  Outputs
   degmats:List
  Description
    Text
     prints the degree matrices of a complex
    Example
     L = {3,4,5}
     I = semigroupIdeal L
     F = res I
     degreeMatrices F
     degreeMatrices I
     degreeMatrices L
  SeeAlso
   semigroupIdeal
///

-* Test section *-

TEST ///-* 0 fasterBound *-

L={8, 9, 12, 13, 19, 23}

b=fasterBound(L,Verbose=>true,Congruence=>true)

--elapsedTime buchweitzSemigroups(13,16)
///

TEST ///-* 1 produceSmoothingFamilies *-

newBounds11=getFromDisk("nbounds11");#newBounds11
LL11bad=newBounds11;
elapsedTime fam11a=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>1); -- 6034.67s elapsed
LL11good=getFromDisk("fam11"); #LL11good -- 66
LL11bad=getFromDisk("fam11Failure"); #LL11bad -- 91
run "rm fam11Failure"
elapsedTime fam11b=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>2); -- 3538.4s elapsed
LL11good=getFromDisk("fam11");#LL11good -- 95
LL11bad=getFromDisk("fam11Failure");#LL11bad -- 62

run "rm fam11Failure"
elapsedTime fam11b=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>3); -- 5485.16s elapsed
LL11good=getFromDisk("fam11");#LL11good -- 108
LL11bad=getFromDisk("fam11Failure");#LL11bad -- 49
LL11bad=select(LL11bad,Lb->not member(Lb_0,LL11good));#LL11bad


run "rm fam11Failure"
fam11c=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>4);
LL11good=getFromDisk("fam11");#LL11good -- 120
LL11bad=getFromDisk("fam11Failure");#LL11bad -- 37
run "rm fam11Failure"

elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>5);
LL11good=getFromDisk("fam11");#LL11good -- 126

LL11bad=getFromDisk("fam11Failure");#LL11bad -- 31
run "rm fam11Failure"
elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>5);-- 6975.39s elapsed

LL11good=getFromDisk("fam11");#LL11good -- 128
LL11bad=getFromDisk("fam11Failure");#LL11bad --  29
run "rm fam11Failure"
elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>6); -- 7110.24s elapsed

LL11good=getFromDisk("fam11");#LL11good --  130
LL11bad=getFromDisk("fam11Failure");#LL11bad -- 27
run "rm fam11Failure"
fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>6);
LL11good=getFromDisk("fam11");#LL11good -- 134
LL11bad=getFromDisk("fam11Failure");#LL11bad --  23
run "rm fam11Failure"
elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>4);-- 38947.9s elapsed
LL11good=getFromDisk("fam11");#LL11good -- 135
LL11bad=getFromDisk("fam11Failure");#LL11bad -- 22

----

newBounds11=getFromDisk("nbounds11");#newBounds11
LL11bad=newBounds11;
LL11good=getFromDisk("fam11");#LL11good
LL11bad=select(LL11bad,Lb->not member(Lb_0,LL11good));#LL11bad

elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>2,CoeffBound=>10^4);
LL11good=getFromDisk("fam11");#LL11good 
LL11bad=getFromDisk("fam11Failure");#LL11bad 
LL11good=getFromDisk("fam11");#LL11good

newBounds11=getFromDisk("nbounds11");#newBounds11
LL11bad=newBounds11;
LL11good=unique getFromDisk("fam11");#LL11good
LL11bad=select(LL11bad,Lb->not member(Lb_0,LL11good));#LL11bad

elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>3,CoeffBound=>10^4);
LL11good=getFromDisk("fam11");#LL11good 
LL11bad=getFromDisk("fam11Failure");#LL11bad 
LL11good=getFromDisk("fam11");#LL11good

newBounds11=getFromDisk("nbounds11");#newBounds11
LL11bad=newBounds11;
LL11good=getFromDisk("fam11");#LL11good
LL11bad=select(LL11bad,Lb->not member(Lb_0,LL11good));#LL11bad
netList LL11bad

elapsedTime fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>4,CoeffBound=>10^4);
LL11good=getFromDisk("fam11");#LL11good 
LL11bad=getFromDisk("fam11Failure");#LL11bad 
LL11good=getFromDisk("fam11");#LL11good


X="fam11.dbm"
Y=openDatabase X
#unique keys Y
2*#LL11good
ListOfIdeals=apply(LL11good,L->(R=value Y#(toString L|"ring");I=value (Y#(toString L|"ideal"))));
ListOfIdeals_0,degrees ring ListOfIdeals_0
-*
run "ls -l"
run "rm fam11"
run "rm fam11Failure"
run "rm fam11.dbm"
run "ls -l"
*-

///
end--

restart
needsPackage "SmoothingFamilies"
debug("SmoothingFamilies.m2")
(L,b)=({7, 10, 13, 15, 16, 18}, 10)
(L,b)=({8, 9, 11, 13, 23}, 9)
getSmoothingFamily(L,b,CoeffSize=>3)

 newBounds11=getFromDisk("nbounds11");#newBounds11
LL11bad=newBounds11;#LL11bad
LL11good=getFromDisk("fam11");#LL11good
LL11bad=select(LL11bad,Lb->not member(Lb_0,LL11good));#LL11bad

LL11badSmall=newBounds11;
--apply(LL11bad,(L,b)->testWeierstrass(L,b,Verbose=>true))
elapsedTime fam11d=produceSmoothingFamilies(LL11badSmall,"fam11small","fam11small.dbm",CoeffSize=>5,CoeffBound=>10^4);
 -- 5261.25s elapsed
tally apply (fam11d,(b,J)->class J)

run "rm fam11Small"
run "rm fam11SmallFailure"
run "rm fam11Small.dbm"






installPackage "SmoothingFamilies"
viewHelp "SmoothingFamilies"


-* Computation section *-
restart
needsPackage "SmoothingFamilies"
LL11=select(findSemigroups 11,L->not knownExample L);#LL11
fam11=getFromDisk( "fam11");#fam11
fam11=unique fam11;#fam11
LL11toDo=select(LL11,L->not member(L,fam11));#LL11toDo
netList LL11toDo
last LL11toDo
LL11toDo_0

newBounds11=getFromDisk("nbounds11");#newBounds11
select(newBounds11, (L,b)-> L=={9, 11, 12, 13, 15, 16, 17})
LL11bad=newBounds11;#LL11bad

--elapsedTime fam11=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",
--   CoeffSize=>3,CoeffBound=>10^4);

LL11good=getFromDisk("fam11");#LL11good
LL11bad=select(newBounds11,Lb->not member(Lb_0,LL11good));#LL11bad
netList LL11bad
LL11bad_2
assert(#LL11good+#LL11bad==#newBounds11)

elapsedTime fam11=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",
    CoeffSize=>3,CoeffBound=>10^4);
#LL11bad
elapsedTime fam11=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",
    CoeffSize=>3,CoeffBound=>10^4);
netList LL11bad








------- with range
restart
needsPackage "SmoothingFamilies"
newBounds11=getFromDisk("nbounds11");#newBounds11
last newBounds11
LL11bad=newBounds11;#LL11bad
LL11good=getFromDisk("fam11");#LL11good
LL11bad=select(newBounds11,Lb->not member(Lb_0,LL11good));#LL11bad
X="fam11.dbm"
Y=openDatabaseOut X
keys Y
elapsedTime fam11d=produceSmoothingFamilies(LL11bad_{3},"fam11","fam11.dbm",
    CoeffSize=>3,CoeffBound=>10^4);


(L,b)=LL11bad_3
elapsedTime bJ3fs=getSmoothingFamilies(L,b,BaseField=>ZZ/nextPrime 10^3);

fib=ideal bJ3fs_1_2
betti res fib == betti res semigroupIdeal L
(ms,C)=coefficients gens fib;
ms
unique flatten entries C
support fib/degree
fib_0
fib_1
elapsedTime apply(LL11bad,(L,b)->(LJ3fam2s=elapsedTime getSmoothingFamilies(L,b);
        <<positions(LJ3fam2s,(s,J3,fam2)->s);
	J3fam2s=select(LJ3fam2s,(s,J3,fam2)->s);
	<<#J3fam2s))
	
LJ3fam2s=getSmoothingFamilies(L,b);
tally apply(LJ3fam2s,(s,J3,fam2)->s)
J3fam2s=select(LJ3fam2s,(s,J3,fam2)->s);
J3=J3fam2s_1_1
codim J3, numgens J3
fJ3=res J3
betti fJ3
kk=coefficientRing ring J3
R=kk[support J3]
JR=sub(J3,R)
betti res JR
dim JR, codim JR, #support JR
------------- finish bounds
bounds11=getFromDisk("bounds11");
#bounds11
bounds11a=select(bounds11,(L,b)->semigroupGenus L == 11)
LL11=findSemigroups 11;
#LL11
LL11toDo=select(LL11,L->not knownExample L);
#LL11toDo
bounds11a=append(bounds11a,(LL11toDo_7,0))
LLdifficult={{6, 8, 17, 19, 21},
    {6, 8, 10, 19, 21, 23},
    {6, 9, 11, 14},{8, 9, 11, 15, 21}}

LL11done=unique apply(bounds11a,(L,b)->L)|LLdifficult
reallyToDo11= select(LL11toDo,L->not member(L,LL11done));
#reallyToDo11

newBounds11=getFromDisk("nbounds11");
#newBounds11
bounds11b=newBounds11|bounds11a
#bounds11b

LL11diffa={{8, 10, 12, 14, 15, 19, 21},{8, 9, 12, 13, 19, 23},{10, 11, 12, 13, 14, 16, 18, 19}}
reallyToDo11a=select(reallyToDo11,L->not member(L,LL11diffa));
#reallyToDo11a
#reallyToDo11a-#newBounds11
tB11=continueComputation(produceBounds,reallyToDo11a,"nbounds11")

LL11diffa
LL11diffb=produceBounds(LL11diffa,"nbounds",Verbose=>true)

--- computing 16 out of 20 families
newBounds11=getFromDisk("nbounds11");
LL=newBounds11_{0..19}
fam11a=produceSmoothingFamilies(LL,"fam11","fam11.dbm",Verbose=>true,CoeffSize=>1)
LL11good=getFromDisk("fam11")
LL11bad=getFromDisk("fam11Failure")
run "rm fam11Failure"
fam11b=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",Verbose=>true,CoeffSize=>2)
LL11good=getFromDisk("fam11");#LL11good
LL11bad=getFromDisk("fam11Failure");#LL11bad

run "rm fam11Failure"
fam11b=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",Verbose=>true,CoeffSize=>3)
LL11good=getFromDisk("fam11");#LL11good
LL11bad=getFromDisk("fam11Failure");#LL11bad

run "rm fam11Failure"
fam11c=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",Verbose=>true,CoeffSize=>4)
LL11good=getFromDisk("fam11");#LL11good
LL11bad=getFromDisk("fam11Failure");#LL11bad
run "rm fam11Failure"
fam11d=produceSmoothingFamilies(LL11bad,"fam11","fam11.dbm",CoeffSize=>5)
LL11good=getFromDisk("fam11");#LL11good
LL11bad=getFromDisk("fam11Failure");#LL11bad



X="fam11.dbm"
Y=openDatabase X
#keys Y,#unique getFromDisk("fam11")
Z="fam11l.dbm"
W=openDatabase Z
#keys W
ListOfIdeals=apply(LL11good,L->(R=value Y#(toString L|"ring");I=value (Y#(toString L|"ideal"))));
ListOfIdeals_0,degrees ring ListOfIdeals_0


---------------
restart
needsPackage "SmoothingFamilies"
LL13=findSemigroups 13;
LL13toDo=select(LL13,L->not knownExample L);
#LL13toDo


