--How the known examples arise:
restart
needsPackage "WeierstrassSemigroups"
elapsedTime LL = flatten apply(13, g->
    findSemigroups g);#LL --1413

isKnownExample = method()
isKnownExample List := Boolean => L ->(
    #L <= 3 or
    genus L < 8 or
    min L < 6 or 
    (#L == 4 and
    isSymmetric L) or
    ewt L < genus L
    )
elapsedTime analysis = for g from 0 to 12 list(
    -- total, known, Mult<6, Numgens<4, gor3
    Lg = findSemigroups g;
    kLg = select(Lg, L -> isKnownExample L);
    smallMult = select(Lg, L-> min L <6);
    smallNumgens = select(Lg, L -> #L<4);
    
    gor3 = select(Lg, L -> #L == 4 and isSymmetric L);
    smallWeight = select(Lg, L -> weight L < genus L);
    smallEWT = select(Lg, L -> ewt L < genus L);
    (#Lg, #kLg, #smallMult, #smallNumgens, #gor3,#smallWeight,#smallEWT)
    ) -- 305 sec for g = 8 to 15
netList analysis
--total, known, Mult<6, Numgens<4, gor3,smallWeight, smallEWT
      +-------------------------------+
o15 = |(1, 1, 1, 1, 0, 0, 0)          |
      +-------------------------------+
      |(1, 1, 1, 1, 0, 1, 1)          |
      +-------------------------------+
      |(2, 2, 2, 2, 0, 2, 2)          |
      +-------------------------------+
      |(4, 4, 4, 3, 0, 3, 4)          |
      +-------------------------------+
      |(7, 7, 7, 5, 0, 5, 7)          |
      +-------------------------------+
      |(12, 12, 11, 5, 1, 9, 12)      |
      +-------------------------------+
      |(23, 23, 17, 9, 1, 13, 19)     |
      +-------------------------------+
      |(39, 39, 21, 9, 1, 22, 30)     |
      +-------------------------------+
      |(67, 58, 26, 13, 1, 33, 45)    |
      +-------------------------------+
      |(118, 88, 32, 14, 2, 49, 67)   |
      +-------------------------------+
      |(204, 127, 40, 20, 3, 73, 97)  |
      +-------------------------------+
      |(343, 172, 44, 15, 2, 106, 139)|
      +-------------------------------+
      |(592, 247, 56, 27, 5, 151, 195)|
      +-------------------------------+
sum(analysis, a -> toList a)
--{1413, 781, 262, 124, 16, 467, 618}
--618-467 == 151, 1413-781 == 632
sum (for g from 0 to 7 list  #findSemigroups g
)
--numgens <=4
LLTwoGens = select(LL, L ->
    #L <= 2);#LLTwoGens --25 Pinkham
LLThreeGens = select(LL, L ->
    #L == 3);#LLThreeGens --99 Pinkham+Schaps
LLGor3 = select(LL, L->
    #L == 4 and
    isSymmetric L);#LLGor3 -- 16 Waldi
 
--numgens >=5
LLSmallMult = select(LL, L ->
    #L >=4 and
    not(#L == 4 and isSymmetric L) and
    min L < 6);#LLSmallMult --143

LLSmallWt = select(LL, L ->
    #L >=4 and
    not(#L == 4 and isSymmetric L) and
    min L >= 6 and
    weight L < genus L
    );#LLSmallWt --423

LLSmallEWt = select(LL, L ->
    #L >=4 and
    not(#L == 4 and isSymmetric L) and
    min L >= 6 and
    weight L >=  genus L and
    ewt L < genus L
    );#LLSmallEWt --73
LLSmallGenus = select(LL, L ->
    #L >=4 and
    not(#L == 4 and isSymmetric L) and
    min L >= 6 and
    ewt L >= genus L and
    genus L < 8);#LLSmallGenus -- 2

25+99+16+143+423+73+2 == 781
781+632 == 1413

uninstallPackage "NumericalSemigroups"
restart
needsPackage "NumericalSemigroups"
peek loadedFiles
viewHelp isKnownExample

needsPackage "WeierstrassSemigroups"
g = 21
L = {6,15,g-1,g+2}
g = 24

for g from 20 to 30 list(
    L = {6,15,g-1,g+2};
    if g%3 == 1 then continue else
    genus L == g and
satisfiesDegreeCondition1 L and
satisfiesDegreeCondition2 L and
hasExactSubcomplex L)


#LL
