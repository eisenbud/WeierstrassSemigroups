--How the known examples arise:
restart
needsPackage "NumericalSemigroups"
elapsedTime LL = flatten apply(13, g->
    findSemigroups g);#LL --1413

--numgens <=4
LLTwoGens = select(LL, L ->
    #L <= 2);#LLTwoGens --25
LLThreeGens = select(LL, L ->
    #L == 3);#LLThreeGens --99
LLGor3 = select(LL, L-> #L==4 and
    isSymmetric L);#LLGor3 -- 16
LLnotGor3 = select(LL, L ->
    #L == 4 and
    not isSymmetric L); #LLnotGor3 -- 201

--numgens >=5
LLSmallMult = select(LL, L ->
    #L >=5 and
    min L < 6);#LLSmallMult --46
LLSmallWt = select(LL, L ->
    #L >= 5 and
    min L >= 6 and
    weight L < genus L
    );#LLSmallWt --418
LLSmallEWt = select(LL, L ->
    #L >= 5 and
    min L >= 6 and
    weight L >=  genus L and
    ewt L < genus L
    );#LLSmallEWt --72

25+99+16+201+46+418+72 == 877
