newPackage(
    "YoungReps",
    Version => "1.1",
    Date => "October, 2023",
    Authors => {{Name => "Jacob Zoromski", Email => "jzoromsk@nd.edu"}},
    Headline => "Representations of Young subgroups of the symmetric group",
    PackageExports => {"SchurRings"},
    DebuggingMode => false
    )

export {
    "youngRing",
    "induction",
    "dimRep",
    "LRCoeff",  
    "restriction",
    "contingencyTables",
    "youngTensor"
}


--code section


---SETUP - Handling Young representation----------------------------------------------------------------------------------------------



--Create a schur ring of schur level n with symbols t1,...,tn over QQ with Sn group action
youngRing = method()
youngRing (ZZ) := Ring => (n) -> (
    T := schurRing(QQ,getSymbol("t1"),n,GroupActing => "Sn");
    for i from 1 to n-1 do T = schurRing(T,getSymbol(concatenate("t",toString((schurLevel T)+1 ))),n,GroupActing => "Sn");
    T
    )

--Create a schur ring of schurlevel n with symbols s1,...,sn over QQ with GLn group action
youngRingGLn = (n) -> (
    T := schurRing(QQ,getSymbol("s1"),n);
    for i from 1 to n-1 do T = schurRing(T,getSymbol(concatenate("s",toString((schurLevel T)+1 ))),n);
    T
    )

--given a schur ring of schur level m, outputs the coefficient ring with the designated schur level n <=m
toSchurLevel = (S,n) -> (
    T := S;
    while schurLevel T > n do T = coefficientRing T;
    T
    )

--moves a rep of from its current ring to the gens of the given ring T (using listForm, i.e. just changing the highest schurLevel part)
changeRing = (T,rep) -> (
    sum apply(listForm rep, A -> (A#1)*T_(A#0))
    )

--converts a representation from GLn to Sn or from Sn to GLn
--if input is a Young GLn ring, then convert to GLn
--if input is a Young Sn ring, then convert to Sn
convert = (U,rep) -> (
    toS(rep,toSchurLevel(U,schurLevel ring rep))
    )

--lists the summands of a representation
--Remark: sums are split across the highest Schur level part by default
summands = (rep) -> (
    apply(listForm rep, (lambda,r) -> r*((ring rep)_lambda))
    )
        
--split a one term rep into irreducibles
irred = (rep) -> (
    T := ring rep;
    if schurLevel T > 1 then (
	A := {(ring rep)_((listForm(rep))#0#0),(listForm(rep))#0#1}; --split rep into a list of form {last part, first part}
	flatten((A#0)*(toList apply(summands(A#1), v -> irred(v))))
	)
    else {rep}
    )

--split an arbitrary rep into irreducibles
irreducibles = (rep) -> (
    flatten(toList(apply(summands(rep), v -> irred(v))))
    )

--determine which Young subgroup a representation belongs
subgroup = (rep) -> (
    apply((splitRep(rep))#0, v -> sum (listForm(v))#0#0)
    )

--remove the last s_() from an irrep. This helps keep representations in the expected Schur level
reduce = (rep) -> (
    L := listForm rep;
    lambda := (L#0)#0;
    newRep := rep;
    while #lambda == 0 do (
    	newRep = (L#0)#1;
	L = listForm newRep;
	lambda = (L#0)#0;
	);
    newRep
    )



---INDUCTION SECTION-------------------------------------------------------------------------------



--Induction from a Young subgroup H to a subgroup G of S_n, where if H = {a_1,\dots,a_k} 
--corresponds to the subgroup S_a1 x ... x S_ak and Reps is a list of representations corresponding
--to the factors of H, all generators of the same schur ring
ind = (Reps,H,G) -> (
    j := 0;
    newReps := new List;
    R := schurRing(QQ,getSymbol("s"),sum G); --convert to GLn so that multiplication in Gln = induction in Sn
    GLreps := apply(Reps,r -> ((listForm(r))#0#1)*R_((listForm(r))#0#0) );
    for i from 0 to #G-1 do (
	     goalSize := G#i;
	     currentSize := H#j;
	     currentRep := GLreps#j;
	     while currentSize < goalSize do (
	    	 j = j + 1;
	    	 currentRep = currentRep*(GLreps#j);
	    	 currentSize = currentSize + H#j;
		 );
	     newReps = append(newReps,currentRep);
	     j = j + 1;
	     );
     newReps
     )

--split a Young irrep into its component pieces along exterior products
splitIrrep = (rep) -> (
    T := ring rep;
    if schurLevel(T) == 1 then return {rep};
    lambda := ((listForm rep)#0)#0; 
    currentList := {T_lambda};
    currentRep := ((listForm rep)#0)#1;
    while schurLevel(T) > 1 do (
	T = coefficientRing T;
	if schurLevel(T) > 1 then (
	    currentList = {sum apply(listForm currentRep, (mu,r) -> T_mu)}| currentList;
	    )
	else currentList = {sum apply(listForm currentRep, (mu,r) -> r*T_mu)}| currentList;
	currentRep = ((listForm currentRep)#0)#1;
	);
    currentList
    )

--splits all irreducibles of a representation into its exterior product parts
--output a list of lists of split irreducibles ala splitIrrep
splitRep = (rep) -> (
    apply(irreducibles(rep), r -> splitIrrep(r))
    )

--Given a list a component parts of a representation, swap all the symbols according to the permutation,
-- e.g. Perm = {2,4} means change s1 to s2 and change s2 to s4
swap = (S,Reps,Perm) -> (
    toList apply(0..(#Reps-1), i -> changeRing(toSchurLevel(S,Perm#i),Reps#i))
    )

 
--induction of a Young representation to a Young subgroup G containing it.
--Note that G has to be obtained by combining adjacent elements of the subgroup H of which rep is a representative
--For example, if rep is a representation of H = {2,1,3} it is possible to induce up to
--{2,1,3},{3,3},{2,4} and {6} but not {5,1}
induction = method()
induction (Ring,RingElement,List) := RingElement => (S,rep,G) -> (
    H := subgroup(rep);
    n := sum H;
    splitIrreducibles := splitRep(rep);
    schurLevelOne := apply(splitIrreducibles, splitList -> apply(splitList, r -> reduce(changeRing(toSchurLevel(S,1),r)))); --take all elements in the lists to schur level one
    induceUp := apply(schurLevelOne, L -> ind(L,H,G)); --which allows us to use ind
    restored := apply(induceUp, inducted -> product swap(S,inducted,toList(1..#inducted))); --return to proper schur level and combine
    sum restored
    )

--compute the dimension of a young rep as an Sn representation, i.e. induce up to Sn
dimRep = method()
dimRep (RingElement) := ZZ => (rep) -> (
    dim induction(ring rep, rep, {sum subgroup(rep)})
    )



----BEGIN RESTRICTION SECTION----------------------------------------------------------------------



--The partitions of n in list form
totalParts = (n) -> (
    L := apply(partitions n, lambda -> new List from lambda)
    )

--computes the littlewood-richardson coefficient of nu with respect to lambda and mu
LRCoeff = method()
LRCoeff (List,List,List) := QQ => (lambda,mu,nu) -> (
    S := schurRing(QQ,getSymbol("s"),sum nu);
    n := 0;
    apply(listForm(S_lambda*S_mu), (u,v) -> if u == nu then n = v);
    n
    )

--Restrict an irrep from S_n to S_a x S_b
simpleRestrict = (S,rep,a,b) -> (
    Hreps := (totalParts(a))**(totalParts(b));
    T := toSchurLevel(S,schurLevel(ring rep));
    T' := toSchurLevel(S,schurLevel(ring rep)+1);
    sum apply(listForm rep, (r,c) -> c * sum apply(Hreps, (u,v) -> LRCoeff(u,v,r)*(T_u)*(T'_v)))
    )


--Restrict an irrep from S_n to an arbitrary Young subgroup H
nToHRestrict = (S,rep,H) -> (
    n := sum H;
    newRep := rep;
    for i from 0 to #H-2 do (
	n = n-H#i;
        newRep = simpleRestrict(S, reduce(newRep), H#i, n);
	);
    newRep
    )

--restrict from S_n to an arbitary subgroup H, with corresponding subgroups belonging to schur levels in list L
swapRestrict = (S,rep,H,L) -> (
    --we restrict first
    newRep := nToHRestrict(S,rep,H);
    --Then we swap
    swapped := apply(splitRep(reduce(newRep)), A -> swap(S,A,L));
    --Then we recombine
    sum apply(swapped, B -> product B)
    )

--helper function for restriction
--produce to a new list based on the subgroup H to restrict to, that is the same as H, but has numbers 1,2,3,etc. in order
simplerList = (H) -> (
    lengthSoFar := 0;
    toList apply(0..#H-1, j -> (
    	    currentLength := #(H#j);
	    A := toList(1..currentLength) + toList(currentLength:lengthSoFar);
	    lengthSoFar = lengthSoFar + currentLength;
	    A)
	)
    )

--Restrict a representation to a subgroup H (given as a list of lists separated by exterior tensor)
restriction = method()
restriction (Ring,RingElement,List) := RingElement => (S,rep,H) -> (
    L := simplerList(H);	
    toReduce := apply(splitRep(rep), A -> apply(A, v -> changeRing(toSchurLevel(S,1),v)));
    reduced := toList apply(0..#toReduce-1, i -> toList apply(0..#(toReduce#0)-1, j -> swapRestrict(S,(toReduce#i)#j,H#j,L#j)));
    sum apply(reduced, A -> product A)
    )
 	


----BEGIN TENSORING SECTION-------------------------------------------------------------------------------------------------------------



--Given a partition (as a list), find the stabilizing subgroup
stab = (L) -> (
    subgroup := new List;
    j := 1;
    for i from 0 to #L-1 do (
	if i < #L-1 and L#i == L#(i+1) then j = j + 1 else (
	    subgroup = append(subgroup,j);
	    j = 1;
	    );
	);
    subgroup
    )

--finds the order of the orbit of a partition under the Sn action
ordOrbit = (L) -> (
    ((#L)!) // product apply(stab(L), i -> i!)
    )

--split an irrep such that each term is in schur level 1
forgetSplit = (rep) -> (
    T := ring rep;
    if schurLevel(T) == 1 then return {rep};
    L1 := toSchurLevel(T,1);
    lambda := ((listForm rep)#0)#0; 
    currentList := {L1_lambda};
    currentRep := ((listForm rep)#0)#1;
    while schurLevel(T) > 1 do (
	T = coefficientRing T;
	if schurLevel(T) > 1 then (
	    currentList = {sum apply(listForm currentRep, (mu,r) -> L1_mu)}| currentList;
	    )
	else currentList = {sum apply(listForm currentRep, (mu,r) -> r*L1_mu)}| currentList;
	currentRep = ((listForm currentRep)#0)#1;
	);
    currentList
    )

--Compute the list Gamma^BA associated to positive compositions alpha and beta
gammaAB  = (alpha,beta) -> (
    --Step1: Create permutational multidegrees lambda,mu corresponding to alpha,beta
    --the actual multidegree doesn't matter, so long as the stabilizers match alpha and beta
    count := (sum alpha) + 1;
    lambda := flatten apply(alpha, i -> (
	    count = count - 1;
	    toList(i:count)
	    )
	);
    count = (sum beta) + 1;
    mu := flatten apply(beta, i -> (
	    count = count - 1;
	    toList(i:count)
	    )
	);
    --Step 2: Find permutations of mu that give double cosets representatives of H_alpha \ Sn / H_beta
    --This can be done by assuming lambda,mu are general (lambda_i + mu_j  = lambda_k + mu_l implies (i,j) = (k,l))
    --and find the permutations of mu such that, when added to lambda, give distinct sums up to permutation
    Pairs := unique apply(unique permutations mu, P -> rsort toList apply(0..#lambda-1, i -> (lambda#i,P#i)));
    permsMu := apply(Pairs, A -> toList apply(A, B -> B#1)); -- permutations of Mu corresponding to double coset reps
    --Step 3: Compute all Gamma^B's
    K := rsort unique mu;
    bIndices := new HashTable from toList apply(0..#(K)-1, i -> (K#i,i+1));
    gammaB := apply(permsMu, M -> apply(M, a -> bIndices#a));
    --Step 4: Compute all Gamma^BA's
    G := stab(lambda);
    apply(gammaB, D -> (
	    k := -1;
	    toList apply(0..#G-1, j -> sort toList apply(0..(G#j)-1, i -> (
			k = k + 1;
			D#k
			)
		    )
		)
	    )
	)
    )


--Compute the contingency tables associated to alpha and beta in list form
contingencyColumns = (alpha,beta) -> (
    numCols := #beta;
    apply(gammaAB(alpha,beta), G -> (
	    tallies := apply(G, L -> tally L);
	    toList apply(0..#tallies-1, i -> (
		    toList apply(1..numCols, j -> if (tallies#i)#?j then (tallies#i)#j else 0)
		    )
		)
	    )
	)
    )

--Compute the contingency tables associted to lambda and mu in matrix form
contingencyTables = method()
contingencyTables (List,List) := List => (alpha,beta) -> (
    apply(contingencyColumns(alpha,beta), A -> transpose matrix A)
    )

--calculate the degree decorations for a contingency table associated to lambda and mu
--That is, lambda_j corresponds to column j and mu_i corresponds to row i
--The (i,j) entry of the result is mu_i + lambda_j
degreeTable = (lambda,mu) -> (
    colDegs := unique lambda;
    rowDegs := unique mu;
    matrix toList apply(0..#rowDegs - 1, i -> (
	    toList apply(0..#colDegs - 1, j -> colDegs#j + rowDegs#i)
	    )
	)
    )

--Given a contingency table determined by multidegrees lambda and mu,
--Tell which index (Schur level) each copy of the symmetric group in the common subgroup should have.
--While this can be done arbitrarily, the idea is to label indices with the same multidegree 
--adjacent to each other to make the induction function work.
indexTable = (M,lambda,mu) -> (
    colDegs := unique lambda;
    rowDegs := unique mu;
    x := symbol x;
    y := symbol y;
    R := QQ[x,y]; --dummy variables to order degrees by grlex
    sortedData := rsort toList apply((0,0)..(#rowDegs-1,#colDegs-1), (i,j) -> {x^(rowDegs#i)*y^(colDegs#j),M_(i,j),(i,j)} );    
    nonZeroEntries := select(sortedData, X -> X#1 > 0);
    orderedEntries := apply(0..#nonZeroEntries-1, i -> {flatten exponents(nonZeroEntries#i#0),nonZeroEntries#i#2,i+1});
    result := mutableMatrix matrix map(ZZ^(#rowDegs),ZZ^(#colDegs),0);
    apply(orderedEntries, Y -> result_(Y#1) = Y#2);
    matrix result
    )
    
    


--Compute the proper groups to restrict row and column reps to, given a contingency table M
--Outputs a list of lists of the form {{colResList,colIndexList},{rowResList,colIndexList}}
--telling where the ith entry of each list tells where the ith row/column rep restricts to and, respectively the index (Schur level)  of that copy of Sn
groupRestrict = (M,lambda,mu) -> (
    indexMatrix := indexTable(M,lambda,mu);
    colResList := toList apply(0..numColumns M - 1, i -> (
	    select(toList apply(0..numRows M - 1, k -> M_(k,i)), a -> a > 0)
	    )
	);
    rowResList := toList apply(0..numRows M - 1, k -> (
	    select(toList apply(0..numColumns M - 1, i -> M_(k,i)), a -> a > 0)
	    )
	);	
    colIndexList := toList apply(0..numColumns M - 1, i -> (
	    select(toList apply(0..numRows M - 1, k -> indexMatrix_(k,i)), a -> a > 0)
	    )
	);
    rowIndexList := toList apply(0..numRows M - 1, k -> (
	    select(toList apply(0..numColumns M - 1, i -> indexMatrix_(k,i)), a -> a > 0)
	    )
	);	
    {{colResList,colIndexList}, {rowResList,rowIndexList}}
    )

--compute the part of the tensor product two multigraded Young irreps corresponding
--to a fixed contingency table T
tableTens = (S,Rep1,Rep2,T) -> (
    result := new List;
    rep1 := Rep1#0;
    deg1 := Rep1#1;
    rep2 := Rep2#0;
    deg2 := Rep2#1;
    --Step1: Restrict to the appropriate common group
    colReps := forgetSplit(rep1);
    rowReps := forgetSplit(rep2);
    restrictLists := groupRestrict(T,deg1,deg2);
    colRestrictList := toList apply(0..#colReps - 1, i -> {colReps#i,restrictLists#0#0#i,restrictLists#0#1#i});
    rowRestrictList := toList apply(0..#rowReps - 1, j -> {rowReps#j,restrictLists#1#0#j,restrictLists#1#1#j});
    restrictedCols := product apply(colRestrictList, A -> swapRestrict(S,A#0,A#1,A#2));
    restrictedRows := product apply(rowRestrictList, B -> swapRestrict(S,B#0,B#1,B#2));
    --Step2: Tensor
    tensored := restrictedCols*restrictedRows;
    --Step3: Compute the new degree
    degTable := degreeTable(deg1,deg2);
    newDeg := delete(,flatten flatten toList apply(0..numRows T - 1, i -> (
	    	toList apply(0..numColumns T - 1, j -> if T_(i,j) > 0 then toList(T_(i,j):(degTable_(i,j))))
	    	)
	    )
    	);
    --Step4: Induce up to the stabilizer of the new degree
    currentGroup := subgroup(tensored);
    degGroup := stab(rsort newDeg);
    if rsort currentGroup != rsort degGroup then (
	result = {induction(S,tensored,degGroup),rsort newDeg};
	)
	else result = {tensored,rsort newDeg};   
    result
    )
    

--tensors two multigraded Young irreps
simpleTens = (U,Reps,Degs) -> (
    P := 0; -- Multideg that will be permuted
    F := 0; -- Multideg that will be fixed
    --we will fix the multidegree with the smaller orbit and permute the other one for efficiency's sake
    if ordOrbit(Degs#0) <= ordOrbit(Degs#1) then F = 1 else P = 1; 
    apply(contingencyTables(stab(Degs#F),stab(Degs#P)), T -> tableTens(U,{Reps#F,Degs#F},{Reps#P,Degs#P},T))
    )

--combine terms with the same multidegree, given a list of lists of the form {rep,degree}
likeTerms = (L) -> (
    degs := unique apply(L, A -> A#1);
    apply(degs, d -> {sum apply(select(L, B -> B#1 == d), A -> A#0),d})
    )

--tensor two multigraded Young reps, each corresponding to one multidegree, together
oneTermTens = (U,L,M) -> (
    rep1 := L#0;
    rep2 := M#0;
    deg1 := L#1;
    deg2 := M#1;
    A := apply(irreducibles(rep1)**irreducibles(rep2), (a,b) -> simpleTens(U,{a,b},{deg1,deg2}));
    likeTerms(toList apply(0..#(A#0)-1, i -> {sum apply(A,B -> (B#i)#0), ((A#0)#i)#1}))
    )

--tensor two arbitrary multigraded Young representations
--L, M are lists of lists of the form {rep,degree}
youngTensor = method()
youngTensor (Ring,List,List) := List => (U,L,M) -> (
    if instance(L#0,RingElement) then return oneTermTens(U,L,M) else likeTerms(flatten flatten apply(L, A -> apply(M, B -> (
		    oneTermTens(U,A,B)
		    )
		)
	    )
	)
    )   

-----------------------------------------------------------------------------------------------------------------------------------------------------------------
beginDocumentation()

doc ///
Key
 youngRing
 (youngRing, ZZ)
Headline
 Creates a Young ring, the representation ring of n copies of the symmetric group Sn.
Usage
 yR = youngRing(n)
Inputs
 n: ZZ
Outputs
 yR: Ring
Description
  Text
   A Young ring is the representation ring QQ[(Sn)^n]. This ring is meant
   to handle representations of Young subgroups of Sn, i.e. reps of Sa1 \times Sa2 \times ...
   \times SaL (v1)*(v2)*...*(vL) where (a1,...,aL) is a composition of n and 
   vi is a representation of Sai. 
   These representations are standins for their induced representations in Sn, called Young representations.
  Example
   A = youngRing(3)
   v = 2*t1_1*t2_1*t3_1
   w = t1_{1,1}*t2_1
///

doc ///
Key
 induction
 (induction, Ring, RingElement, List)
Headline
 Computes the induced representation from a Young subgroup to another Young Subgroup G containing it.
Usage
 inducedRep = induction(U,rep,G)
Inputs
 U: Ring
 rep: RingElement
 G: List
Outputs
 inducedRep: RingElement
Description
  Text
   Given a Young representation v corresponding to a subgroup H, another subgroup  G = {b_1,...,b_M}
   containing H, and U its Young ring, compute its induction up to G. Note that G has to be obtained by combining
   adjacent elements of the subgroup H of which rep is a representative.
   For example, if rep is a representation of H = {2,1,2} it is possible to induce up to
   {2,1,2},{2,3},{3,2}, and {5} but not {4,1}
  Example
   A = youngRing(5)
   v = t1_{2}*t2_1*t3_{1,1}
   induction(A,v,{3,2})
   induction(A,v,{2,3})
   induction(A,v,{5})
///

doc ///
Key
 dimRep
 (dimRep, RingElement)
Headline
 Computes the dimension (as an Sn-representation) of a Young representation.
Usage
 d = dimRep(rep)
Inputs
 rep: RingElement
Outputs
 d: ZZ
Description
  Text
   Given a representation v of a Young subgroup Sa1 x ... x SaL, find its dimension as an Sn
   rep, where n = a1 + ... + aL. That is, find the dimension of v when induced up to Sn.
  Example
   A = youngRing(3)
   v = t1_1*t2_1*t3_1
   induction(A,v,{3})
   dimRep(v)
   w = t1_2*t2_1
   induction(A,w,{3})
   dimRep(w)
///

doc ///
Key
 LRCoeff
 (LRCoeff, List, List, List)
Headline
 Computes the Littlewood-Richardson coefficient of L_{lambda,mu}^nu.
Usage
 coeff = LRCoeff(lambda,mu,nu)
Inputs
 lambda: List
 mu: List
 nu: List
Outputs
 coeff: QQ
Description
  Text
   Given partitions lambda,mu of a,b respectively and a partition nu of a+b, compute the
   Littlewood-Richardson coefficient of nu with respect to lambda and mu. This is the number
   of copies of s_nu appearing in the induced representation of s_lambda x s_mu up to Sn. Alternatively,
   by Frobenius reciprocity, it is the number of copies of s_lambda x s_mu appearing in the 
   restriction of s_nu to Sa x Sb.
  Example
   LRCoeff({2,1},{1},{2,1,1})
   LRCoeff({2,1},{1},{1,1,1,1})
   LRCoeff({2,1},{2,1},{3,2,1})
///

doc ///
Key
 restriction
 (restriction, Ring, RingElement, List)
Headline
 Computes the restriction of a Young representation to a smaller Young subgroup H.
Usage
 restrict = restriction(U,rep,Groups)
Inputs
 U: Ring
 rep: RingElement
 Groups: List
Outputs
 restrict: RingElement
Description
  Text
   Given a Young representation rep, U its Young ring, and Groups a list of lists 
   corresponding to which Young subgroup each component of rep is meant to be restricted,
   restrict rep to the corresponding Groups.
  Example
   A = youngRing(4)
   w = t1_{2,2}
   restriction(U,w,{{2,2}})
   w' = t1_{2,1,1}
   restriction(U,w',{{2,2}})
   v = t1_1*t2_{1,1,1}
   restriction(U,v,{{1},{1,2}})
///

doc ///
Key
 contingencyTables
 (contingencyTables, List, List)
Headline
 Lists all contingency tables with margins (alpha,beta).
Usage
 tables = contingencyTables(alpha,beta)
Inputs
 alpha: List
 beta: List
Outputs
 tables: List
Description
  Text
   Let alpha and beta be positive compositions of a fixed N. That is, all alpha_i are positive integers
   and the sum of all alpha_i is N, and similarly for beta. A contingency table with margins (alpha,beta)
   is a matrix with non-negative integer entries such that the sum of the entries in the ith column
   is alpha_i and the sum of the entries in the jth row is beta_j. They are relevant to statistics,
   combinatorics, and representation theory. This function produces the set of all contingency tables
   with margins (alpha,beta). They are in bijection with double coset representatives of the symmetric
   group Sn with respect to the Young subgroups H_alpha and H_beta.  
  Example
   alpha = {2,2,1}
   beta = {2,3}
   contingencyTables(alpha,beta)
///

doc ///
Key
 youngTensor
 (youngTensor, Ring, List, List)
Headline
 Tensor two multigraded Young representations together.
Usage
 tensored = youngTensor(U,L,M)
Inputs
 U: Ring
 L: List
 M: List
Outputs
 tensored: List
Description
  Text
   Given two multigraded Young representations of the form L = {rep1,deg1} and M = {rep2,deg2}, this function
   computes their tensor product in terms of other multigraded Young representations. The output is a list.
   Representations with the same multidegree are combined, but representations of different 
   multidegrees are separate elements in the list.
   Alternatively, L and M can be lists of multigraded Young representations, corresponding to sums
   of multigraded Young representations of varying degrees.
  Example
   U = youngRing(4)
   rho = {t1_2*t2_{1,1},{1,1,0,0}}
   tau = {t1_1*t2_{2,1},{4,2,2,2}}
   rt = youngTensor(U,rho,tau)
   youngTensor(U,{rho},rt)
///

TEST ///

///

end--


restart
loadPackage "YoungReps"

U = youngRing(5)

--induction demo
v = t1_{2}*t2_1*t3_{1,1}
induction(U,v,{3,2})
induction(U,v,{2,3})
induction(U,v,{5})

--restriction demo
w = t1_{2,2}
restriction(U,w,{{2,2}})
w' = t1_{2,1,1}
restriction(U,w',{{2,2}})

--tensor demo
r1 = {t1_2*t2_{1,1},{1,1,0,0}}
r2 = {t1_1*t2_{2,1},{4,2,2,2}}
youngTensor(U,r1,r2)
r3 = {t1_1*t2_3,{1,0,0,0}}
r4 = {2*t1_1*t2_1*t3_1*t4_1,{3,2,1,0}}
youngTensor(U,r3,r4)



