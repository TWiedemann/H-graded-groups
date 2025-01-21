#### Realisation of the root system H4 as a folding of E8

K := CF(5); # Ground field: Rationals adjoined fifth root of unity
gold := (1 + Sqrt(5))/2; # Golden ratio, contained in K

## The root system E8
E8Lie := SimpleLieAlgebra("E", 8, Rationals);
E8Vec := FullRowSpace(K, 8); # Euclidean space containing E8
E8 := RootSystem(E8Lie); # Root system as a GAP object
E8Pos := PositiveRoots(E8);
E8Roots := Concatenation(E8Pos, -E8Pos); # List of roots
# The simple system in the "usual" order:
#     2
#     |
# 1-3-4-5-6-7-8
# i.e.
# 8-7-6-5
#      /
# 1-3-4-2
E8SimStandOrder := SimpleSystem(E8);
E8SimStandOrderBas := Basis(E8Vec, E8SimStandOrder);
# The simple system in the order we use:
#     5
#     |
# 8-6-4-3-2-1-7
# i.e.
# 7-1-2-3
#      /
# 8-6-4-5
E8Sim := E8SimStandOrder{[7, 6, 5, 4, 2, 3, 8, 1]};
E8SimBas := Basis(E8Vec, E8Sim);

E8RootFromNumber := function(rootNum)
	return E8Roots[rootNum];
end;

E8NumberFromRoot := function(root)
	return Position(E8Roots, root);
end;

# D6 as a subsystem of E8
D6Sim := E8Sim{[1..6]};
D6Vec := Subspace(E8Vec, D6Sim);
D6Roots := Filtered(E8Roots, root -> root in D6Vec);
D6Pos := Filtered(E8Pos, root -> root in D6Vec);

# Bilinear form on E8 (and D6)
bilForm := function(root1, root2)
	local coeff1, coeff2, mat;
	coeff1 := Coefficients(E8SimStandOrderBas, root1);
	coeff2 := Coefficients(E8SimStandOrderBas, root2);
	mat := BilinearFormMat(E8);
	return (coeff1*mat)*coeff2;
end;

# Returns Cartan integer of root1 and root2
cartanInt := function(root1, root2)
	return 2 * bilForm(root1, root2) / bilForm(root1, root1);
end;

# Returns \sigma_{root1}(root2), i.e., reflection of root2 along root1
refl := function(root1, root2)
	return root2 - cartanInt(root1, root2) * root1;
end;

## The subspaces W1 and W2 of E8Vec, as defined in [BW, 4.5]
# List of basis vectors
W1BasList := [ E8Sim[4] - gold*E8Sim[2], E8Sim[3] - gold*E8Sim[5], E8Sim[6] - gold*E8Sim[1], E8Sim[8] - gold*E8Sim[7] ];
W2BasList := [ E8Sim[2] + gold*E8Sim[4], E8Sim[5] + gold*E8Sim[3], E8Sim[1] + gold*E8Sim[6], E8Sim[7] + gold*E8Sim[8] ];
# The subspaces
W1 := Subspace(E8Vec, W1BasList);
W2 := Subspace(E8Vec, W2BasList);
# The bases as basis objects in GAP
W1Bas := Basis(W1, W1BasList);
W2Bas := Basis(W2, W2BasList);
E8VecWBas := Basis(E8Vec, Concatenation(W1BasList, W2BasList)); # Basis of E8Vec

## Projection maps
# alpha: Element of E8Vec
# Output: The projection of alpha onto W1 or W2, respectively
projW1 := function(alpha)
	local coeff, vectors;
	coeff := Coefficients(E8VecWBas, alpha);
	vectors := Concatenation(W1BasList, [Zero(E8Vec), Zero(E8Vec), Zero(E8Vec), Zero(E8Vec)]);
	return coeff * vectors;
end;
projW2 := function(alpha)
	local coeff, vectors;
	coeff := Coefficients(E8VecWBas, alpha);
	vectors := Concatenation([Zero(E8Vec), Zero(E8Vec), Zero(E8Vec), Zero(E8Vec)], W2BasList);
	return coeff * vectors;
end;

## Definition of GH3 and H3
GH3Roots := List(D6Roots, projW2);
GH3Pos := List(D6Pos, projW2);
GH4Roots := List(E8Roots, projW2);
GH4Pos := List(E8Pos, projW2);

# List of root lengths (i.e. inner product with itself, no square root) which occur in GH4 (and hence in GH3). The test functions in H3-test.g verify that this is a list with two elements whose second element is gold^2 times the first element.
rootLengthsInGH4 := Set(List(GH4Roots, alpha -> bilForm(alpha, alpha)));

# alpha: Root in GH_4
# Output: True if alpha is short (in GH4) and false otherwise
GH4RootIsShort := function(alpha)
	return (bilForm(alpha, alpha) = rootLengthsInGH4[1]);
end;

# H3 and H4 consists of all short roots in GH3 and GH4, respectively
H3Roots := Filtered(GH3Roots, GH4RootIsShort);
H3Pos := Filtered(GH3Pos, GH4RootIsShort);
H4Roots := Filtered(GH4Roots, GH4RootIsShort);
H4Pos := Filtered(GH4Pos, GH4RootIsShort);

# beta: Root in GH4.
# Output: The unique root alpha in E8 with projW2(alpha) = beta.
projW2Inv := function(beta)
	local alpha;
	for alpha in E8Roots do
		if projW2(alpha) = beta then
			return alpha;
		fi;
	od;
	return fail;
end;

# alpha: Root in GH4.
# Output: alpha if alpha is short, otherwise (1/gold)*alpha. By the verification testGHIsGoldenH, scaleMap(alpha) is the unique shortest root in GH4 in the same ray as alpha.
# In [BW], we scale to the unit sphere, but this makes no difference for our arguments.
scaleMap := function(alpha)
	if GH4RootIsShort(alpha) then
		return alpha;
	else
		return (1/gold)*alpha;
	fi;
end;

# alpha: Root in H4.
# Output: A list [ beta, gamma ] of the unique roots in E8 such that projW2(beta) = alpha and projW2(gamma) = gold*alpha.
FoldingPreimage := function(alpha)
	return [ projW2Inv(alpha), projW2Inv(gold*alpha) ];
end;

# Root bases of H3 and H4
H4Sim := [ scaleMap(projW2(E8Sim[7])), scaleMap(projW2(E8Sim[1])), scaleMap(projW2(E8Sim[2])), scaleMap(projW2(E8Sim[3])) ];
H4SimBas := Basis(W2, H4Sim);
H3Sim := H4Sim{[2..4]};
H3Vec := Subspace(W2, H3Sim);
H3SimBas := Basis(H3Vec, H3Sim);

# Coefficients of the roots in H3 with respect to H3Sim
H4Coeffs := List(H4Roots, alpha -> Coefficients(H4SimBas, alpha));
H4PosCoeffs := List(H4Pos, alpha -> Coefficients(H4SimBas, alpha));
H3Coeffs := List(H3Roots, alpha -> Coefficients(H3SimBas, alpha));
H3PosCoeffs := List(H3Pos, alpha -> Coefficients(H3SimBas, alpha));

# ---- Auxiliary functions ----

# rootSystem: A root system (whose elements lie in some vector space).
# rootList: A subset of rootSystem.
# Output: The root subsystem generated by rootList.
generatedSubsystem := function(rootSystem, rootList)
	local vecspace, subspace;
	vecspace := VectorSpace(K, rootSystem);
	subspace := Subspace(vecspace, rootList);
	return Intersection(rootSystem, subspace);
end;

# alpha, beta: Roots in H4.
# Output: true if (alpha, beta) is an H2-pair, otherwise false.
IsH2Pair := function(alpha, beta)
	return (bilForm(alpha, beta) / bilForm(alpha, alpha) = -gold/2);
end;

# alpha, epsilon: An H2-pair in H4.
# Output: The corresponding H2-quintuple.
H2QuintupleFromPair := function(alpha, epsilon)
	if not IsH2Pair(alpha, epsilon) then
		return fail;
	else
		return [ alpha, gold*alpha+epsilon, gold*(alpha+epsilon), alpha+gold*epsilon, epsilon ];
	fi;
end;

# startRoot: A root in H4.
# onlyH3: Bool.
# Output: If onlyH3 = false, a list of all H2-quintuples in H4 starting from startRoot. If onlyH3 = true, only the (four) H2-quintuples in H3 are considered, and it returns fail if startRoot is not in H3.
H2QuintuplesStartingFromRoot := function(startRoot, onlyH3)
	local H2PairRoots;
	if onlyH3 and not startRoot in H3Roots then
		return false;
	fi;
	if onlyH3 then
		H2PairRoots := Filtered(H3Roots, alpha -> IsH2Pair(startRoot, alpha));
	else
		H2PairRoots := Filtered(H4Roots, alpha -> IsH2Pair(startRoot, alpha));
	fi;
	return List(H2PairRoots, alpha -> H2QuintupleFromPair(startRoot, alpha));
end;

# ---- Tests ----

# Returns true if the decomposition E8Vec = W1 + W2 is orthogonal, otherwise false. Claimed in [BW, 4.5].
testDecompIsOrtho := function()
	local i, j;
	for i in [1..Length(W1BasList)] do
		for j in [1..Length(W2BasList)] do
			if W1BasList[i] * W2BasList[j] <> Zero(K) then
				return false;
			fi;
		od;
	od;
	return true;
end;

# Returns true if the decomposition E8Vec = W1 + W2 is R-invariant, otherwise false. Here R denotes the set of simple reflections in Weyl(H4). Claimed in [BW, 4.5].
testDecompIsInvar := function()
	local R, r, v;
	R := [ x -> refl(E8Sim[1], refl(E8Sim[6], x)),
			x -> refl(E8Sim[3], refl(E8Sim[5], x)),
			x -> refl(E8Sim[2], refl(E8Sim[4], x)),
			x -> refl(E8Sim[7], refl(E8Sim[8], x)) ];
	for r in R do
		for v in W1BasList do
			if not r(v) in W1 then
				Display(v);
				return false;
			fi;
		od;
		for v in W2BasList do
			if not r(v) in W2 then
				return false;
			fi;
		od;
	od;
	return true;
end;

# Returns true if GH3 and GH4 are the disjoint unions of H3, gold*H3 and H4, gold*H4, respectively. Otherwise returns false. Claimed in [BW, 4.5].
testGHIsGoldenH := function()
	if Length(H3Roots) <> 30 or Length(GH3Roots) <> 60 or Length(H4Roots) <> 120 or Length(GH4Roots) <> 240 then
		return false;
	elif rootLengthsInGH4 <> [rootLengthsInGH4[1], gold^2 * rootLengthsInGH4[1]] then
		return false;
	else
		return (Set(GH3Roots) = Set(Concatenation(H3Roots, gold*H3Roots))) and (Set(GH4Roots) = Set(Concatenation(H4Roots, gold*H4Roots)));
	fi;
end;

# Returns true if H_3 and H_4 are invariant under all reflections sigma_alpha for alpha in H_3 and alpha in H_4, respectively, I.e. if H_3 and H_4 are indeed root systems. Claimed in [BW, 4.5].
testHIsRootSystem := function()
	local alpha, beta;
	for alpha in H3Roots do
		for beta in H3Roots do
			if not refl(alpha, beta) in H3Roots then
				return false;
			fi;
		od;
	od;
	for alpha in H4Roots do
		for beta in H4Roots do
			if not refl(alpha, beta) in H4Roots then
				return false;
			fi;
		od;
	od;
	return true;
end;

# Returns true if the assertion of [BW, 4.13] is true, i.e. \sigma_{E8Sim[i]} \sigma_{E8Sim[j]}, \sigma(projW2(E(Sim[i])) and \sigma(projW2(E8Sim[j])) act identically on GH3 for all (i,j) in { (1,6), (3,5), (2,4), (7, 8) }.
testReflActionLem := function()
	local pair, i, j, r, r1, r2, alpha;
	for pair in [ [1,6], [3,5], [2,4], [7,8] ] do
		i := pair[1];
		j := pair[2];
		r := x -> refl(E8Sim[j], refl(E8Sim[i], x));
		r1 := x -> refl(projW2(E8Sim[i]), x);
		r2 := x -> refl(projW2(E8Sim[j]), x);
		for alpha in E8Roots do
			if r(projW2(alpha)) <> r1(projW2(alpha)) or r(projW2(alpha)) <> r2(projW2(alpha)) then
				return false;
			fi;
		od;
	od;
	return true;
end;

# r: Element of K = CF(5).
# Replaces gold, gold^2, 2*gold by "t", "t^2" and "2t", respectively.
makeGoldReadable := function(r)
	if r = gold then
		return "t";
	elif r = gold^2 then
		return "t^2";
	elif r = 2*gold then
		return "2t";
	else
		return r;
	fi;
end;

# Returns true if the assertion of [BW, 2.12] is true, i.e. each root in H3 is contained in precisely 2 subsystems of type A1 x A2, 2 subsystems of type A2 and 2 subsystems of type H2. (By the transitivity of the Weyl group on H3, it suffices to check this for one root.)
testH3SubsysProp := function()
	local baseroot, subsystems, alpha, numA1A1, numA2, numH2;
	baseroot := H3Sim[1]; # Root for which the property is checked
	# Compute all subsystems of H3 generated by baseroot and another root
	subsystems := [];
	for alpha in H3Roots do
		AddSet(subsystems, generatedSubsystem(H3Roots, [ baseroot, alpha ]));
	od;
	# Subsystems of type A1 x A1, A2 or H2 are characterised by the fact that they have precisely 4, 6 or 10 elements, respectively.
	numA1A1 := Size(Filtered(subsystems, x -> (Size(x) = 4)));
	numA2 := Size(Filtered(subsystems, x -> (Size(x) = 6)));
	numH2 := Size(Filtered(subsystems, x -> (Size(x) = 10)));
	return (numA1A1 = 2 and numA2 = 2 and numH2 = 2);
end;

# Returns true if the assertion of [BW, 5.16] is true, otherwise false. (By the transitivity of the Weyl group, it suffices to check this for one choice of alpha.)
testTwoA2Prop := function()
	local alpha, H2Quints, H2Quint1, H2Quint2, H2Sub1, H2Sub2, bRhoFound, rho;
	alpha := H3Sim[2];
	H2Quints := H2QuintuplesStartingFromRoot(alpha, true);
	for H2Quint1 in H2Quints do
		for H2Quint2 in H2Quints do
			H2Sub1 := generatedSubsystem(H3Roots, H2Quint1);
			H2Sub2 := generatedSubsystem(H3Roots, H2Quint2);
			if not IsEqualSet(H2Sub1, H2Sub2) then
				# If the assertion of the lemma is incorrect for this choice of H2-quintuples, return false.
				bRhoFound := false; # Whether rho as in the lemma was found
				for rho in [ H2Quint2[3], H2Quint2[4] ] do
					if Size(generatedSubsystem(H3Roots, [ rho, H2Quint1[2] ])) = 6 and Size(generatedSubsystem(H3Roots, [ rho, H2Quint1[3] ])) = 6 then
						bRhoFound := true;
						break;
					fi;
				od;
				# No suitable rho was found -> return false
				if not bRhoFound then
					return false;
				fi;
			fi;
		od;
	od;
	# Return true if the assertion is satisfied for all choices of H2Quint1 and H2Quint2
	return true;
end;