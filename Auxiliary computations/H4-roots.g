#### Realisation of the root system H4 as a folding of E8 (and of the subsystem H3 as a folding of the subsystem D6)

# ---- Golden ratio ----
K := CF(5); # Ground field: Rationals adjoined fifth root of unity
gold := (1 + Sqrt(5))/2; # Golden ratio, contained in K
# r: Element of K = CF(5).
# Replaces gold by "t".
makeGoldReadable := function(r)
	if r = gold then
		return "t";
	elif r = gold^2 then
		return "t^2";
	elif r = gold+2 then
		return "t+2";
	elif r = 2*gold+1 then
		return "2t+1";
	elif r = 2*gold+2 then
		return "2t+2";
	elif r = 3*gold+3 then
		return "3t+3";
	elif r = 2*gold then
		return "2t";
	elif r = 3*gold+1 then
		return "3t+1";
	elif r = 3*gold+2 then
		return "3t+2";
	elif r = 4*gold+2 then
		return "4t+2";
	else
		return r;
	fi;
end;

# ---- The root system E8 ----
E8Lie := SimpleLieAlgebra("E", 8, Rationals);
E8Vec := FullRowSpace(K, 8); # Euclidean space containing E8
E8 := RootSystem(E8Lie); # Root system as a GAP object
E8Pos := PositiveRoots(E8);
# The order of E8Roots is precisely the order of the roots used by GAP. Specifically, for any
# i in [1..Length(E8Roots)], E8Lie.(i) is the Chevalley basis vector of E8Roots[i].
E8Roots := Concatenation(E8Pos, -E8Pos); # List of roots
# The simple system in the "standard" order:
#     2
#     |
# 1-3-4-5-6-7-8
# i.e.
# 8-7-6-5
#      /
# 1-3-4-2
E8SimStandOrder := SimpleSystem(E8);
E8SimStandOrderBas := Basis(E8Vec, E8SimStandOrder);
# The simple system in the order we use (with the natural ordering of the D6-subsystem):
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

# ---- D6 as a subsystem of E8 ----
D6Sim := E8Sim{[1..6]};
D6Vec := Subspace(E8Vec, D6Sim);
D6Roots := Filtered(E8Roots, root -> root in D6Vec);
D6Pos := Filtered(E8Pos, root -> root in D6Vec);

# D6Root: A root in D6Roots.
# Output: The same root expressed as a linear combination of e_1, ..., e_6, so that D6 = { \pm e_i \pm e_j | i,j \in [1..6] }
D6RootInStandForm := function(D6Root)
	local e, eBas;
	e := [];
	e[5] := (1/2) * (D6Sim[5] + D6Sim[6]); # (1/2) * (e5-e6 + e5+e6)
	e[6] := e[5] - D6Sim[5]; # e5 - (e5-e6)
	e[4] := e[5] + D6Sim[4];
	e[3] := e[4] + D6Sim[3];
	e[2] := e[3] + D6Sim[2];
	e[1] := e[2] + D6Sim[1];
	eBas := Basis(D6Vec, e);
	return Coefficients(eBas, D6Root);
end;

# ---- Reflections in the root systems ----

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

# ---- Subspaces of E8Vec on which we project ----

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

# ---- Construction of GH3 and GH4 ----

GH3Roots := List(D6Roots, projW2);
GH3Pos := List(D6Pos, projW2);
GH4Roots := List(E8Roots, projW2);
GH4Pos := List(E8Pos, projW2);

# ---- Root lengths in GH4 and scaling ----

# List of root lengths (i.e. inner product with itself, no square root) which occur in GH4. The test functions in H4-test.g verify that this is a list with two elements whose second element is gold^2 times the first element.
rootLengthsInGH4 := Set(List(GH4Roots, alpha -> bilForm(alpha, alpha)));

# alpha: Root in GH4
# Output: True if alpha is short (in GH4) and false otherwise
GH4RootIsShort := function(alpha)
	return (bilForm(alpha, alpha) = rootLengthsInGH4[1]);
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

# ---- Construction of H3 and H4 ----

# H3 and H4 consist of all short roots in GH3 and GH4, respectively
H3Roots := Filtered(GH3Roots, GH4RootIsShort);
H3Pos := Filtered(GH3Pos, GH4RootIsShort);
H4Roots := Filtered(GH4Roots, GH4RootIsShort);
H4Pos := Filtered(GH4Pos, GH4RootIsShort);

# Root bases of H3 and H4
H4Sim := [ scaleMap(projW2(E8Sim[7])), scaleMap(projW2(E8Sim[1])), scaleMap(projW2(E8Sim[2])), scaleMap(projW2(E8Sim[3])) ];
H4SimBas := Basis(W2, H4Sim);
H3Sim := H4Sim{[2..4]};
H3Vec := Subspace(W2, H3Sim);
H3SimBas := Basis(H3Vec, H3Sim);

# ---- Preimage maps from (G)H4 to E8

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

# alpha: Root in H4.
# Output: A list [ beta, gamma ] of the unique roots in E8 such that projW2(beta) = alpha and projW2(gamma) = gold*alpha.
FoldingPreimage := function(alpha)
	return [ projW2Inv(alpha), projW2Inv(gold*alpha) ];
end;



# ---- Coefficients of roots in H3 and H4 ----

H4RootFromCoeff := function(a, b, c, d)
	local root;
	root := a*H4Sim[1] + b*H4Sim[2] + c*H4Sim[3] + d*H4Sim[4];
	if not root in H4Roots then
		return false;
	else
		return root;
	fi;
end;

H4CoeffFromRoot := function(H4Root)
	return Coefficients(H4SimBas, H4Root);
end;

H4CoeffFromRootReadable := function(H4Root)
	return List(H4CoeffFromRoot(H4Root), makeGoldReadable);
end;

H3CoeffFromRoot := function(H3Root)
	return Coefficients(H3SimBas, H3Root);
end;

H3CoeffFromRootReadable := function(H3Root)
	return List(H3CoeffFromRoot(H3Root), makeGoldReadable);
end;

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