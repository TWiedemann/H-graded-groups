# ---- Construction of the Chevalley group of type E8 ---

# The Chevalley group is defined with respect to some module V over E8Lie.
# The particular choice of V is irrelevant, but we chooose it so that its
# dimension is minimal.
V := HighestWeightModule(E8Lie, [0, 0, 0, 0, 0, 0, 0, 1]);
VBasis := Basis(V);
dimV := Dimension(V);
oneR := One(PolynomialRing(Integers, 1));

# x: Element of E8Lie
# Returns the matrix of x with respect to VBasis (as a left action on column vectors)
repMatrix := function(x)
	local result, i;
	result := [];
	for i in [1..dimV] do
		Add(result, Coefficients(VBasis, x^VBasis[i]));
	od;
	return TransposedMat(result);
end;

# Returns id + mat + mat^2/2 + mat^3/3! + ...
matrixExp := function(mat)
	local result, A, n;
	result := mat^0;
	A := mat;
	n := 1;
	while not IsZero(A) do
		result := result + A;
		n := n+1;
		A := A*mat/n;
	od;
	return result;
end;

# root: A root of E8 in the numbering format
# r: An element of F.
# Output: x_root(r) where x_root is the root homomorphism in the Chevalley group
E8RootHomOnNumber := function(E8RootNumber, r)
	return matrixExp(r*repMatrix(E8Lie.(E8RootNumber)));
end;

E8RootHomOnRoot := function(E8Root, r)
	return E8RootHomOnNumber(E8NumberFromRoot(E8Root), r);
end;

# H4Root: Root in H4.
# s: Element of R x R.
# Output: The image of s under the root homomorphism for H4Root in the H4-graded group obtained by folding.
H4RootHom := function(H4Root, s)
	local preimage, E8RootShort, E8RootLong;
	preimage := FoldingPreimage(H4Root);
	E8RootShort := preimage[1]; # projW2 of this root is short in GH3
	E8RootLong := preimage[2];
	# if H4Root in [ H3Sim[1], -H3Sim[1] ] then
		# "Twist" the root homomorphism for H3Sim[1] and -H3Sim[1]
		# return E8RootHom(E8RootShort, s[1]) * E8RootHom(E8RootLong, -s[2]);
	# else
		return E8RootHomOnRoot(E8RootShort, s[1]) * E8RootHomOnRoot(E8RootLong, s[2]);
	# fi;
end;

# H4Root: Root in H4.
# s: Invertible element of R x R.
# Output: The corresponding H4Root-Weyl element in the H4-grading.
H4WeylEl := function(H4Root, s)
	local sInv;
	sInv := [ s[1]^-1, s[2]^-1 ];
	return H4RootHom(-H4Root, -sInv) * H4RootHom(H4Root, s) * H4RootHom(-H4Root, -sInv);
end;

H4StandardWeyl := function(H4Root)
	return H4WeylEl(H4Root, [ oneR, oneR ]);
end;

## --- Computation of the parity map for H4 ---

# alpha, delta: Roots in H4.
# Output: A tuple (a, b) in { +-1 }^2 s.t. H4RootHom(alpha, [ r, s ])^{H4StandardWeyl(delta)} = H4RootHom(refl(delta, alpha), [ ar, bs ]) for all r, s in R.
H4Parity := function(alpha, delta)
	local w, x1, x2, gamma, conj;
	w := H4StandardWeyl(delta);
	x1 := Indeterminate(Integers, 1);
	x2 := Indeterminate(Integers, 2);
	gamma := refl(delta, alpha);
	conj := w^-1 * H4RootHom(alpha, [x1, x2]) * w;
	if conj = H4RootHom(gamma, [-x1, -x2]) then
		return [ -1, -1 ];
	elif conj = H4RootHom(gamma, [x1, x2]) then
		return [ 1, 1 ];
	elif conj = H4RootHom(gamma, [-x1, x2]) then
		return [ -1, 1 ];
	elif conj = H4RootHom(gamma, [x1, -x2]) then
		return [ 1, -1];
	else
		return fail;
	fi;
end;

# alpha: Root in H4.
# deltaList: List of roots in H4.
# Output: The parity of w_{deltaList[1]} ... w_{deltaList[k]} on alpha.
H4ParityProd := function(alpha, deltaList)
	local result, basRoot, delta, par;
	result := [ 1, 1 ];
	basRoot := alpha;
	for delta in deltaList do
		par := H4Parity(basRoot, delta);
		result[1] := result[1] * par[1];
		result[2] := result[2] * par[2];
		basRoot := refl(delta, basRoot);
	od;
	return result;
end;

## ---- Computation of the parity map ----

# Returns a list with one entry for each positive root alpha in H4. Each entry is a list [ coeff, b1, b2 ] where coeff is the coefficient list of alpha with respect to H4Sim, b1 is the unique root in E8 with projW2(b1) = alpha and b2 is the unique root in E8 with projW2(b2) = gold*alpha. I.e. the output is precisely [BW, Figure 2].
H4PosFoldingTable := function()
	local coeff, resultList, GH4ShortRoot, GH4LongRoot;
	resultList := [];
	for coeff in H4PosCoeffs do
		GH4ShortRoot := coeff * H4Sim; # alpha
		GH4LongRoot := gold * GH4ShortRoot; # gold*alpha
		coeff := List(coeff, makeGoldReadable);
		Add(resultList, [ coeff, projW2Inv(GH4ShortRoot), projW2Inv(GH4LongRoot) ]);
	od;
	return resultList;
end;

# Returns a list with one entry for each positive root alpha in H3. Each entry is a list [ coeff, e1, e2, e3 ] where coeff is the coefficient list of alpha with respect to H4Sim and ei is the parity of the Weyl element of H4Sim[i] on alpha. I.e. the output is precisely [BW, Figure 5] and the function verifies [BW, 6.16].
H4ParityTable := function()
	local resultList, i, j, coeff, entry;
	resultList := [];
	for i in [1..Length(H3Pos)] do
		coeff := List(H4PosCoeffs[i], makeGoldReadable);
		entry := [ coeff ];
		for j in [1..3] do
			Add(entry, H4Parity(H4Pos[i], H4Sim[j]));
		od;
		Add(resultList, entry);
	od;
	return resultList;
end;