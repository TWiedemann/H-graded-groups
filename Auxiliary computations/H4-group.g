# ---- Construction of the Chevalley group of type E8 ---

# The Chevalley group is defined with respect to some module V over E8Lie.
# The particular choice of V is irrelevant, but we chooose it so that its
# dimension is minimal.
V := E8Lie; # HighestWeightModule(E8Lie, [0, 0, 0, 0, 0, 0, 0, 1]);
VBasis := Basis(V);
dimV := Dimension(V);
oneR := One(PolynomialRing(Integers, 1));

# x: Element of E8Lie
# Returns the matrix of x with respect to VBasis (as a left action on column vectors)
repMatrix := function(x)
	local result, i;
	result := [];
	for i in [1..dimV] do
		Add(result, Coefficients(VBasis, x*VBasis[i]));
	od;
	return TransposedMat(result);
end;

# Returns id + r*mat + r^2*mat^2/2 + r^3*mat^3/3! + ...
matrixExp := function(r, mat)
	local result, A, n;
	result := mat^0;
	A := mat;
	n := 1;
	while not IsZero(A) do
		result := result + r^n * A;
		n := n+1;
		A := A*mat/n;
	od;
	return result;
end;

# root: A root of E8 in the numbering format
# r: An element of F.
# Output: x_root(r) where x_root is the root homomorphism in the Chevalley group
E8RootHomOnNumber := function(E8RootNumber, r)
	return matrixExp(r, repMatrix(E8Lie.(E8RootNumber)));
end;

E8RootHomOnRoot := function(E8Root, r)
	return E8RootHomOnNumber(E8NumberFromRoot(E8Root), r);
end;

# H4Root: Root in H4.
# s: Element of R x R.
# Output: The image of s under the root homomorphism for H4Root in the H4-graded group obtained by folding.
H4RootHom := function(H4Root, s)
	local preimage, E8RootShort, E8RootLong, leftTwist, rightTwist, leftTwistList, rightTwistList, f;
	preimage := FoldingPreimage(H4Root);
	E8RootShort := preimage[1]; # projW2 of this root is short in GH3
	E8RootLong := preimage[2];
	leftTwist := 1;
	rightTwist := 1;
	f := H4RootFromCoeff;
	leftTwistList := [f(0, gold, gold, 1), f(0, gold, gold^2, gold^2), f(0, gold, 2*gold, gold^2)];
	rightTwistList := [f(0, 1, 0, 0), f(0, gold, gold, gold), f(0, 1, 1, gold), f(0, gold, gold^2, gold), f(0, 1, gold^2, gold), f(0, 1, gold^2, gold^2), f(0, gold, gold^2, gold^2), f(0, gold, 2*gold, gold^2)];
	if H4Root in Concatenation(leftTwistList, -leftTwistList) then
		leftTwist := -1;
	fi;
	if H4Root in Concatenation(rightTwistList, -rightTwistList) then
		rightTwist := -1;
	fi;
	# if H4Root in [ H3Sim[1], -H3Sim[1] ] then
		# "Twist" the root homomorphism for H3Sim[1] and -H3Sim[1]
		# return E8RootHom(E8RootShort, s[1]) * E8RootHom(E8RootLong, -s[2]);
	# else
		return E8RootHomOnRoot(E8RootShort, leftTwist*s[1]) * E8RootHomOnRoot(E8RootLong, rightTwist*s[2]);
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
	return H4WeylEl(H4Root, [ 1, 1 ]);
end;

## ---- Tests of the commutator relations in the folding ----

eval := function(mat, indets, values)
	return List(mat, row -> List(row, x -> oneR*Value(x, indets, values)));
end;

# Returns true if the commutator relations in [BW, 4.12, Figure 5] hold.
testComRels := function()
	local a, b, c, d, quint, comm, testComRel;
	# a := Indeterminate(Integers, 1);
	# b := Indeterminate(Integers, 2);
	# c := Indeterminate(Integers, 3);
	# d := Indeterminate(Integers, 4);
	a := 2;
	b := 3;
	c := 5;
	d := 7;
	quint := H2QuintupleFromPair(H4Sim[3], H4Sim[4]);
	# Returns the commutator of two generic elements of the corresponding root groups
	comm := function(root1, root2)
		local x, y;
		x := H4RootHom(root1, [ a, b ]);
		y := H4RootHom(root2, [ c, d ]);
		return x^-1 * y^-1 * x * y;
	end;
	testComRel := function(root1, root2, test)
		if test <> comm(root1, root2) then
			return false;
		else
			return true;
		fi;
	end;
	return
		## Commutator relation in the A_2-subsystem spanned by H4Sim[2], H4Sim[3]
		testComRel(H4Sim[1], H4Sim[2], H4RootHom(H4Sim[1]+H4Sim[2], [ a*c, b*d ])) and
		## Commutator relation in the A_2-subsystem spanned by H4Sim[2], H4Sim[3]
		testComRel(H4Sim[2], H4Sim[3], H4RootHom(H4Sim[2]+H4Sim[3], [ a*c, b*d ])) and
		## Commutator relations in the H_2-subsystem
		# Roots with one root between them
		testComRel(quint[1], quint[3], H4RootHom(quint[2], [ 0, a*c ])) and
		testComRel(quint[2], quint[4], H4RootHom(quint[3], [ 0, -a*c ])) and
		testComRel(quint[3], quint[5], H4RootHom(quint[4], [ 0, a*c ])) and
		# Roots with two roots between them
		testComRel(quint[1], quint[4], H4RootHom(quint[2], [ 0, -b*c ]) * H4RootHom(quint[3], [ 0, a*d ])) and
		testComRel(quint[2], quint[5], H4RootHom(quint[3], [ 0, b*c ]) * H4RootHom(quint[4], [ 0, -a*d ])) and
		# Roots with three roots between them
		testComRel(quint[1], quint[5], H4RootHom(quint[2], [ b*c, a*b*d ]) * H4RootHom(quint[3], [ -b*d, a*b*c*d ]) * H4RootHom(quint[4], [ a*d, -b*c*d ]));
end;

## --- Computation of the parity map for H4 ---

weylBase :=  [ H4StandardWeyl(H4Sim[1]), H4StandardWeyl(H4Sim[2]), H4StandardWeyl(H4Sim[3]), H4StandardWeyl(H4Sim[4])];
weylBaseInv := List(weylBase, x -> x^-1);

# alpha: Root in H4.
# i: Index of a simple root in H4
# Output: A tuple (a, b) in { +-1 }^2 s.t. H4RootHom(alpha, [ r, s ])^{H4StandardWeyl(delta_i)} = H4RootHom(refl(delta_i, alpha), [ ar, bs ]) for all r, s in R.
H4ParitySimRoot := function(alpha, i)
	local w, wInv, x1, x2, gamma, conj;
	w := weylBase[i];
	wInv := weylBaseInv[i];
	x1 := Indeterminate(Integers, 1);
	x2 := Indeterminate(Integers, 2);
	gamma := refl(H4Sim[i], alpha);
	conj := wInv * H4RootHom(alpha, [x1, x2]) * w;
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

# This returns the same result as H4ParitySimRoot, but is much faster because it does not use indeterminates. However, H4ParitySimRoot is needed for a "solid" proof.
# alpha: Root in H4.
# i: Index of a simple root in H4
# Output: A tuple (a, b) in { +-1 }^2 s.t. H4RootHom(alpha, [ 1, 1 ])^{H4StandardWeyl(delta_i)} = H4RootHom(refl(delta_i, alpha), [ a, b ]).
H4ParitySimRootWithoutIndets := function(alpha, i)
	local w, wInv, x1, x2, gamma, conj;
	w := weylBase[i];
	wInv := weylBaseInv[i];
	x1 := 1;
	x2 := 1;
	gamma := refl(H4Sim[i], alpha);
	conj := wInv * H4RootHom(alpha, [x1, x2]) * w;
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

# Returns a list with one entry for each positive root alpha in H4. Each entry is a list [ coeff, e4, e1, e2, e3 ] where coeff is the coefficient list of alpha with respect to H4Sim and ei is the parity of the Weyl element of H4Sim[i] on alpha. I.e. the output is precisely [BW, Figure 5] and the function verifies [BW, 6.16].
H4ParityTable := function()
	local resultList, i, j, coeff, entry, par;
	resultList := [];
	for i in [1..Length(H4Pos)] do
		coeff := List(H4PosCoeffs[i], makeGoldReadable);
		entry := [ coeff ];
		for j in [1..4] do
			par := H4ParitySimRootWithoutIndets(H4Pos[i], j);
			Add(entry, par);
			if par = fail then
				return [coeff, j, fail];
			fi;
		od;
		Add(resultList, entry);
	od;
	return resultList;
end;

# Returns a list with one entry for each positive root alpha in H3. Each entry is a list [ coeff, e1, e2, e3 ] where coeff is the coefficient list of alpha with respect to H4Sim and ei is the parity of the Weyl element of H4Sim[i] on alpha. I.e. the output is precisely [BW, Figure 5] and the function verifies [BW, 6.16].
H3ParityTable := function()
	local resultList, i, j, coeff, entry;
	resultList := [];
	for i in [1..Length(H3Pos)] do
		coeff := List(H3PosCoeffs[i], makeGoldReadable);
		entry := [ coeff ];
		for j in [2..4] do
			Add(entry, H4ParitySimRootWithoutIndets(H3Pos[i], j));
		od;
		Add(resultList, entry);
	od;
	return resultList;
end;

# Returns true if H4Parity(alpha, delta) = H3Parity(-alpha, delta) for all alpha in H4 and delta in H4Sim. Claimed in [BW, 6.16].
testH4ParityOpposite := function()
	local alpha, i;
	for alpha in H4Pos do
		for i in [1..4] do
			if H4ParitySimRootWithoutIndets(alpha, i) <> H4ParitySimRootWithoutIndets(-alpha, i) then
				return false;
			fi;
		od;
	od;
	return true;
end;

printTable := function(table)
	local row, cell, i, j;
	for j in [1..Length(table)] do
		row := table[j];
		if j=6 or j=11 then
			Print("\n");
		fi;
		Print(j, "\t");
		for i in [2..Length(row)] do
			Print(row[i], "\t");
		od;
		Print("\t", row[1], "\n");
	od;
end;

H3Table := H3ParityTable();
printTable(H3Table);