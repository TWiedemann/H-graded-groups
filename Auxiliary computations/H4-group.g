# ---- Construction of the Chevalley group of type E8 ---

# The Chevalley group is defined with respect to some module V over E8Lie.
# The particular choice of V is irrelevant, but we chooose it so that its
# dimension is minimal.
V := HighestWeightModule(E8Lie, [1, 0, 0, 0, 0, 0, 0, 0]);
VBasis := Basis(V);
dimV := Dimension(V);

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
E8RoothomOnNumber := function(E8RootNumber, r)
	return matrixExp(r*repMatrix(E8Lie.(E8RootNumber)));
end;

E8RoothomOnRoot := function(E8Root, r)
	return E8RoothomOnNumber(E8RootNumber(E8Root), r);
end;

# H4Root: Root in H4.
# s: Element of R x R.
# Output: The image of s under the root homomorphism for H4Root in the H4-graded group obtained by folding.
H4Roothom := function(H4Root, s)
	local preimage, D6RootShort, D6RootLong;
	preimage := FoldingPreimage(H4Root);
	E8RootShort := preimage[1]; # projW2 of this root is short in GH3
	E8RootLong := preimage[2];
	# if H4Root in [ H3Sim[1], -H3Sim[1] ] then
		# "Twist" the root homomorphism for H3Sim[1] and -H3Sim[1]
		# return E8RootHom(E8RootShort, s[1]) * E8RootHom(E8RootLong, -s[2]);
	# else
		return E8RootHom(E8RootShort, s[1]) * E8RootHom(E8RootLong, s[2]);
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