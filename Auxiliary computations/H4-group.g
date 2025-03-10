#### Construction of the Chevalley group of type E8 and of its folding, which has an H4-grading

# ---- E8-root homomorphisms ----

# The Chevalley group is defined with respect to some module V over E8Lie.
# The particular choice of V is irrelevant, but we chooose it so that its
# dimension is minimal.
# In the following (comments), we will denote by R the polynomial ring over
# the integers. Any function which accepts elements of R also accepts integers.
V := E8Lie;
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

# r: Element of R.
# mat: A square matrix.
# Output: id + r*mat + r^2*mat^2/2 + r^3*mat^3/3! + ...
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

# E8RootHomNumber: An integer in [1..Length(E8Roots)]
# r: An element of R.
# Output: x_root(r) where x_root is the root homomorphism in the Chevalley group and root = E8Roots[i].
# See [BW, 4.23, 4.26].
E8RootHomOnNumber := function(E8RootNumber, r)
	local E8TwistSet;
	# List of roots in E8 which have to be twisted, given by their coefficient vector
	E8TwistSet := [[ 0, 0, 0, 1, 1, 1, 0, 0 ], [ 0, 1, 1, 1, 1, 1, 0, 0 ], [ 0, 0, 1, 2, 1, 1, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0 ], [ 1, 1, 1, 1, 1, 1, 0, 0 ], [ 0, 0, 1, 1, 1, 1, 0, 0 ], [ 1, 1, 1, 2, 1, 1, 0, 0 ], [ 0, 1, 1, 2, 1, 1, 0, 0 ], [ 0, 1, 2, 2, 1, 1, 0, 0 ], [ 1, 1, 2, 2, 1, 1, 0, 0 ], [ 1, 2, 2, 2, 1, 1, 0, 0 ]];
	E8TwistSet := Concatenation(E8TwistSet, -E8TwistSet);
	if E8CoeffFromRoot(E8RootFromNumber(E8RootNumber)) in E8TwistSet then
		r := -r;
	fi;
	return matrixExp(r, repMatrix(E8Lie.(E8RootNumber)));
end;

E8RootHomOnRoot := function(E8Root, r)
	return E8RootHomOnNumber(E8NumberFromRoot(E8Root), r);
end;

# ---- H4-root homomorphisms and Weyl elements ----

# H4Root: Root in H4.
# s: Element of R x R.
# Output: The image of s under the root homomorphism for H4Root in the H4-graded group obtained by folding.
# See [BW, 4.21, 4.26].
H4RootHom := function(H4Root, s)
	local preimage, E8RootShort, E8RootLong, leftTwist, rightTwist, leftTwistList, rightTwistList, f;
	preimage := FoldingPreimage(H4Root);
	E8RootShort := preimage[1]; # projW2 of this root is short in GH3
	E8RootLong := preimage[2];
	return E8RootHomOnRoot(E8RootShort, s[1]) * E8RootHomOnRoot(E8RootLong, s[2]);
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


# ---- Computation of the parity map for H4 ----

# Compute the standard Weyl elements for the root base only once, and not every time H4ParitySimRoot is called
weylBase :=  [ H4StandardWeyl(H4Sim[1]), H4StandardWeyl(H4Sim[2]), H4StandardWeyl(H4Sim[3]), H4StandardWeyl(H4Sim[4])];
weylBaseInv := List(weylBase, x -> x^-1);

# alpha: Root in H4.
# i: Index of a simple root in H4
# indets: Bool. If indets = true, then indeterminates are used in the computation, so that we have a solid proof that the equality below holds for all r, s in R. If indets = false, then 1 is used in place of indeterminates. This produces the same results and is much faster, but does not provide a solid proof.
# Output: A tuple (a, b) in { +-1 }^2 s.t. H4RootHom(alpha, [ r, s ])^{H4StandardWeyl(delta_i)} = H4RootHom(refl(delta_i, alpha), [ ar, bs ]) for all r, s in R.
# Note: In the test functions, we compute all values of the parity map with indets = true. The fact that this computation never produces "fail" shows that the function call with indets = false produces the same results.
# See [BW, 4.27].
H4ParitySimRoot := function(alpha, i, indets)
	local w, wInv, x1, x2, gamma, conj;
	w := weylBase[i];
	wInv := weylBaseInv[i];
	if indets = true then
		x1 := Indeterminate(Integers, 1);
		x2 := Indeterminate(Integers, 2);
	else
		x1 := 1;
		x2 := 1;
	fi;
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

# alpha: Root in H4.
# deltaList: List of indices in [1..4]
# Output: The parity of w_{H4Sim[deltaList[1]]} ... w_{H4Sim[deltaList[k]]} on alpha.
H4ParityProd := function(alpha, deltaList)
	local result, basRoot, i, par;
	result := [ 1, 1 ];
	basRoot := alpha;
	for i in deltaList do
		par := H4ParitySimRoot(basRoot, i, false);
		result[1] := result[1] * par[1];
		result[2] := result[2] * par[2];
		basRoot := refl(H4Sim[i], basRoot);
	od;
	return result;
end;