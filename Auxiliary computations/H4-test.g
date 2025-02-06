###### Tests

# ---- Root-system-theoretic tests ----

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

# Tests that D6RootInStandForm works as intended
testD6RootInStandForm := function()
    local e, i;
    e := [];
    e[1] := [1, 0, 0, 0, 0, 0];
    e[2] := [0, 1, 0, 0, 0, 0];
    e[3] := [0, 0, 1, 0, 0, 0];
    e[4] := [0, 0, 0, 1, 0, 0];
    e[5] := [0, 0, 0, 0, 1, 0];
    e[6] := [0, 0, 0, 0, 0, 1];
    for i in [1..5] do
        if D6RootInStandForm(D6Sim[i]) <> e[i] - e[i+1] then
            return false;
        fi;
    od;
    if D6RootInStandForm(D6Sim[6]) <> e[5] + e[6] then
        return false;
    fi;
    return true;
end;

# Returns a list with one entry for each positive root alpha in H4. Each entry is a list [ coeff, b1, b2 ] where coeff is the coefficient list of alpha with respect to H4Sim, b1 is the unique root in E8 with projW2(b1) = alpha and b2 is the unique root in E8 with projW2(b2) = gold*alpha. I.e. the output is precisely [BW, Figure 2].
H4PosFoldingTable := function()
	local coeff, alpha, preimage, resultList;
	resultList := [];
	for alpha in H4Pos do
		coeff := List(H4CoeffFromRoot(alpha), makeGoldReadable);
        preimage := FoldingPreimage(alpha);
		Add(resultList, [ coeff, preimage[1], preimage[2] ]);
	od;
	return resultList;
end;

## ---- Tests in the root graded group ----

# Returns true if the twisting involution in the H3-graded group acts on parameters as (x, y) -> (-x, y), and false otherwise. In other words, verifies the assertion of ...
testH3TwistInvo := function()
	local x, y, alpha, quint, ep, w;
	x := Indeterminate(Integers, 1);
	y := Indeterminate(Integers, 2);
	for alpha in H3Roots do
		quint := H2QuintuplesStartingFromRoot(alpha, true)[1];
		ep := quint[5];
		w := H3WeylEl(ep, [1,1])^2;
		if H3RootHom(alpha, [x,y])^w <> H3RootHom(alpha, [-x, y]) then
			return false;
		fi;
	od;
	return true;
end;

# Returns true if the twisting involution in the H4-graded group acts on parameters as (x, y) -> (-x, y), and false otherwise. In other words, verifies the assertion of ...
testH4TwistInvo := function()
	local x, y, alpha, quint, ep, w, count;
	x := Indeterminate(Integers, 1);
	y := Indeterminate(Integers, 2);
	count := 1;
	for alpha in H4Roots do
		Display(count);
		count := count+1;
		quint := H2QuintuplesStartingFromRoot(alpha, false)[1];
		ep := quint[5];
		w := H4WeylEl(ep, [1,1])^2;
		if w^-1 * H4RootHom(alpha, [x,y]) * w <> H4RootHom(alpha, [-x, y]) then
			return false;
		fi;
	od;
	return true;
end;

## ---- Tests of the commutator relations ----

# Returns true if the commutator relations in [BW, 4.12, Figure 5] hold for the H4-graded group.
testH4ComRels := function()
	local a, b, c, d, quint, comm, testComRel;
	a := Indeterminate(Integers, 1);
	b := Indeterminate(Integers, 2);
	c := Indeterminate(Integers, 3);
	d := Indeterminate(Integers, 4);
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
			Print(H4CoeffFromRoot(root1), ", ", H4CoeffFromRoot(root2), "\n");
			return false;
		else
			return true;
		fi;
	end;
	return
		## Commutator relation in the A_2-subsystem spanned by H4Sim[1], H4Sim[2]
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

# Returns true if the commutator relations in [BW, 4.12, Figure 5] hold for the H3-graded group constructed in H3-group.g. In other words, this H3-graded group satisfies the same commutator relations as the H3-graded subgroup of our H4-graded group.
testH3ComRels := function()
	local a, b, c, d, quint, comm, testComRel;
	a := Indeterminate(Integers, 1);
	b := Indeterminate(Integers, 2);
	c := Indeterminate(Integers, 3);
	d := Indeterminate(Integers, 4);
	quint := H2QuintupleFromPair(H3Sim[2], H3Sim[3]);
	# Returns the commutator of two generic elements of the corresponding root groups
	comm := function(root1, root2)
		return H3RootHom(root1, [ -a, -b]) * H3RootHom(root2, [ -c, -d ]) * H3RootHom(root1, [ a, b ]) * H3RootHom(root2, [ c, d ]);
	end;
	testComRel := function(root1, root2, test)
		if test <> comm(root1, root2) then
			return false;
		else
			return true;
		fi;
	end;
	return
	## Commutator relation in the A_2-subsystem
		testComRel(H3Sim[1], H3Sim[2], H3RootHom(H3Sim[1]+H3Sim[2], [ a*c, b*d ])) and
	## Commutator relations in the H_2-subsystem
	# Roots with one root between them
		testComRel(quint[1], quint[3], H3RootHom(quint[2], [ 0, a*c ])) and
		testComRel(quint[2], quint[4], H3RootHom(quint[3], [ 0, -a*c ])) and
		testComRel(quint[3], quint[5], H3RootHom(quint[4], [ 0, a*c ])) and
	# Roots with two roots between them
		testComRel(quint[1], quint[4], H3RootHom(quint[2], [ 0, -b*c ]) * H3RootHom(quint[3], [ 0, a*d ])) and
		testComRel(quint[2], quint[5], H3RootHom(quint[3], [ 0, b*c ]) * H3RootHom(quint[4], [ 0, -a*d ])) and
	# Roots with three roots between them
		testComRel(quint[1], quint[5], H3RootHom(quint[2], [ b*c, a*b*d ]) * H3RootHom(quint[3], [ -b*d, a*b*c*d ]) * H3RootHom(quint[4], [ a*d, -b*c*d ]));
end;

## ---- Tests concerning the parity map ----
## ---- Computation of the parity map ----



# Returns a list with one entry for each positive root alpha in H4. Each entry is a list [ coeff, e4, e1, e2, e3 ] where coeff is the coefficient list of alpha with respect to H4Sim and ei is the parity of the Weyl element of H4Sim[i] on alpha. I.e. the output is precisely [BW, Figure 5] and the function verifies [BW, 6.16].
H4ParityTable := function()
	local resultList, i, j, coeff, entry, par, H4PosCoeffs;
	# Make sure that the "global variables" for the Weyl elements are set correctly
	weylBase :=  [ H4StandardWeyl(H4Sim[1]), H4StandardWeyl(H4Sim[2]), H4StandardWeyl(H4Sim[3]), H4StandardWeyl(H4Sim[4])];
	weylBaseInv := List(weylBase, x -> x^-1);
	# Computation of the table
	H4PosCoeffs := List(H4Pos, H4CoeffFromRootReadable);
	resultList := [];
	for i in [1..Length(H4Pos)] do
		coeff := List(H4PosCoeffs[i], makeGoldReadable);
		entry := [ coeff ];
		for j in [1..4] do
			par := H4ParitySimRoot(H4Pos[i], j, true);
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
	local resultList, i, j, coeff, entry, H3PosCoeffs;
	# Make sure that the "global variables" for the Weyl elements are set correctly
	weylBase :=  [ H4StandardWeyl(H4Sim[1]), H4StandardWeyl(H4Sim[2]), H4StandardWeyl(H4Sim[3]), H4StandardWeyl(H4Sim[4])];
	weylBaseInv := List(weylBase, x -> x^-1);
	# Computation of the table
	H3PosCoeffs := List(H3Pos, H4CoeffFromRootReadable);
	resultList := [];
	for i in [1..Length(H3Pos)] do
		coeff := List(H3PosCoeffs[i], makeGoldReadable);
		entry := [ coeff ];
		for j in [2..4] do
			Add(entry, H4ParitySimRoot(H3Pos[i], j, false));
		od;
		Add(resultList, entry);
	od;
	return resultList;
end;

# Prints a table (of parity values) in a nice format
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

# Returns true if H4ParitySimRoot(alpha, i) = H4ParitySimRoot(-alpha, i) for all alpha in H4 and i in [1..4]. Claimed in [BW, 6.16].
testH4ParityOpposite := function()
	local alpha, i;
	for alpha in H4Pos do
		for i in [1..4] do
			if H4ParitySimRoot(alpha, i, true) <> H4ParitySimRoot(-alpha, i, true) then
				return false;
			fi;
		od;
	od;
	return true;
end;

# Returns true if the parity table of the H3-graded group from H3-group.g coincides with the one of the H3-graded subgroup of the H4-graded group.
testH3InH4Parity := function()
    local alpha, i;
    for alpha in H3Roots do
        for i in [2..4] do
             if H3Parity(alpha, H4Sim[i]) <> H4ParitySimRoot(alpha, i, false) then
                return false;
            fi;
        od;
    od;
    return true;
end;