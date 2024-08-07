## Verifies that the basis in D6ChevBasEl of H3-group.g is indeed a Chevalley basis, a fact for which we could not find an explicit reference.

K := Rationals;
n := 6;

# Initialise standard basis vectors
e := [];
for i in [1..n] do
	e[i] := [];
	for j in [1..n] do
		if i=j then
			e[i][j] := One(K);
		else
			e[i][j] := Zero(K);
		fi;
	od;
od;

# Initialise D_n
Dn := [];
for i in [1..n] do
	for j in [1..n] do
		if i <> j then
			Add(Dn, e[i] - e[j]);
			if i < j then
				Add(Dn, e[i] + e[j]);
				Add(Dn, -e[i] - e[j]);
			fi;
		fi;
	od;
od;

# Standard torus element for root alpha
hEl := function(alpha)
	local hBas, h;
	hBas := function(i)
		local result;
		result := NullMat(2*n, 2*n, K);
		result[i][i] := One(K);
		result[i+n][i+n] := -One(K);
		return result;
	end;
	h := List([1..n], i -> hBas(i)); # [ hBas(1), ..., hBas(n) ]
	return alpha * h;
end;

# Chevalley basis element
xEl := function(alpha)
	local result, posPositions, negPositions, i, j;
	result := NullMat(2*n, 2*n, K);
	# List of indices where alpha has value 1 or -1.
	posPositions := Positions(alpha, 1);
	negPositions := Positions(alpha, -1);
	if IsEmpty(negPositions) then
		# alpha is of the form e_i + e_j
		i := posPositions[1];
		j := posPositions[2];
		result[i][n+j] := One(K);
		result[j][n+i] := -One(K);
	elif IsEmpty(posPositions) then
		# alpha is of the form -e_i - e_j
		i := negPositions[1];
		j := negPositions[2];
		result[n+j][i] := One(K);
		result[n+i][j] := -One(K);
	else
		# alpha is of the form e_i - e_j
		i := posPositions[1];
		j := negPositions[1];
		result[i][j] := One(K);
		result[n+j][n+i] := -One(K);
	fi;
	return result;
end;

# Structure constant c_{alpha, beta} of the Chevalley basis
chevStr := function(alpha, beta)
	local comm;
	if alpha + beta in Dn then
		comm := LieBracket(xEl(alpha), xEl(beta));
		if comm = xEl(alpha+beta) then
			return 1;
		elif comm = -xEl(alpha+beta) then
			return -1;
		else
			return fail;
		fi;
	else
		return 0;
	fi;
end;

# Check whether c_{alpha, beta} = -c_{-alpha, -beta} for all alpha, beta
testChevStr := function()
	local alpha, beta;
	for alpha in Dn do
		for beta in Dn do
			if alpha <> -beta then
				if chevStr(alpha, beta) <> -chevStr(-alpha, -beta) then
					return false;
				fi;
			fi;
		od;
	od;
	return true;
end;