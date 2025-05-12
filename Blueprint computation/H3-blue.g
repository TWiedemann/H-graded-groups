### Blueprint computations for H_3 ###

# Directory where text files are created
mainDir := "Desktop/"; 

# ---- Definition of the tree data structure for terms ----

# A "term" is a record with 2 or 3 entries. The entry named "type" is a string that describes the type of the term. The remaining entries (which are called "sub" if there is only one or "subLeft" and "subRight" if there are two) store the information which describes the term. We document the types in the following format:
# "Type string" [number of additional list entries, either 1 or 2]: Description of the type. [Description of the additional list entries. If they are terms (which is the case most of the time), we do not add this description.] Description of the mathematical term which is represented by this list, where "term1" and "term2" represent the list entries 2 and 3, respectively.
# "Indet" [1]: An indeterminate. The second list entry is a string s. Represents the indeterminate with the name s.
# "Integer" [2]: An integer. The second list entry is an integer i. Represents the integer i.
# "RingMinus" [1]: A minus sign (in the ring). Represents -term1.
# "RingAdd" [2]: A sum of two terms (in the ring). Represents term1 + term2.
# "RingMult" [2]: A product of two terms (in the ring). Represents term1 * term2.
# "RingInv" [1]: The ring involution x -> x*. Represents (term1)*.
# "psi_aeb" [2]: The maps psi. Represents psi_{alpha,varepsilon}^beta(term1, term2), i.e. a=alpha, b=beta, c=gamma, d=delta and e=varepsilon.
# "com1" [2]: The commutator map f(x,y) = \psi_{a,c}(x,y).
# "com2" [2]: The commutator map g(x,y) = \psi_{a,d}^b(x,y).
# "com31" [2]: The commutator map h_1(x,y) = \psi_{a,e}^b(x,y).
# "com32" [2]: The commutator map h_2(x,y) = \psi_{a,e}^c(x,y).

## Initialise variables (to avoid GAP warnings)

IndetForString := fail;
IndetForInt := fail;
RingMinus := fail;
RingAdd := fail;
RingMult := fail;
RingInv := fail;
psi_ac := fail;
psi_bd := fail;
psi_ce := fail;
psi_adb := fail;
psi_adc := fail;
psi_bec := fail;
psi_bed := fail;
psi_aeb := fail;
psi_aec := fail;
psi_aed := fail;
com1 := fail;
com2 := fail;
com31 := fail;
com32 := fail;

ZeroTerm := rec( type := "Integer", sub := 0 );

# Defines constructors for all types of terms. All identities (i) with i <= idNum are used to simplify the constructors.
defineComMaps := function(idNum)
	IndetForString := function(string)
		return rec( type := "Indet", sub := string );
	end;

	IndetForInt := function(n)
		return rec( type := "Indet", sub := n );
	end;

	RingMinus := function(term)
		local type;
		type := term.type;
		if type = "RingMinus" then
			return term.sub; # -- = +
		else
			return rec( type := "RingMinus", sub := term );
		fi;
	end;

	RingAdd := function(term1, term2)
		return rec( type := "RingAdd", subLeft := term1, subRight := term2 );
	end;

	RingMult := function(term1, term2)
		return rec( type := "RingMult", subLeft := term1, subRight := term2 );
	end;

	RingInv := function(term)
		local type;
		type := term.type;
		if type = "RingMinus" and idNum >= 1 then
			return RingMinus(RingInv(term.sub)); # Prefer -x^* over (-x)^*
		elif type = "RingAdd" then
			return RingAdd(RingInv(term.subLeft), RingInv(term.subRight)); # Prefer x^* + y^* over (x+y)^*
		elif type = "RingInv" then
			return term.sub; # (x^*)^* = x
		elif idNum >= 2 and type = "RingMult" then
			return RingMult(term.subLeft, RingInv(term.subRight));
		elif (idNum >= 5 and type in [ "psi_ac", "psi_bd", "psi_ce" ]) or (idNum >= 21 and type in [ "com1", "com2" ]) then
			return term;
		else
			return rec( type := "RingInv", sub := term );
		fi;
	end;

	psi_ac := function(term1, term2)
		local type1, type2;
		type1 := term1.type;
		type2 := term2.type;
		if type1 = "RingMinus" or (idNum >= 21 and type1 = "RingInv") then
			# psi(-x, y) = -psi(x,y)
			return RingMinus(psi_ac(term1.sub, term2));
		elif type2 = "RingMinus" or (idNum >= 21 and type2 = "RingInv") then
			# psi(x, -y) = -psi(x,y)
			return RingMinus(psi_ac(term1, term2.sub));
		elif idNum >= 21 then
			if type1 in ["com1", "com2"] or type2 in ["com1", "com2"] then
				return ZeroTerm;
			elif type2 = "com32" then
				return RingMult(term2.subRight, com2(term2.subLeft, term1));
			elif type1 = "com32" then
				return com1(term2, term1); # com1 is symmetric
			else
				return rec( type := "com1", subLeft := term1, subRight := term2 );
			fi;
		else
			return rec( type := "psi_ac", subLeft := term1, subRight := term2 );
		fi;
	end;
	
	com1 := psi_ac;

	psi_bd := function(term1, term2)
		local type1, type2;
		type1 := term1.type;
		type2 := term2.type;
		if idNum >= 7 then
			return RingMinus(psi_ac(term1, term2)); 
		else
			return rec( type := "psi_bd", subLeft := term1, subRight := term2 );
		fi;
	end;

	psi_ce := function(term1, term2)
		local type1, type2;
		type1 := term1.type;
		type2 := term2.type;
		if idNum >= 7 then
			return psi_ac(term1, term2);
		else
			return rec( type := "psi_ce", subLeft := term1, subRight := term2 );
		fi;
	end;

	psi_adb := function(term1, term2)
		if term2.type = "RingMinus" or (idNum >= 21 and term2.type = "RingInv") then
			# psi(x, -y) = -psi(x,y)
			return RingMinus(psi_adb(term1, term2.sub));
		elif idNum >= 21 then
			if term1.type = "RingMinus" then
				return RingMinus(psi_adb(term1.sub, term2));
			elif term1.type = "RingInv" then
				return psi_adb(term1.sub, term2);
			elif term2.type in ["com1", "com2"] then
				return ZeroTerm;
			else
				return rec( type := "com2", subLeft := term1, subRight := term2 );
			fi;
		else
			return rec( type := "psi_adb", subLeft := term1, subRight := term2 );
		fi;
	end;
	
	com2 := psi_adb;

	psi_adc := function(term1, term2)
		if idNum >= 21 then
			return RingMinus(psi_adb(term2, term1));
		elif term1.type = "RingMinus" then
			# psi(-x, y) = -psi(x, y)
			return RingMinus(psi_adc(term1.sub, term2));
		else
			return rec( type := "psi_adc", subLeft := term1, subRight := term2 );
		fi;
	end;

	psi_bec := function(term1, term2)
		if idNum >= 21 then
			return RingMinus(psi_adb(term1, term2));
		elif term2.type = "RingMinus" then
			# psi(-x, y) = -psi(x, y)
			return RingMinus(psi_bec(term1, term2.sub));
		else
			return rec( type := "psi_bec", subLeft := term1, subRight := term2 );
		fi;
	end;

	psi_bed := function(term1, term2)
		if idNum >= 21 then
			return psi_adb(term2, term1);
		elif term1.type = "RingMinus" then
			# psi(-x, y) = -psi(x, y)
			return RingMinus(psi_bed(term1.sub, term2));
		else
			return rec( type := "psi_bed", subLeft := term1, subRight := term2 );
		fi;
	end;


	psi_aeb := function(term1, term2)
		if term2.type = "RingMinus" then
			return RingMinus(psi_aeb(term1, term2.sub));
		elif idNum >= 21 then
			return rec( type := "com31", subLeft := term1, subRight := term2 );
		else
			return rec( type := "psi_aeb", subLeft := term1, subRight := term2 );
		fi;
	end;
	
	com31 := psi_aeb;

	psi_aec := function(term1, term2)
		if idNum >= 21 then
			return rec( type := "com32", subLeft := term1, subRight := term2 );
		else
			return rec( type := "psi_aec", subLeft := term1, subRight := term2 );
		fi;
	end;
	
	com32 := psi_aec;

	psi_aed := function(term1, term2)
		if idNum >= 21 then
			return RingMinus(psi_aeb(RingMinus(term2), term1));
		else
			return rec( type := "psi_aed", subLeft := term1, subRight := term2 );
		fi;
	end;
end;

# ---- End of definition of tree data structure ----

# ---- Functions for handling terms ----

# Replaces the indeterminate with name indet by (the integer) 0, and returns the resulting term.
PlugInZero := function(term, indet)
	local type, func, newTerm, newTerm1, newTerm2;
	type := term.type;
	if type = "Indet" then
		if term.sub = indet then
			return ZeroTerm;
		else
			return StructuralCopy(term);
		fi;
	elif type = "Integer" then
		return StructuralCopy(term);
	elif type = "RingMinus" or type = "RingInv" then
		if type = "RingMinus" then
			func := RingMinus;
		elif type = "RingInv" then
			func := RingInv;
		fi;
		newTerm := PlugInZero(term.sub, indet);
		if newTerm = ZeroTerm then
			return ZeroTerm; # -0 = 0 or 0* = 0
		else
			return func(newTerm);
		fi;
	elif type = "RingAdd" then
		func := RingAdd;
		newTerm1 := PlugInZero(term.subLeft, indet);
		newTerm2 := PlugInZero(term.subRight, indet);
		if newTerm1 = ZeroTerm and newTerm2 = ZeroTerm then
			return ZeroTerm;
		elif newTerm1 <> ZeroTerm and newTerm2 <> ZeroTerm then
			return func(newTerm1, newTerm2);
		elif newTerm1 = ZeroTerm then
			return newTerm2;
		else
			return newTerm1;
		fi;
	elif type in ["RingMult", "psi_ac", "psi_bd", "psi_ce", "psi_adb", "psi_adc", "psi_bec", "psi_bed", "psi_aeb", "psi_aec", "psi_aed", "com1", "com2", "com31", "com32"] then
		if type = "RingMult" then
			func := RingMult;
		elif type = "psi_ac" then
			func := psi_ac;
		elif type = "psi_bd" then
			func := psi_bd;
		elif type = "psi_ce" then
			func := psi_ce;
		elif type = "psi_adb" then
			func := psi_adb;
		elif type = "psi_adc" then
			func := psi_adc;
		elif type = "psi_bec" then
			func := psi_bec;
		elif type = "psi_bed" then
			func := psi_bed;
		elif type = "psi_aeb" then
			func := psi_aeb;
		elif type = "psi_aec" then
			func := psi_aec;
		elif type = "psi_aed" then
			func := psi_aed;
		elif type = "com1" then
			func := com1;
		elif type = "com2" then
			func := com2;
		elif type = "com31" then
			func := com31;
		elif type = "com32" then
			func := com32;
		fi;
		newTerm1 := PlugInZero(term.subLeft, indet);
		newTerm2 := PlugInZero(term.subRight, indet);
		if newTerm1 = ZeroTerm or newTerm2 = ZeroTerm then
			return ZeroTerm;
		else
			return func(newTerm1, newTerm2);
		fi;
	fi;
end;

# Returns the input string in brackets
inBrackets := function(string)
	return Concatenation("(", string, ")");
end;

RingInvOnString := function(string)
	return Concatenation(string, "^*");
end;

# Returns a string representation of a term
TermAsString := function(term)
	local type, substring, string1, string2, substring1, substring2, funcstring, argument, subtype, subtype1, subtype2;
	type := term.type;
	if type = "Indet" or type = "Integer" then
		return String(term.sub);
	elif type = "RingMinus" then
		substring := TermAsString(term.sub);
		subtype := term.sub.type;
		if subtype = "RingAdd" then
			return Concatenation("-", inBrackets(substring));
		elif subtype = "RingMinus" then # -- = +
			return TermAsString(term.sub.sub);
		else
			return Concatenation("-", substring);
		fi;
	elif type = "RingAdd" then
		string1 := TermAsString(term.subLeft);
		string2 := TermAsString(term.subRight);
		subtype2 := term.subRight.type;
		if subtype2 = "RingMinus" or subtype2 = "RingAdd" then
			return Concatenation(string1, "+",  inBrackets(string2));
		else
			return Concatenation(string1, "+", string2);
		fi;
	elif type = "RingMult" then
		substring1 := TermAsString(term.subLeft);
		subtype1 := term.subLeft.type;
		substring2 := TermAsString(term.subRight);
		subtype2 := term.subRight.type;
		if subtype1 in ["RingAdd", "RingMult", "RingMinus"] then
			string1 := inBrackets(substring1);
		else
			string1 := substring1;
		fi;
		if subtype2 in ["RingAdd", "RingMult", "RingMinus"] then
			string2 := inBrackets(substring2);
		else
			string2 := substring2;
		fi;
		return Concatenation(string1, string2);
	elif type = "RingInv" then
		substring := TermAsString(term.sub);
		return RingInvOnString(inBrackets(substring));
	elif type in ["psi_ac", "psi_bd", "psi_ce", "psi_adb", "psi_adc", "psi_bec", "psi_bed", "psi_aeb", "psi_aec", "psi_aed", "com1", "com2", "com31", "com32"] then
		if type = "psi_ac" then
			funcstring := "\\psi_{\\alpha,\\gamma}";
		elif type = "psi_bd" then
			funcstring := "\\psi_{\\beta,\\delta}";
		elif type = "psi_ce" then
			funcstring := "\\psi_{\\gamma,\\epsilon}";
		elif type = "psi_adb" then
			funcstring := "\\psi_{\\alpha,\\delta}^\\beta";
		elif type = "psi_adc" then
			funcstring := "\\psi_{\\alpha,\\delta}^\\gamma";
		elif type = "psi_bec" then
			funcstring := "\\psi_{\\beta,\\epsilon}^\\gamma";
		elif type = "psi_bed" then
			funcstring := "\\psi_{\\beta,\\epsilon}^\\delta";
		elif type = "psi_aeb" then
			funcstring := "\\psi_{\\alpha,\\epsilon}^\\beta";
		elif type = "psi_aec" then
			funcstring := "\\psi_{\\alpha,\\epsilon}^\\gamma";
		elif type = "psi_aed" then
			funcstring := "\\psi_{\\alpha,\\epsilon}^\\delta";
		elif type = "com1" then
			funcstring := "f";
		elif type = "com2" then
			funcstring := "g";
		elif type = "com31" then
			funcstring := "h_1";
		elif type = "com32" then
			funcstring := "h_2";
		fi;
		string1 := TermAsString(term.subLeft);
		string2 := TermAsString(term.subRight);
		argument := inBrackets(Concatenation(string1, ",", string2));
		return Concatenation(funcstring, argument);
	fi;
end;

# ---- End of functions for terms ---

# ---- The blueprint rewriting rules, as in [BW, 8.11] ----

# Elementary homotopy 121 -> 212
rule121 := function(list, startindex)
	local a, b, c, transformedList;
	transformedList := StructuralCopy(list);
	a := list[startindex];
	b := list[startindex+1];
	c := list[startindex+2];
	transformedList[startindex] := c;
	transformedList[startindex+1] := RingAdd(RingMinus(b), RingMinus(RingMult(c, a)));
	transformedList[startindex+2] := a;
	return transformedList;
end;

# Elementary homotopy 212 -> 121
rule212 := function(list, startindex)
	local a, b, c, transformedList;
	transformedList := StructuralCopy(list);
	a := list[startindex];
	b := list[startindex+1];
	c := list[startindex+2];
	transformedList[startindex] := c;
	transformedList[startindex+1] := RingAdd(RingMinus(b), RingMinus(RingMult(a, c)));
	transformedList[startindex+2] := a;
	return transformedList;
end;

# rule13 and rule31 are the same.
ruleSwitch := function(list, startindex)
	local a, b, transformedList;
	transformedList := StructuralCopy(list);
	transformedList[startindex] := list[startindex+1];
	transformedList[startindex+1] := list[startindex];
	return transformedList;
end;

# Elementary homotopy 23232 -> 32323
rule23232 := function(list, startindex)
	local a, b, c, d, e, transformedList;
	transformedList := StructuralCopy(list);
	a := list[startindex];
	b := list[startindex+1];
	c := list[startindex+2];
	d := list[startindex+3];
	e := list[startindex+4];

	transformedList[startindex] := e;

	transformedList[startindex+1] := RingMinus(RingInv(RingAdd(RingAdd(RingAdd(RingMinus(psi_adb(e,RingMinus(b))),RingMinus(psi_aeb(e,a))),RingMinus(psi_ac(e,c))),RingMinus(d))));

	transformedList[startindex+2] := RingMinus(RingAdd(RingAdd(RingAdd(RingAdd(RingAdd(RingMinus(psi_adc(e,RingMinus(b))),RingMinus(psi_bd(RingMinus(psi_adb(e,RingMinus(b))),RingMinus(b)))),RingMinus(psi_bd(RingAdd(RingAdd(RingMinus(psi_aeb(e,a)),RingMinus(psi_ac(e,c))),RingMinus(d)),RingAdd(RingMinus(b),RingMinus(psi_aed(e,a)))))),RingMinus(psi_bec(RingAdd(RingAdd(RingMinus(psi_aeb(e,a)),RingMinus(psi_ac(e,c))),RingMinus(d)),a))),RingMinus(psi_aec(e,a))),c));

	transformedList[startindex+3] := RingMinus(RingInv(RingAdd(RingAdd(RingAdd(RingMinus(b),RingMinus(psi_aed(e,a))),RingMinus(psi_ce(RingAdd(RingAdd(RingMinus(psi_bec(RingAdd(RingAdd(RingMinus(psi_aeb(e,a)),RingMinus(psi_ac(e,c))),RingMinus(d)),a)),RingMinus(psi_aec(e,a))),c),a))),RingMinus(psi_bed(RingAdd(RingAdd(RingMinus(psi_aeb(e,a)),RingMinus(psi_ac(e,c))),RingMinus(d)),a)))));

	transformedList[startindex+4] := a;
	return transformedList;
end;

# Elementary homotopy 32323 -> 23232
rule32323 := function(list, startindex)
	local a, b, c, d, e, transformedList;
	transformedList := StructuralCopy(list);
	a := list[startindex];
	b := list[startindex+1];
	c := list[startindex+2];
	d := list[startindex+3];
	e := list[startindex+4];

	transformedList[startindex] := e;

	transformedList[startindex+1] := RingMinus(RingAdd(RingAdd(RingAdd(psi_bed(RingMinus(RingInv(b)),e),psi_aed(a,e)),psi_ce(RingMinus(c),e)),RingMinus(RingInv(d))));

	transformedList[startindex+2] := RingAdd(RingAdd(RingAdd(RingAdd(RingAdd(psi_bec(RingMinus(RingInv(b)),e),psi_bd(RingMinus(RingInv(b)),psi_bed(RingMinus(RingInv(b)),e))),psi_bd(RingAdd(RingMinus(RingInv(b)),psi_aeb(a,e)),RingAdd(RingAdd(psi_aed(a,e),psi_ce(RingMinus(c),e)),RingMinus(RingInv(d))))),psi_adc(a,RingAdd(RingAdd(psi_aed(a,e),psi_ce(RingMinus(c),e)),RingMinus(RingInv(d))))),psi_aec(a,e)),RingMinus(c));

	transformedList[startindex+3] := RingMinus(RingAdd(RingAdd(RingAdd(RingMinus(RingInv(b)),psi_aeb(a,e)),psi_ac(a,RingAdd(RingAdd(psi_adc(a,RingAdd(RingAdd(psi_aed(a,e),psi_ce(RingMinus(c),e)),RingMinus(RingInv(d)))),psi_aec(a,e)),RingMinus(c)))),psi_adb(a,RingAdd(RingAdd(psi_aed(a,e),psi_ce(RingMinus(c),e)),RingMinus(RingInv(d))))));

	transformedList[startindex+4] := a;
	return transformedList;
end;

# ---- End of blueprint rewriting rules ----

# ---- Blueprint computation, as in [BW, 8.9] ----

# Returns a list [ listDown, listUp ] which represents the result of the blueprint computation: listDown and listUp are lists of terms such that listDown[i] = listUp[i] is a blueprint identity for all i. All blueprint identities (i) for i <= idNum are used. If bPrintToFile is true, then a tex file with the results is printed to the directory mainDir.
# This function with idNum = 0 is used to compute the basic form of the 15 blueprint identities, which are given in Blue_Identities.pdf.
blueH3 := function(idNum, bPrintToFile)
	local list, listDown, listUp, i, homcycle, homcycle2, filestring, outputFile;
	
	defineComMaps(idNum);

	# Initialise listDown and listUp
	list := List(["y_1", "y_2", "y_3", "y_4", "y_5", "y_6", "y_7", "y_8", "y_9", "y_{10}", "y_{11}", "y_{12}", "y_{13}", "y_{14}", "y_{15}"], x -> IndetForString(x));
	listDown := StructuralCopy(list);
	listUp := StructuralCopy(list);
	
	# The homotopy cycle from [BW, Figure 6]. More precisely, homcycle contains the information that, at the i-th step, we apply rewriting rule homcycle[i][2] beginning at position homcycle[i][1].
	# homcycle contains the rewriting rules applied in rows (1)-(32)
	homcycle := [[1, 32], [5, 21], [7, 13], [10, 13], [8, 12], [10, 23], [4, 13], [9, 13], [5, 32], [3, 21], [9, 21], [5, 13], [11, 13], [8, 13], [2, 13], [6, 12], [14, 13], [12, 12], [8, 23], [7, 13], [3, 32], [1, 21], [7, 21], [3, 13], [6, 13], [4, 12], [9, 13], [12, 13], [10, 12], [6, 23], [5, 13]];

	# homcycle2 contains the rewriting rules applied in rows (63)-(32)
	homcycle2 := [[5, 31], [6, 32], [10, 21], [12, 31], [13, 12], [9, 31], [4, 21], [6, 31], [7, 12], [9, 23], [13, 31], [8, 31], [3, 31], [4, 32], [8, 21], [10, 31], [11, 12], [7, 31], [2, 21], [4, 31], [5, 12], [7, 23], [11, 31], [6, 31], [1, 31], [2, 32], [6, 21], [8, 31], [9, 12], [11, 23], [10, 31]];

	# Working down from (1) to (32) using homcycle
	for i in [1..31] do
		if homcycle[i][2] = 12 then
			listDown := rule121(listDown, homcycle[i][1]);
		elif homcycle[i][2] = 21 then
			listDown := rule212(listDown, homcycle[i][1]);
		elif homcycle[i][2] = 23 then
			listDown := rule23232(listDown, homcycle[i][1]);
		elif homcycle[i][2] = 32 then
			listDown := rule32323(listDown, homcycle[i][1]);
		else
			listDown := ruleSwitch(listDown, homcycle[i][1]);
		fi;
	od;

	# Working up from (63)=(1) to (32) using homcycle2
	for i in [1..31] do
		if homcycle2[i][2] = 12 then
			listUp := rule121(listUp, homcycle2[i][1]);
		elif homcycle2[i][2] = 21 then
			listUp := rule212(listUp, homcycle2[i][1]);
		elif homcycle2[i][2] = 23 then
			listUp := rule23232(listUp, homcycle2[i][1]);
		elif homcycle2[i][2] = 32 then
			listUp := rule32323(listUp, homcycle2[i][1]);
		else
			listUp := ruleSwitch(listUp, homcycle2[i][1]);
		fi;
	od;
	
	# Print one basic tex file containing all identities
	if bPrintToFile then
		filestring := Concatenation(mainDir, "Blue_Identities.tex");
		outputFile := OutputTextFile(filestring, false);
		SetPrintFormattingStatus(outputFile, false);
		PrintTo(outputFile); # Make file empty
		# Preamble of the tex file
		AppendTo(outputFile, "\\documentclass[a4paper,landscape]{article}\n");
		AppendTo(outputFile, "\\usepackage[left=1cm,right=1cm,top=1cm,bottom=2cm]{geometry}\n\n");
		AppendTo(outputFile, "\\title{Blueprint identities for $ H_3 $}\n");
		AppendTo(outputFile, "\\sloppy\n\n\\begin{document}\n\\maketitle\n");
		# Print all identites
		for i in [1..15] do
			AppendTo(outputFile, "\\section*{Identity ", String(i), "}\n\n");
			AppendTo(outputFile, "$ ", TermAsString(listDown[i]), " $\n\n\\addvspace{0.5cm}\n", "=", "\n\n\\addvspace{0.5cm}\n");
			AppendTo(outputFile, "$ ", TermAsString(listUp[i]), " $\n\n");
		od;
		# End of tex file
		AppendTo(outputFile, "\\end{document}");
		CloseStream(outputFile);
	fi;
	return [listDown, listUp];
end;

# Output: List [ term1', term2' ] where term1' and term2' are obtained from term1 and term2 by replacing all indeterminates (except for those whose numbers lie in nonZeroVars) by 0.
evaluateIdentity := function(term1, term2, nonZeroVars)
	local i, j, varName;
	for j in [1..15] do
		if j < 10 then
			varName := Concatenation("y_", String(j));
		else
			varName := Concatenation(Concatenation("y_{", String(j)), "}");
		fi;
		if not j in nonZeroVars then
			term1 := PlugInZero(term1, varName);
			term2 := PlugInZero(term2, varName);
		fi;
	od;
	return [term1, term2];
end;

# Creates a txt file with all evaluated blueprint identities (1), ..., (35). The resulting identities must be simplified by hand to obtain the identities in [BW, Figures 7 to 9]. The file is created in the directory mainDir.
identitiesForPaper := function()
	local blueResult, listDown, listUp, blueIdToEvalList, nonZeroVarsList, filestring, outputFile, i, blueId, result, idNum;
	
	blueIdToEvalList := [ 12, 5, 9, 9, 14, 5, 7, 7, 13, 3, 3, 12, 7, 11, 11, 6, 7, 8, 6, 9, 3, 3, 12, 11, 4, 5, 3, 13, 7, 3, 3, 4, 6, 11, 6 ]; # Second columns in Figures 7, 8, 0
	nonZeroVarsList := [ [ 4 ], [ 2, 15 ], [ 5, 8 ], [ 4, 5, 12 ], [ 1, 3 ], [ 1, 12 ], [ 4, 10, 12 ], [ 4, 10, 12 ], [ 1, 4 ], [ 7, 15 ], [ 10, 14 ], [ 2, 5 ], [ 7, 10 ], [ 1, 3, 8 ], [ 1, 4, 9 ], [ 3, 5, 13 ], [ 1, 4, 12 ], [ 4, 6, 15 ], [ 7, 10, 14 ], [ 2, 5, 14 ], [ 1, 14 ], [ 4, 15 ], [ 1, 5 ], [ 1, 5, 8 ], [ 4, 10, 15 ], [1, 4, 15 ], [ 5, 10, 15 ], [ 1, 5 ], [ 1, 5, 12 ], [ 3, 5, 15 ], [ 1, 5, 15 ], [ 1, 7, 15 ], [ 5, 10, 15 ], [ 1, 5, 12 ], [ 1, 4, 14 ] ]; # Third columns in Figures 7, 8, 9
	if Length(blueIdToEvalList) <> Length(nonZeroVarsList) then
		return fail;
	fi;
	filestring := Concatenation(mainDir, "blue_eval.txt");
	outputFile := OutputTextFile(filestring, false);
	SetPrintFormattingStatus(outputFile, false);
	PrintTo(outputFile); # Make file empty
	for i in [1..Length(blueIdToEvalList)] do
		# Perform the blueprint computation with all identities which are already established
		idNum := i-1;
		blueResult := blueH3(idNum, false);
		listDown := blueResult[1];
		listUp := blueResult[2];
		# Evaluate the result
		blueId := blueIdToEvalList[i];
		result := evaluateIdentity(listDown[blueId], listUp[blueId], nonZeroVarsList[i]);
		# Print it to a file
		AppendTo(outputFile, "Identity (", String(i), "):\n");
		AppendTo(outputFile, TermAsString(result[1]), "\n=\n");
		AppendTo(outputFile, TermAsString(result[2]), "\n\n");
	od;
	CloseStream(outputFile);
end;

writeFilesForPaper := function()
	blueH3(0, true);
	identitiesForPaper();
end;