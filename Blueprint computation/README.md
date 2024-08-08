In the file H3-blue.g, we perform the blueprint computation in [BW, Section 8]. More precisely:
1. Using GAP records, we define a data structure to represent mathematical terms as trees.
2. In "defineComMaps()", we define GAP functions to perform operations on these trees. The precise definition of these functions depends on the identities which have already been established.
3. We define the blueprint rewriting rules for H_3 in terms of these GAP functions.
4. We perform the blueprint computation.

The folder "Results" contains the files which are created by calling the function "writeFilesForPaper()". Namely, it contains:
1. The file "Blue_Identities.tex", which contains the full version of all 15 blueprint identities that result from the blueprint computation, and the pdf file that is created from this tex file.
2. The file "blue_eval.txt", which contains the 35 "evaluated blueprint identities" (see [BW, 8.2]). The reader can verify by hand that the identities (1) to (35) in [BW, Figures 7 to 9] follow from these identities.
