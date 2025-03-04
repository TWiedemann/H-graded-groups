# Usage

Attention: This script write files to your file system.
1. Download `H3-blue.g`.
2. Change the value of the variable `mainDir` at the top of the file to the file path where you want to store the output of the computation. By default, this is `"Desktop/"` which should work on a Windows machine.
3. Execute `writeFilesForPaper()`.
This creates two files in `mainDir`, which are also provided in the `Results` folder of this repositor for convenience. Namely, it contains:
1. The file `Blue_Identities.tex`, which contains the full version of all 15 blueprint identities that result from the blueprint computation, and the pdf file that is created from this tex file. The main purpose of this file is to illustrate that the blueprint identities are too long to be accessible for manipulation by hand (see [BW, 8.2]). For convenience, we also provide the compiled pdf file.
2. The file `blue_eval.txt`, which contains the 35 "evaluated blueprint identities" (see [BW, 8.2]). The reader can verify by hand that the identities (1) to (35) in [BW, Figures 7 to 9] follow from these identities.

# Mathematical details

See [BW, Sections 7 and 8].

# Implementation details

1. Using GAP records, we define a data structure to represent mathematical terms as trees.
2. In `defineComMaps()`, we define GAP functions to perform operations on these trees. The precise definition of these functions depends on the identities which have already been established.
3. We define the blueprint rewriting rules for H_3 in terms of these GAP functions.
4. We perform the blueprint computation.

