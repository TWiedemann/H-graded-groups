# Usage

Attention: This script write files to your file system.

## Download and setup

Download `H3-blue.g` and change the value of the variable `mainDir` at the top of the file to the file path where you want to store the output of the computation. By default, this is `"Desktop/"` which should work on a Windows machine.

## Read files (on Unix)

Open the terminal, navigate to the folder in which you have stored `H3-blue.g` and start a GAP session there. Then execute the following command:
```
Read("./H3-blue.g");
```

## Read files (on Windows)

Start a GAP session and execute the  command
```
Read("your/file/path/H3-blue.g");
```
where `"your/file/path/H3-blue.g"` is the path where you have stored `H3-blue.g`.

## Execution

Execute `writeFilesForPaper()`.
This creates two files in `mainDir` (see also [BW, 9.2]):
1. `Blue_Identities.tex`, which contains the full version of all 15 blueprint identities that result from the blueprint computation.
2. `blue_eval.txt`, which contains the 35 "evaluated blueprint identities". The reader can verify by hand that the identities (1) to (35) in [BW, Figures 7 to 9] follow from these identities.

# Results

For convenience, the folder `Results` in this repository contains the files `Blue_Identities.tex` and `blue_eval.txt` as well as the pdf file `Blue_Identities.pdf` that is obtained by compiling `Blue_Identities.tex`. Note that the main purpose of `Blue_Identities.tex` and `Blue_Identities.pdf` is to illustrate that the full blueprint identities (unlike the evaluated bluepring identities) are too long to be accessible for manipulation by hand (see [BW, 9.2])

# Mathematical details

See [BW, Sections 8 and 9].

# Implementation details

1. Using GAP records, we define a data structure to represent mathematical terms as trees.
2. In `defineComMaps()`, we define GAP functions to perform operations on these trees. The precise definition of these functions depends on the identities which have already been established.
3. We define the blueprint rewriting rules for H_3 in terms of these GAP functions: `rule121`, `rule212`, `ruleSwitch`, `rule23232`, `rule32323` ([BW, 8.11]).
4. We perform the blueprint computation: `blueH3` ([BW, 8.9]). To obtain the full blueprint identities, call `blueH3(0, true)`. To obtain a simplified version of the blueprint identities in which the validity of the `i`-th blueprint identity is used for all `i <= idNum`, call `blueH3(idNum, true)`.
5. We compute the "evaluated blueprint identities" ([BW, 9.2]): `identitiesForPaper()`.

