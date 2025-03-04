# Usage

## Read files (on Unix)

Download all files to a common folder, start a GAP session from this folder and execute the following command:
```
Read("./read.g");
```
This reads all involved files in the correct order.

## Read files (on Windows)

Download all files to a common folder ("your/file/path" in the following), start a GAP session and execute the following commands:
```
Read("your/file/path/H4-roots.g");
Read("your/file/path/H4-group.g");
Read("your/file/path/H3-group.g");
Read("your/file/path/H4-test.g");
```

## Execute tests (on all systems)

Then execute
```
testAll();
```
which executes all test functions in H4-test.g. If the function returns `true`, then all tests were successful (i.e., all claims about certain computations that we make in [BW] are correct). The test `testHTwistInvo(4)` (which is called by `testAll()`) is the most expensive one and displays some progress information. The whole test may take roughly one hour on a standard office PC.

# Documentation

The following is a brief description of the individual files.
1. `H4-roots.g`. In this file, we define the root system E_8 (as implemented in GAP), which is a subset of an 8-dimensional vector space, and  projection map on a 4-dimensional subspace. The image of E_8 under this map is H_4. We also define D_6 as a subset of E_8, and its image under the projection map is H_3. We further define various auxiliary functions for handling H_4 and H_3 in this way. The mathematical background is explained in [BW, Section 4].
2. `H4-group.g`. In this file, we first define the root homomorphisms of the adjoint Chevalley group of type E_8 (over a polynomial ring over the integers in sufficiently many variables) and then define an H_4-grading of this group. We also define functions which compute the so-called parity map of this group. The mathematical background is explained in [BW, Section 4].
3. `H3-group.g`. Similar to H4-group.g, but we construct the simply connected Chevalley group of type D_6 and an H_3-grading of this group.
4. `H3-test.g`. In this file, we define various test functions which prove certain claims in [BW]. Comments indicate which claims in [BW] are proven. The reader who wants to verify the correctness of these claims should call `testAll()` and observe that this function returns `true`. These tests involve both the H_3-graded group and the H_4-graded group from the previous files. In particular, the test functions verify that the commutator relations and the parity map of the H_3-graded group are the same as those of the H_4-graded groups on its standard H_3-subsystem.
5. `D6ChevBas.g`. This file is independent from the other files. The function `testChevStr()` verifies that the Chevalley basis used in H3-group.g is indeed a Chevalley basis (of type D_6). This is a well-known fact for which an explicit reference is difficult to find. This information is needed to justify that the constructed H_3-graded group may be called a "Chevalley group", but is otherwise not needed.
6. `read.g`. This is a helper file which simply reads all the other files.
