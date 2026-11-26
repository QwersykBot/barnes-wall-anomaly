E8(2) MINIMAL-CHARACTER CUBIC: EXACT DATA AND DEGREE EXHAUSTION
26 November 2026 -- internal reproducible calculation and elementary deduction

Scope
-----
Let V be the complex irreducible E8(2)-representation of degree
d=545,925,250 in Frank Luebeck's published data. This note determines its
tensor square, symmetric/exterior squares, and invariant cubic dimension
from those data. It does NOT construct an E8(2) action on any VOA, identify
a VOA primary space with V, or prove equivariance of a proposed product.
No GAP code, power maps, representation matrices, or q-series were used.

1. Primary source and acquisition
-------------------------------
Author's explanatory page:
https://www.math.rwth-aachen.de/~Frank.Luebeck/chev/E82.html

It describes the complete character-degree list and all values of the
minimal nontrivial character, while stating that the full complex
character table is not known. These are the author's computational data;
the underlying character calculations were not rederived here.

Class centralizers and minimal-character values:
https://www.math.rwth-aachen.de/~Frank.Luebeck/chev/E82cl.g
  15,478 bytes; acquired 2026-11-26 18:47:10.085752 UTC; HTTP 200.
  Server Last-Modified: 10 May 2007 12:51:01 GMT.
  SHA256 ddc0c0d747652eef78439c0caf3bdf4e92c359671f1b5a093612c60cf0cb8972
  Acquisition metadata: acquisition.json

All character degrees, with multiplicity:
https://www.math.rwth-aachen.de/~Frank.Luebeck/chev/E82deg.g
  43,529 bytes; acquired 2026-11-26 18:48:32.291299 UTC; HTTP 200.
  Server Last-Modified: 20 July 2004 21:50:22 GMT.
  SHA256 1bcd2e7862193f9d406193e856a9c41bf236d683fb11c8cb6e8fb0e04c79e1be
  Acquisition metadata: degrees-acquisition.json

The scripts accept only the expected named integer assignments/lists.
They never execute or evaluate the downloaded GAP-language text.

2. Exact rational inner products and alignment checks
----------------------------------------------------
For k=0,1,2,3, analyze_e82.py computes, using fractions.Fraction,

  m_k = sum_C chi(C)^k / |C_G(g_C)|.

All 1156 centralizer orders and all 1156 character values are used.
Results are exact fractions with denominator 1:

  m_0=1,   m_1=0,   m_2=1,   m_3=1.

Every centralizer order is positive and divides the stated group order.
The class sizes sum to that group order. The first centralizer order is
the group order; the first character value is d. The first three values
are 545925250, 9054338, 665730, matching the explanatory page's initial
class rows identity, A1, 2A1. No assumption about a VOA class fusion enters.

Since the published character is integer-valued, V is self-dual. Thus
m_2=1 is the trivial multiplicity in V tensor V, and m_3=1 is both the
invariant tensor-cube dimension and the multiplicity of V in V tensor V.
These computations alone do not distinguish a symmetric cubic.

3. Complete small-degree census
------------------------------
d^2 = 298,034,378,587,562,500.

Parsing ALL 1156 entries of the degree list gives exactly the following
irreducible degrees <=d^2, each occurring once in the published list:

                    1
          545,925,250
       76,321,227,908,420       denote its irrep U_a
   46,453,389,380,074,796       unused in the tensor square below
   51,320,060,161,363,500       denote its irrep U_b
   97,697,128,859,455,125       denote its irrep U_c
  144,074,197,011,621,500       unused in the tensor square below
  148,940,867,792,910,204       denote its irrep U_e

The 97,697,128,859,455,125 degree is essential: it is outside the first
unipotent-series row and appears in the page's E7(q) series, row 5.
It was absent from the initial suggested shortlist, but is included in
EVERY exhaustive computation reported here.

Published degree-list multiplicity is not a bound on tensor multiplicity.
The algorithm allows arbitrary nonnegative tensor multiplicities subject
only to dimension. Uniqueness of each listed degree means a unique degree
decomposition here also identifies the irreducible constituents.

4. Exhaustive degree and square-split algorithm
---------------------------------------------
The known multiplicities of 1 and V are exactly one. The remaining target
is d^2-1-d. For each degree larger than a=76,321,227,908,420, recursively
enumerate multiplicities from 0 through floor(remaining_target/degree).
At a leaf, determine the multiplicity of U_a by EXACT residual division;
reject if the remainder is nonzero. This enumerates every nonnegative
integer solution, not just bounded guesses or a single successful fit.

In ascending order the five larger degrees have initial multiplicity
bounds 6,5,3,2,2: at most 7*6*4*3*3=1512 outer tuples. Pruning by the
remaining nonnegative target leaves 72 exact residual divisions.
There is exactly ONE tensor-square solution:

  V tensor V = 1 + V + U_a + U_b + U_c + U_e.

All displayed constituents have multiplicity one; the two other degrees
in Section 3 have multiplicity zero.

Next split every such tensor decomposition into symmetric/exterior
parts of dimensions

  dim Sym^2 V = 149,017,189,566,743,875,
  dim Alt^2 V = 149,017,189,020,818,625.

The algorithm initially permits BOTH placements of 1 and BOTH placements
of V. It enumerates every larger-degree multiplicity between zero and
its tensor multiplicity, then obtains the U_a multiplicity by residual
division and checks its allowed bound. There are 19 division leaves and
exactly TWO dimension-compatible splits:

  I:  Sym^2 V = V + U_b + U_c;
      Alt^2 V = 1 + U_a + U_e.

  II: Sym^2 V = 1 + V + U_a + U_e;
      Alt^2 V = U_b + U_c.

In BOTH splits, the single copy of V lies in Sym^2 V. Dimension constraints
alone therefore force this placement, but do NOT distinguish the two
Frobenius-Schur signs. The raw result preserves both solutions.

5. The unique invariant cubic is symmetric
-----------------------------------------
Self-duality and Section 4 give a nonzero equivariant map Sym^2 V -> V.
Pairing its value with a third vector using any invariant nondegenerate
bilinear form gives a nonzero invariant trilinear form fixed by the
transposition (12). By Section 2 the space of invariant trilinear forms
has dimension ONE. The permutation action on this line is a
one-dimensional representation of S3. All transpositions are conjugate,
so if (12) acts by +1, every transposition does. The form is fully
symmetric. Consequently

  dim (Sym^3 V)^E8(2) = 1,
  dim (Alt^3 V)^E8(2) = 0.

This deduction does not use power maps or assume symmetry from a tensor
cube count alone.

6. Frobenius-Schur sign and the actual square decomposition
----------------------------------------------------------
There is also an elementary argument selecting split II. A self-dual
irreducible representation of a finite group is real or quaternionic.
If V were quaternionic, it would admit a commuting invertible antilinear
J with J^2=-I. Then J tensor J tensor J would preserve (V tensor^3)^G
and square to -I there. That space has complex dimension one by m_3=1.
But an antilinear map on a complex line has the form z -> c conjugate(z),
whose square is |c|^2 I, never -I. This is a contradiction.

Thus V has Frobenius-Schur indicator +1. Its unique invariant bilinear
form is symmetric; 1 lies in Sym^2 V. The actual decomposition is

  Sym^2 V = 1 + V + U_a + U_e,
  Alt^2 V = U_b + U_c.

This sign argument is separate from the dimension enumeration. It does
not alter or discard either solution in the saved raw computation.

7. Replay and frozen identities
------------------------------
Python 3 standard library only, from this directory:

  python analyze_e82.py E82cl.g
  python exhaust_degree_splits.py E82deg.g result.json

The second command uses the preserved exact inner-product receipt. No
network is needed after acquiring the two pinned data files. Compare the
JSON output with result.json and degree-splits-result.json respectively.

analyze_e82.py:
  3b7bad97f5920da61922cad0af0246aff118a79e3527522e3bebd8f24b709187
result.json:
  af556875211def71a31460296872794883f53be719ba6b07df2087aa04779bab
acquisition.json:
  e2ca27814c89f2b251ee301b23787cadac7383b897f6ff5d1dd5b793f41815de
exhaust_degree_splits.py:
  cd694d9ac18b15638ab143f3765f17047f7601b419c207a3cef988eb28c91ea2
degree-splits-result.json:
  db71bf1c75fd480fd18ba40f7af922a09f8d7b2101e05a42b79cfc96a8297ad6
degrees-acquisition.json:
  d21e706611302683a88906ec44c04ef4b34d0ab8b5bb6476a2e448621d86d70c

The original inner-product script, data and receipt were left unchanged
when the degree-exhaustion calculation was added. This directory accompanies
the conditional diagonal-flip proof package and records exact supporting
calculations; it is not an independent construction of a VOA action.
