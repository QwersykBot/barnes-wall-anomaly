A CONDITIONAL UNITARY c = 128 HOLOMORPHIC VOA WITH GROUP E8(2)
Proof package and dependency guide
26 November 2026

RESULT AND STATUS

The four core notes and the two addenda establish the following implication.
Take the VOA W32, its specified elementary abelian automorphism subgroup,
and the VOA U with its fusion, module, and automorphism data as proved in
Gerald Höhn, Hexagon 2611.00631v2, dated 20 November 2026. Then the full
diagonal extension of U tensor U, followed by the orbifold of its literal
flip, is a strongly rational holomorphic VOA Y such that

  c(Y) = 128,
  Y1 = 0,  dim Y2 = dim Y3 = 1,
  dim Y4 = dim Y5 = 545925252,
  Aut(Y) is isomorphic to E8(2),
  Y admits a positive unitary VOA structure.

In particular, its first nonvacuum Virasoro primary space occurs in
weight four and has dimension 545925250. Its weight-four and weight-six
primary spaces are irreducible modules of dimensions 545925250 and
76321227908420, respectively; the weight-five primary space is zero.
Every homogeneous space Y_n is a conformal 6-design. An explicit
centralizer-fixed primary idempotent witnesses the nonzero E8(2)-invariant
cubic, which is unique up to scale. Its four multiplication eigenvalues
are computed directly.

This is a conditional mathematical result with explicit inherited inputs,
not a claim to have independently verified Höhn's entire recent preprint.
The new extension, actual automorphism, finiteness, simplicity, and group
identification arguments have undergone several internal mathematical
reviews. That is not external peer review or a computer-formalized proof.
The package was prepared by AI agents; no external specialist acceptance
or human-authored proof is represented here.
No claim of priority is made. The package preserves enough detail and
primary-source locations for an independent reader to check each step.

HOW TO READ THE PACKAGE

1. diagonal-flip-c128-extraspecial-construction-20261126.txt
   Constructs the specified Y and its exact character. Computes the
   actual elementary-group anomaly, the explicit bimodule associator,
   and the full-center identification of the SAME extension. This gives
   an actual extraspecial subgroup and the exact full involution
   centralizer. Its final finiteness statement is conditional until
   the next note supplies the required three-cycle.

2. diagonal-flip-permutation-preservation-20261126.txt
   Places that SAME Y in a full elementary abelian orbifold problem
   on W32^tensor4. Determines its actual relative extension support
   by the individual twisted ground labels. Proves preservation by
   factor permutations, and lifts an actual order-three automorphism
   cycling three commuting involutions inside the extraspecial group.

3. extraspecial-centralizer-elementary-simplicity-20261126.txt
   Proves a general elementary finite-group criterion. Applied to the
   full centralizer and actual fusion from the first two notes, it
   proves that Aut(Y) is simple. It uses only Sylow theory and elementary
   properties of extraspecial groups, not a classification theorem.

4. e8-recognition-from-extraspecial-centralizer-20261126.txt
   Applies the exact standalone classification theorem on page 283 of
   Aschbacher's ICM 1978 survey. Checks its hypotheses and eliminates
   all listed alternatives by exact group-order arguments. This is
   the source used for recognition; no unread Smith theorem or an
   unaudited formalization is substituted for it.

5. unitarity-three-axis-20261126.txt
   Proves positivity of this same Y from its three actual conjugate
   axes, finite automorphism groups of the fixed algebras, and Gui's
   precise theorem for preunitarizable simple-current extensions.
   It does not depend on the E8(2) recognition step. This addendum
   supplies the unitarity conclusion that the earlier frozen core
   notes deliberately left open.

6. e8-minimal-primaries-conformal-designs-and-e7-axis-20261126.txt
   Deduces the irreducible primary modules through weight six and the
   conformal-design assertion. Computes the explicit primary cubic,
   idempotent, and multiplication spectrum from ordinary Virasoro
   and permutation-twisted OPE calculations. Uses the published complete
   ordinary E8(2) character-degree data, with the exact checks below.

The additional independent review of the permutation argument is an
audit record, not a substitute for any of these proofs. SHA256SUMS
pins every included file. The archive contains no copies of the cited
research papers; the notes give their primary-source locations. The
character-screen folder contains the primary author's numerical data and
the small exact-integer scripts used to check the representation constraints;
it does not contain any research-paper text.

NOTATION ACROSS THE NOTES

The individual notes were written independently and sometimes reuse
letters. This dictionary fixes the objects needed for their interfaces.

  W32       Höhn's holomorphic VOA of central charge 32.
  A27       O2(Aut(W32)), elementary abelian of order 2^27.
  U         (W32 tensor W32)^(diagonal A27 times swap), c = 64.
  D         The 56-dimensional hyperbolic fusion space of U.
  X         Direct sum over d in D of U_d tensor U_d, c = 128.
  sigma     The literal flip of the two positions in every X summand.
  Xplus     X^sigma.
  Y         Xplus plus the integral sigma-twisted constituent of X.
  z         Its quantum involution, negative on the twisted constituent.
  R         The actual extraspecial group 2_+^(1+56) in Aut(Y).
  H         The full automorphism group Aut(Y).
  C         C_H(z), with R normal and C/R = E7(2).
  P         The Klein four of double transpositions on four W32 factors.
  K         Diagonal A27 times P, an elementary group of order 2^29.
  Nbase     (W32^tensor4)^K, the pointed base used in the second note.

In particular, the symbol N for the extraspecial group in the first
note is different from the symbol N for Nbase in the second note.
The symbol Q in the simplicity note means R in this dictionary.

THE COMPLETE LOGICAL CHAIN

A. Construction and low weights.

The diagonal subgroup of D plus D is self-perpendicular and isotropic.
The isotropic simple-current extension theorem gives X. Its literal flip
preserves products because each projected intertwiner is a scalar times
the tensor square of the same intertwiner. The Fourier modular matrix
of U transforms its flip trace to 2^28 chi_U(tau/2). The twisted ground
therefore has weight four and dimension 2^28; the flip has cyclic type
zero. The canonical integral twisted constituent gives Y. Direct counts
give the dimensions displayed above.

B. An actual extraspecial group, not only a fusion rule.

The group Gamma = D* times <sigma> acts faithfully on X. Its anomaly
has cyclic restriction epsilon q_D(t), represented by the explicit
cocycle (-1)^(epsilon f(u,v)). Gauging <sigma> gives a dual category
whose simple objects multiply as

  (t,r)(u,s) = (t+u, r+s+f(t,u)).

The note computes the tensorators and shows that the resulting associator
is trivial. The full-center correspondence identifies the algebra object
of this Y with the regular algebra Fun(R) in Z(Vec_R). Its translations
are actual VOA automorphisms. Tracking the electric labels identifies
Z(R)=<z> and the quotient action on Xplus with the original D*.

C. The full centralizer.

X2 has exactly two primitive conformal idempotents. They recover the
two U factors intrinsically, so Aut(X) is (D*.E7(2)) times <sigma>.
The three nonvacuum Xplus modules have distinct minimum weights
2, 4, and 11/2. Every automorphism of Xplus therefore fixes both
extension classes, and the exact simple-current lifting sequences give

  1 -> <z> -> C_H(z) -> Aut(Xplus) -> 1,
  1 -> R -> C_H(z) -> E7(2) -> 1.

The quotient acts faithfully on R/<z>. Consequently C_C(R)=<z>.
Splitting of either dotted extension is not needed.

D. The extra three-cycle acts on the same extension.

The second note identifies a common intermediate extension of U tensor U
and compares its actual flip, then proves that Y's support over Nbase
is transverse to the untwisted charge subgroup K*. Thus Y selects one
simple module in every K-flux. Every nontrivial permutation flux has a
unique weight-four ground line. The specified extension contains all
these intrinsic labels: the paired-flip sectors are compared explicitly,
and the remaining 2^28 individual upper bounds all saturate. Their fluxes
span K, so their labels determine the entire support.

Actual factor permutations preserve that support and therefore lift.
If g lifts a three-cycle, g^3 lies in the elementary abelian kernel K*,
so g^4 is an actual order-three lift. It cycles the three nonzero
characters in P*. The electric-label comparison places all of K*,
and hence these three axes, in R.

E. Finiteness and irreducibility.

C2-cofiniteness gives finite generation. Dong--Griess algebraicity then
makes H a finite-dimensional affine algebraic group. The three axes
have conjugate finite full centralizers. Every complex character of
their Klein four has a nontrivial kernel, so their Lie-algebra fixed
spaces being zero forces Lie(H)=0. Thus H is finite.

Irreducibility of C on R/<z> also has a short check using the supplied
module data. The smallest nonzero E7(2)-orbit in D has size 277347807,
which exceeds 2^28-1. A nonzero invariant subspace must therefore have
dimension at least 29. If it were proper, its nonzero orthogonal
complement for the invariant nondegenerate polar form would have
dimension at most 27, a contradiction. This uses no separate modular
representation irreducibility theorem.

F. Simplicity.

Apply the third note with R of extraspecial width 28. Every nontrivial
normal subgroup contains R, by irreducibility and the three-axis fusion.
If its centralizer of z were exactly R, Frattini's argument would make
the second axis conjugate to z inside that normal subgroup. The
intersection of the two extraspecial centralizers would then have
derived subgroup both <z> and the distinct second axis, impossible.
It follows that the normal subgroup contains C; another Frattini
argument gives all of H. Hence H is nonabelian simple.

G. Recognition.

The ICM classification theorem now applies to the 2-local C. Its
characteristic-abelian hypothesis follows from irreducibility: an
abelian characteristic subgroup of R must lie in its cyclic center.
The Sylow 2-subgroup order of H is 2^(57+63)=2^120. The exact list in
the theorem and standard order formulas leave only L16(2), U16(2),
and E8(2) among its groups over the field of order two. E7(2) contributes
the primes 19 and 73 to |C|. The order of 2 modulo 19 is 18, excluding
L16(2); the order of -2 modulo 73 is 18, excluding U16(2). The fourth
note checks every remaining listed exception, including the odd-field
PSL2 family and historical sporadic names. Therefore H = E8(2).

H. Positivity and the first representations.

The unitary lattice and permutation-twisted-module results provide
positive U-module forms. Gui's simple-current theorem gives the actual
X a unitary structure, and finiteness of Aut(X) makes the flip unitary.
Its fixed algebra Z is unitary. For D0=Y^(P*), all three conjugate fixed
algebras transport positive forms to the same base D0. A finite-index
support-stabilizer lifting argument proves Aut(D0) finite. Comparing
the normalized PCT structures then shows that all three base forms
coincide. Their simple-current constituents cover Y. Gui's theorem
therefore supplies a positive form for the actual multiplication on Y.

The complete E8(2) degree census forces its nontrivial weight-four
primary representation to be irreducible. In weight six, dimension
and the actual quantum-involution trace force the next irreducible:
trying to use only trivial and weight-four constituents would require
a negative trivial multiplicity. The fixed spaces through weight six
are therefore exactly the vacuum Virasoro spaces. Finite averaging
gives the conformal 6-design trace identities on every Y_n.

For the explicit primary P=80A-48B-171C in the two-factor Virasoro
space, its projected product satisfies P circle P=22548P, with norm
57959424. The normalized idempotent P/22548 has eigenvalues

  1, 112/1879, 5/5637, -57/60128,

with respective multiplicities 1,141986,277347807,268435456. In
particular its cubic is nonzero. The last eigenvalue is obtained by
subtracting the ordinary VOA stress-field OPE on the permutation
cover, independently of a trace-zero identity.

REPRODUCING THE FINITE NUMERICAL CHECKS

The package contains mathematical proofs in the six notes and exact
finite calculations supporting their displayed numbers. Running the
latter does not certify the full VOA or group proof. The three Python
scripts use only the standard library. From the package root, run:

  python3 check_character_low_weights.py
  python3 e8-minimal-cubic-screen/analyze_e82.py e8-minimal-cubic-screen/E82cl.g
  python3 e8-minimal-cubic-screen/exhaust_degree_splits.py e8-minimal-cubic-screen/E82deg.g e8-minimal-cubic-screen/result.json

The first reconstructs the c=128 character from its six low coefficients
and the displayed modular-uniqueness argument, then computes the primary
dimensions and involution traces. Its receipt is character-low-weights.json.
The other two scripts use the frozen author-hosted E8(2) class and degree
data; their acquisition metadata, source hashes, and receipts are in
e8-minimal-cubic-screen/. Consult its README for the mathematical
interpretation of the symmetric-cubic calculation.

Run sha256sum -c SHA256SUMS from the package root to verify all file bytes.
All dependencies on external theorems remain stated in the notes.

BOUNDARIES AND NEXT QUESTIONS

The construction has the same entire graded character as the dense
Barnes--Wall orbifold T0 from the separate anomaly project, conditional
on that project's premises. Equality of characters does not identify
their vertex products; no isomorphism Y = T0 is used or proved here.
Likewise, this package does not claim uniqueness of all VOAs with this
character. Unitarity is proved separately in the fifth note and is not
an input to the four core proofs. Strong locality, a conformal-net
realization, a weight-seven design assertion, and a complete axial
fusion law are not claimed.

The immediate external-validation target is review of these actual
product, support, lift, and recognition arguments by specialists,
together with scrutiny of the inherited recent Höhn construction.
Internal agreement and the number of artifacts are not evidence of
independent adoption or external mathematical acceptance.
