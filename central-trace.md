# Central defect traces for odd $m\ge5$

**Proposed analytic proof, 26 November 2026.** Prepared by coordinated AI agents and checked independently within that process; external expert review is pending.

This note derives the existing trace lookup discussed in
[DRINFELD issue 467](https://github.com/thomas-gemunden/DRINFELD/issues/467)
for every odd $m\ge5$, including the requested case $m=7$.
It uses the exact Schur-sum definition and conventions at commit
`219d8dbb2e2d6a4370b221f4a7a9c7b018214ded`: its deterministic symplectic
basis, elementary seed, zero linear shift and common normalization.
The argument is elementary binary linear algebra and quadratic summation.
No GAP execution, finite-vector enumeration or runtime measurement is reported.

## Theorem and exact conventions

Let $m\ge5$ be odd, put
$$
k=2^{m-1},\qquad d=2^{m-2}=k/2,\qquad D=2^k,
$$
and write an element of the prescribed extraspecial matrix group as
$$
h=z^\epsilon\prod_{i=1}^mX_i^{s_i}Z_i^{t_i},\qquad
s_i,t_i\in\mathbb F_2,\qquad Q=\sum_{i=1}^ms_it_i.
$$
Here $X_i=\mathrm{UnimodSigma}(m,i,1)$ and
$Z_i=\mathrm{UnimodSigma}(m,i,2)$ are row-action matrices in the original
$w_a$ basis. Tensor position $i$ is numerical bit $m-i$.
The exact row formulas appear in
[twisted_group_algebra.g, lines 26–55](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/twisted_group_algebra.g#L26-L55).
The underlying tensor generators are
[em_construction.g, lines 13–60](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/em_construction.g#L13-L60).
They give $h^2=z^Q$; all $s_i,t_i$ vanish exactly for $h=1,z$.

Let $S_h$ be the raw elementary-seed Schur sum, with $e=f=0$, linear
shift $s_h=0$, and the actual deterministic `BasisForN(m)`.
Put $A_h=S_h/D$. Then
$$
\operatorname{Tr} A_h=
\begin{cases}
2^k,&h=1\text{ or }z,\\
2^{\,k-2^{m-3}}=2^{3d/2},&h\text{ is a noncentral involution},\\
2^{\,k-2^{m-2}}=2^d,&h\text{ has order four}.
\end{cases}
$$
All these traces are positive. The raw trace is $D$ times the displayed
normalized trace. In particular, at $m=7$:

| Element | Normalized trace $\operatorname{Tr}A_h$ | Raw trace $\operatorname{Tr}S_h$ |
|---|---:|---:|
| $1$ or $z$ | $2^{64}$ | $2^{128}$ |
| Noncentral involution | $2^{48}$ | $2^{112}$ |
| Order four | $2^{32}$ | $2^{96}$ |

## 1. The actual polarization

For a numerical $m$-bit index $a$, put $\bar a=2^m-1-a$ and
$p(a)=m-\operatorname{wt}(a)\pmod2$. At odd $m$, the
[literal Gram formula](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/bw_lattice.g#L28-L56)
is
$$
G_{ab}=2^{(m-1-\operatorname{dist}(a,b)+p(a)+p(b))/2}.
$$
Let $M$ span the even-popcount $w_a$, and $O$ the odd-popcount $w_b$.
For $C_0=G\bmod2$, $C_0(M,M)=0$, an even $w_a$ pairs only with
$w_{\bar a}$, and two odd basis vectors pair exactly at Hamming distance
$m-1$. The diagonal is even; the mixed complement pairing makes $C_0$
nondegenerate.

The deterministic routine starts with increasing original standards:
[F2_BitsOfLen, lines 211–216](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/defect_rep_minus_id.g#L211-L216)
and [the pivot loop, lines 258–375](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/defect_rep_minus_id.g#L258-L375).
Its first $2^{m-3}$ pairs are $(w_a,w_{\bar a})$ for even-popcount
$a<2^{m-2}$, in increasing order. Each earlier odd index has already
been modified by a lower even one-bit neighbor. The next complement
cannot have been modified: two indices below $2^{m-2}$ differ in at
most $m-2$ bits. At each step every nonselected vector has zero pairing
with the first member, so its correction adds only that first member in $M$.

These pairs remove every odd standard. With high bits $00$, an odd
index has a lower even neighbor below $2^{m-2}$; with high bits $01$ or
$10$, clear that high bit; with high bits $11$, its complement was a
selected first member. The remaining $3\cdot2^{m-3}$ clean standards
lie in $M$, and every remaining composite is one distinct odd standard
plus an $M$ correction. The mixed stage pairs each remaining even
standard with the unique composite having its complementary odd
component. All further corrections remain in $M$.

Thus, after labeling the second members by odd subsets $I$, the actual
basis has
$$
\beta_I=w_I+m_I,\quad m_I\in M,
\qquad\alpha_I=w_{I^c}.
$$
Relabeling these coordinates is only a permutation; it introduces no
linear term into a zero-linear quadratic.

## 2. Exact shear entries and the literal Schur normalization

Reducing the row formulas for `UnimodSigma` modulo two gives
$$
h\bmod2=I+N_h,\qquad
N_h=\sum_i(s_iA_i^++t_iA_i^-).
$$
Here $A_i^+$ adds $i$ to an odd subset when absent, $A_i^-$ removes it
when present, and both kill $M$. Every product of two increments is
zero, so this expression is valid for every word, including its central
factor. In particular the corrections $m_I$ disappear under $N_h$.

In the actual symplectic coordinates,
$$
H_h=\begin{pmatrix}I&0\\K_h&I\end{pmatrix},\qquad
(K_h)_{I,J}=[w_{J^c}]\,N_hw_I.
$$
For $U=\{1,\ldots,m\}$, the precise coefficient formula is
$$
(K_h)_{I,J}=
\begin{cases}
s_i,&I\mathbin\triangle J=U\setminus\{i\},\ i\notin I\cup J,\\
t_i,&I\mathbin\triangle J=U\setminus\{i\},\ i\in I\cap J,\\
0,&\text{otherwise}.
\end{cases}
$$
The missing index $i$, when present, is unique. Hence $K_h$ is symmetric
with zero diagonal.

The code's
[cocycle and coordinate action](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/defect_rep_minus_id.g#L402-L438)
and [strict-upper defect matrix](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/defect_rep_minus_id.g#L486-L511)
therefore give
$$
R=\begin{pmatrix}0&I\\0&0\end{pmatrix},\qquad
R+H_hRH_h^T=\begin{pmatrix}0&0\\0&K_h\end{pmatrix},\qquad
B_h(a,b)=(-1)^{q_{K_h}(b)},
$$
where $q_K(b)=\sum_{I<J}K_{I,J}b_Ib_J$ uses the returned order.
The Weyl convention is $\rho(a,b)e_c=(-1)^{a\cdot c}e_{c+b}$, as in
[KRR v2, (4.1.5) and (4.2.2)–(4.2.9)](https://arxiv.org/pdf/2411.13646v2).

In the raw sum
$$
S_h=\sum_{a,b\in\mathbb F_2^k}
B_h(a,b)^{-1}\rho(a,b)^{-1}P_{00}\rho((a,b)H_h),
$$
only $b=c$ survives on $e_c$. The two $a\cdot c$ signs cancel and
$cK_hc^T=0$, leaving $D$ identical terms. Thus
$$
A_he_c=(-1)^{q_{K_h}(c)}e_c,\qquad
\operatorname{Tr}A_h=\sum_{c\in\mathbb F_2^k}(-1)^{q_{K_h}(c)}.
$$
This fixes the normalization directly; a physical implementer or its
unitarity is not a premise.

## 3. The exact zero-linear quadratic

Put $r=m-1$ and $W=\mathbb F_2\{e_2,\ldots,e_m\}$. Split the
odd-subset coordinate space as
$$
O=\Lambda^{\mathrm{odd}}W\oplus e_1\wedge\Lambda^{\mathrm{even}}W.
$$
Write its coordinates as $(x,y)$, and abbreviate the two $d$-dimensional
parity spaces by $O_r,E_r$. On either space define
$$
q(u)=\sum_{\{I,I^c\}}u_Iu_{I^c},\qquad
B(u,v)=[e_2\wedge\cdots\wedge e_m](u\wedge v).
$$
Here complements are inside $\{2,\ldots,m\}$, and each unordered
complementary pair is counted once. Since $r$ is even, complements
preserve parity. Each parity quadratic has $d/2$ disjoint pairs; its
polar form $B$ is nondegenerate and alternating. Denote the restrictions
by $q_o,q_e$ and $B_o,B_e$.

Set
$$
s=s_1,\quad t=t_1,\quad
C=\sum_{i=2}^m(s_i\,e_i\wedge+t_i\,\iota_i),\quad
Q_0=\sum_{i=2}^ms_it_i,
$$
where $\iota_i$ is contraction by the dual basis vector. Section 2's
coefficient formula gives exactly
$$
q_{K_h}(x,y)=F(x,y)
 =s\,q_o(x)+t\,q_e(y)+B_o(x,Cy).\tag{1}
$$
For $i=1$ the two indices have the same first bit and complementary
remaining $r$ bits, giving the two $q$ terms. For $i>1$ their first
bits differ; $B_o(e_I,Ce_J)$ gives exactly the toggle coefficient.
Equivalently the cross term is $B_e(Cx,y)$. Both sides have zero
constant and linear terms, so the coefficient comparison proves (1)
without a gauge correction.

## 4. Clifford identities and the null rank

Wedge and contraction satisfy
$$
C^2=Q_0I,\qquad B(Cu,v)=B(u,Cv).
$$
The second identity follows from the top-degree pairing and the
derivation rule for contraction, in characteristic two. Consequently
$B(Cu,Cv)=Q_0B(u,v)$. The polar form of $q(Cu)+Q_0q(u)$ is zero, so
this function is linear. It vanishes on each exterior monomial:
the image under $C$ is supported on one-bit neighbors, any two of
which differ in at most two bits and therefore cannot be complementary
when $r\ge4$. Thus
$$
q_o(Cy)=Q_0q_e(y),\qquad q_e(Cx)=Q_0q_o(x).\tag{2}
$$
This is the step requiring $m\ge5$ among odd $m$.

If $Q_0=1$, $C$ is an isomorphism between the parity spaces.
If $Q_0=0$ and $C\ne0$, choose an odd Clifford operator $J$ with
$CJ+JC=I$: take $J=\iota_i$ when $s_i=1$, or $J=e_i\wedge$ when
$t_i=1$. Then $\ker C=\operatorname{im}C$ on the full
$2d$-dimensional exterior algebra, so the total rank is $d$.
Each parity image is $B$-isotropic, since $B(Cu,Cv)=0$.
Nondegeneracy bounds each image dimension by $d/2$; the two ranks
sum to $d$, so both are exactly $d/2$.

## 5. Signed Gauss sums

For either parity, the $d/2$ complementary pairs give
$$
\sum_u(-1)^{q(u)}=2^{d/2},\qquad \sum_u1=2^d.
$$
The sign is positive because each pair contributes
$\sum_{a,b\in\mathbb F_2}(-1)^{ab}=2$.

**Case $s=1$.** By (2), complete the square:
$$
F(x,y)=q_o(x+Cy)+(t+Q_0)q_e(y).
$$
The variable change is a bijection. Since $Q=t+Q_0$, the sum is
$2^{3d/2}$ when $Q=0$ and $2^d$ when $Q=1$, both positive.

**Case $s=0,t=1$.** Self-adjointness and (2) give
$$
F(x,y)=q_e(y+Cx)+Q_0q_o(x).
$$
Here $Q=Q_0$, yielding the same two values.

**Case $s=t=0$.** Fourier orthogonality gives
$$
\sum_{x,y}(-1)^{B_o(x,Cy)}
 =2^d\lvert\ker(C:E_r\to O_r)\rvert
 =2^{2d-\operatorname{rank}(C|_{E_r})}.
$$
The operator $C$ vanishes exactly when all its coefficients vanish:
apply it to $1$ and then to each $e_i$. This gives $h=1,z$ and trace
$2^{2d}=2^k$. Otherwise the parity rank is $d/2$ for $Q_0=0$ and
$d$ for $Q_0=1$, giving $2^{3d/2}$ and $2^d$ respectively.
These cases exhaust all $h$ and prove the theorem.

## 6. Why $m=3$ is excluded

The polarization, shear, Schur normalization and null-rank arguments
still hold at $m=3$, but (2) can fail. The tail now has two generators.
For $C=e_2\wedge+e_3\wedge$, one has $Q_0=0$ while
$$
C1=e_2+e_3,\qquad q_o(C1)=1.
$$
Two one-bit neighbors are now complementary.

This gives a literal counterexample to extending the lookup to $m=3$.
Take the noncentral involution $h=X_1X_2X_3$. Write
$x=x_2e_2+x_3e_3$ and $y=y_0+y_{23}e_2\wedge e_3$.
Formula (1) becomes
$$
F=x_2x_3+y_0(x_2+x_3).
$$
The $y_{23}$ variable is free. Summing over $x_2,x_3$ gives $+2$ for
$y_0=0$ and $-2$ for $y_0=1$, hence
$\operatorname{Tr}A_h=2(2-2)=0$. The extrapolated lookup would give
$2^{4-1}=8$.

## Scope

This proves the specified mathematical Schur trace for every odd
$m\ge5$, using the pinned deterministic polarization and common-$D$
normalization. It does not verify optimized evaluators, caches, integer
solvers or production code paths. No even-$m$ claim is made.
The normalized/raw distinction is essential.

The result does not use or establish vanishing of the full VOA anomaly.
The existing lookup is
[implemented here](https://github.com/thomas-gemunden/DRINFELD/blob/219d8dbb2e2d6a4370b221f4a7a9c7b018214ded/extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g#L1220-L1259).
This note supplies an analytic justification on the odd-$m$ range
$m\ge5$, without claiming a new implementation or measured speed improvement.
