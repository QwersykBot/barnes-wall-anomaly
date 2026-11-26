# Appendix: a direct conformal-net consequence

**Draft for mathematical review, 26 November 2026.** This appendix derives a conformal-net consequence from four stated inputs of the Barnes–Wall argument. The analytic derivation is included here. Prepared by coordinated AI agents; external expert review is pending. It does not assume equality of VOA and net anomalies, or an identification of an algebraic full-orbifold VOA with the net extension constructed below.

## A. Statement and inputs from the main argument

Let $L=BW(7)$ in the KRR normalization, a positive even unimodular lattice of rank $128$. Retain the following four inputs from the [main argument at the pinned revision](https://github.com/QwersykBot/barnes-wall-anomaly/blob/7f9b50a009ae08eb037dd233a2fcb5d3c5d7e4bb/proof.md).

1. **The actual extraspecial action.** The prescribed unitary sign lifts give a faithful group $E=2_+^{1+14}$ on $V_L$. Its involutions are standard lifts. On the real Heisenberg space, the central involution $z$ is $-I$; a noncentral involution has $64$ eigenvalues of each sign; every order-four element squares to $z$.
2. **The common quaternion subgroup.** The specified order-eight lift $g$ and its companion generate an actual $Q_{16}$, whose common $Q_8$ is the prescribed subgroup of $E$, including all lift phases. The real action of $g$ has each primitive eighth root as an eigenvalue with multiplicity $32$. Its lift is standard.
3. **The cohomological detector.** A class in $H^4(E,\mathbb Z)$ vanishing on every involution subgroup and on that $Q_8$ is zero. The restrictions from $H^4(Q_{16},\mathbb Z)$ to its indicated $C_8$ and $Q_8$ have the same kernel.
4. **The invariant vacuum spectrum.** $(V_L)^E$ has only Virasoro vacuum descendants below weight four and contains the exhibited nonzero Virasoro primary of weight four.

These inputs concern the specified lifts and subgroups, rather than just their projected orthogonal matrices.

**Claim.** Subject to inputs 1–4, the action of $E$ on the lattice conformal net $\mathcal A_L$ has trivial intrinsic net anomaly. The fixed net $\mathcal A_L^E$ admits a holomorphic local conformal extension $\mathcal B$ of central charge $128$ whose primary gap is exactly four.

Here the primary gap is the smallest positive eigenvalue of the vacuum conformal Hamiltonian supporting a nonzero Virasoro highest-weight vector. All energies below are absolute $L_0$ eigenvalues with vacuum energy zero.

## B. The established lattice-net base

Gui [G, Theorems 3.46 and 3.48] supplies strong locality of the positive even lattice VOA and identifies its associated net with the Dong–Xu lattice net. CKLW [C, Theorem 6.9] transfers its unitary automorphisms as the same operators on the Hilbert completion. Thus the actual $E$ and $Q_{16}$ actions remain faithful and agree on the specified common $Q_8$. Canonical sign lifts preserve the natural lattice unitary structure: their phases are real of modulus one, and their action on the Heisenberg space is orthogonal.

In applying Dong–Xu [D, §4], take its finite signed action $\Gamma$ to be this actual prescribed action ($E$ or $Q_{16}$), with the same lattice cocycle $\epsilon$ and $\eta_\sigma(\alpha)^{-1}=c_\sigma(\alpha)$, where $c_\sigma$ is the phase of the actual lift. The lift cocycle identity $\epsilon(\alpha,\beta)c_\sigma(\alpha+\beta)=c_\sigma(\alpha)c_\sigma(\beta)\epsilon(\alpha\sigma,\beta\sigma)$, together with orthogonality and the actual group relations, verifies the required simultaneous signed loop-group action. Hence [D, Definition 4.24 and Proposition 4.25] constructs solitons and their covariance for these same lifts, including their agreement on the prescribed common $Q_8$.

Dong–Xu [D, Corollary 3.19] gives
\[
\mu(\mathcal A_L)=|L^*/L|=1.
\]
The lattice net is therefore completely rational and holomorphic. Its finite group actions are proper, so [D, Theorem 2.4] makes $\mathcal A_L^E$ completely rational. Moreover, [C, Proposition 7.6] identifies its vacuum net with that of $(V_L)^E$. In particular, input 4 applies to the fixed net's actual vacuum Hilbert space and Virasoro action.

The remaining task is to compute the relevant energies for the net's own twisted solitons. We do so using bounded current Weyl operators and the local diffeomorphism unitaries already present in the vacuum net.

## C. Canonical Möbius implementation from common local unitaries

We will use the following consequence of D’Antoni–Fredenhagen–Köster [F, Proposition 2, Lemmas 3–4 and Theorem 5].

Suppose a conformal subnet $\mathcal C\subset\mathcal D$ contains the local vacuum diffeomorphism unitaries of $\mathcal D$, and let $\pi$ be a locally normal circle representation. Then the canonical globally inner Möbius implementation for $\pi(\mathcal D)$ is the canonical one for its restriction to $\mathcal C$.

Indeed, the construction in [F] first forms products of represented localized diffeomorphism unitaries. Their multiplication defects are central in the generated von Neumann algebra; the construction corrects them using functional calculus in that central algebra. Since the starting unitaries lie in $\pi(\mathcal C)''$, their products and corrections lie there as well. The resulting implementation for $\mathcal D$ is therefore globally inner for $\mathcal C$ and implements its Möbius action. The uniqueness in [F, Theorem 5] identifies the two.

This argument uses the **same local unitaries**, not just covariance on the smaller algebra. In a tensor product it gives exact additivity of the canonical generators. Under an exact normal intertwiner of local current algebras, it transfers their canonical action as well. Applying the construction to the whole represented algebra also fixes its action on charge sums and multiplicity spaces; arbitrary independent rotation shifts on those spaces are not available.

There is a related useful criterion. If a covariant representation has finite-dimensional commutant, a given honest universal-cover Möbius implementation agrees with the canonical globally inner one. Their ratio lies in the commutant; because the canonical implementation is globally inner, the ratio is an ordinary continuous unitary representation there. Such a representation of the connected group $\widetilde{\operatorname{PSL}}(2,\mathbb R)$ in a finite-dimensional unitary algebra is trivial: its Lie algebra has no nonzero homomorphism from $\mathfrak{sl}_2(\mathbb R)$ into a compact unitary Lie algebra.

## D. Geometric current sectors and negative cycles

Write $\mathcal J_r$ for the vacuum rank-$r$ current net. The rank-one current net is split; for example its vacuum trace $\prod_{k\ge1}(1-q^k)^{-1}$ is finite for $0<q<1$ [C, §3.3]. Apply the geometric permutation construction of Longo–Xu [X, §6, equation (33), Theorem 6.3]. On the vacuum $n$-cover, its rotation generator is
\[
H_n=\frac{L_0^{\mathrm{cover}}}{n}+\frac{n^2-1}{24n}.
\tag{1}
\]
This is the actual covariance implementation from [X, §2, equation (14), and Theorem 6.3(b,e)]. No rationality or finite $\mu$-index of the current net is used for this formula. Theorem 6.3(d) supplies a finite sum of irreducible constituents on the cyclic fixed net, so the finite-commutant criterion in §C identifies (1) with its canonical implementation.

For completeness, the local Weyl map makes a signed-cycle factor visible without a twisted stress-tensor calculation. Choose inverse branches
\[
h_j(e^{i\theta})=e^{i(\theta+2\pi j)/n},\qquad 0\le j<n,
\]
over a base interval $I$ avoiding a cut. For scalar test functions $F_j$ supported in $I$, the geometric representation is
\[
\Pi_n\left(\bigotimes_j W(F_j)\right)
=W\left(\sum_j F_j\circ h_j^{-1}\right).
\tag{2}
\]
Each pullback is extended by zero outside its branch interval. The branch supports are disjoint, so cross symplectic pairings vanish. These are current test-function pullbacks, with no Jacobian factor.

Set $n=2s$ and make the constant orthogonal change of the base currents
\[
J_j^\pm=\frac{J_j\pm J_{j+s}}{\sqrt2},\qquad 0\le j<s.
\tag{3}
\]
The monodromy becomes a positive $s$-cycle $P_s$ on the plus currents and a negative $s$-cycle $N_s$ on the minus currents. In (2), the resulting cover functions satisfy
\[
G_+(\theta+\pi)=G_+(\theta),\qquad
G_-(\theta+\pi)=-G_-(\theta).
\]
They occupy respectively the even and odd Fourier modes. Their subspaces are orthogonal for the complex positive-frequency inner product
\[
\langle F,G\rangle_1=\sum_{k>0}k\,\overline{F_k}G_k.
\tag{4}
\]
Thus the pulled-back Gaussian vacuum factors, and second quantization gives a tensor factorization of the full local Weyl representation into even and odd Fock spaces.

The plus factor is exactly the ordinary $s$-cycle vacuum representation: the map from its unfolded scalar function to the $2s$-cover is
\[
G(\theta)\longmapsto \frac{G(2\theta)}{\sqrt2},\qquad
\sum_{k>0}2k\left|\frac{G_k}{\sqrt2}\right|^2
=\sum_{k>0}k|G_k|^2.
\tag{5}
\]
It is a complex one-particle isometry preserving the zero-charge vacuum.

Moving the cut changes branch order by $P_s\oplus N_s$. Hence both factors glue on their own circle fixed nets
\[
\mathcal C_+=\mathcal J_s^{\langle P_s\rangle},\qquad
\mathcal C_-=\mathcal J_s^{\langle N_s\rangle}.
\]
Their product $\mathcal C=\mathcal C_+\otimes\mathcal C_-$ is a subnet of
$\mathcal D=(\mathcal J_s\otimes\mathcal J_s)^{\langle P_s\oplus N_s\rangle}$.

The orthogonal current change (3) preserves the vacuum stress tensor. For a localized diffeomorphism, the vacuum local unitary of $\mathcal D$ is the product of the plus and minus vacuum local unitaries, both already in $\mathcal C$. This vacuum identity follows equally from current second quantization or the vacuum-current and tensor results [C, Example 8.6 and Corollary 8.2]. Apply the normal local representation to that bounded identity and then §C. Its canonical implementation is exactly $U_+\otimes U_-$.

Now $L_0^{\mathrm{cover}}=L_0^{\mathrm{even}}+L_0^{\mathrm{odd}}$, while (5) identifies $L_0^{\mathrm{even}}$ with twice the plus cover generator. Using (1) for $2s$ and for $s$ therefore gives
\[
\begin{aligned}
H^-_s
&=\frac{L_0^{\mathrm{odd}}}{2s}
  +\frac{4s^2-1}{48s}-\frac{s^2-1}{24s}\\
&=\frac1{2s}\sum_{\substack{k>0\\ k\ \mathrm{odd}}}kN_k
  +\frac{2s^2+1}{48s}.
\end{aligned}
\tag{6}
\]
This is an identity of generators of the identified one-parameter groups. In particular, it is not a subtraction of unrelated self-adjoint operators or independently phased rotations. The odd-mode vacuum attains the positive minimum
\[
h^-_s=\frac{2s^2+1}{48s};
\qquad h^-_1=\frac1{16},\quad h^-_2=\frac3{32},\quad
h^-_4=\frac{11}{64}.
\tag{7}
\]

## E. Matching the actual Dong–Xu soliton

Let $\sigma$ be one of the prescribed standard lattice isometries, of actual order $N$, and put
\[
P_0=\frac1N\sum_{j=0}^{N-1}\sigma^j,\qquad
E_0=P_0(\mathbb RL).
\]
The representation used here is the locally normal soliton constructed by Dong–Xu [D, Definitions 4.22 and 4.24, Lemma 4.23 and Proposition 4.25].

### E.1 The local current operator and its normalization

Use $t\in\mathbb R/\mathbb Z$. For a smooth real vector test function $f$ supported away from the cut, define
\[
\widehat f(t)=\sigma^j f(Nt-j),
\qquad j/N\le t\le(j+1)/N.
\tag{8}
\]
It is smooth, obeys $\widehat f(t+1/N)=\sigma\widehat f(t)$, and has mean $P_0f_0$, where $f_0=\int_0^1 f(t)\,dt$. The cover inner product in [D, Definitions 4.5 and 4.7] is $1/N$ times the lattice inner product. Indeed,
\[
\frac1N\int_0^1\langle\widehat f'(t),\widehat g(t)\rangle\,dt
=\int_0^1\langle f'(u),g(u)\rangle\,du.
\tag{9}
\]
This follows by changing variables in each tile of (8); each tile contributes the same base integral before the prefactor $1/N$.

The local current loop has zero winding. Thus the lattice translation $U_{\Delta f}$ and winding phase in [D, Definition 4.22] are absent. On a momentum fiber $p$, its actual bounded operator is
\[
\pi_\sigma(W(f))\big|_p
=e^{2\pi i\langle p,P_0f_0\rangle}
  W_\sigma(\widehat f-P_0f_0)\otimes 1_{D_\sigma},
\tag{10}
\]
where $W_\sigma$ is the positive-frequency Fock Weyl representation and $D_\sigma$ is the finite defect space in that construction.

Dong–Xu [D, Remark 4.20] uses a lattice $U_\alpha$ commutator conjugate to the convention in Bakalov–Kac. Formula (10) contains no such lattice operator. The current Weyl representation and the cover normalization are matched directly. Reversing the sign convention for a momentum character merely relabels $p$ by $-p$ in the support determined next.

### E.2 An occupied zero-momentum fiber

For the standard lift the fixed-torus period is visible directly in the bounded construction. If $\alpha\in L^\sigma=L\cap E_0$, the constant representative $f(t)=\alpha$ is the identity torus loop [D, §3]. In Definition 4.22 it has zero winding, constant equivariant cover $\alpha$, and no mean-zero Weyl or winding factor. Lemma 4.23 therefore gives $T(\alpha)=1$ for its fixed-torus operator. This is also the fixed-torus period relation [K, equation (4.47)], obtained from (4.46) using $\sigma\alpha=\alpha$, $b_\alpha=0$, and the standard-lift normalization $\eta_\sigma(\alpha)=1$ in (4.18)–(4.20). Thus every occurring momentum belongs to $(L^\sigma)^*$. No scalar for a moving image-lattice operator is used in this step.

Unimodularity gives
\[
(L^\sigma)^*=P_0L.
\tag{11}
\]
To see the nontrivial inclusion, $L^\sigma$ is primitive in $L$: an integral multiple of a lattice vector can be fixed only if the vector is fixed. An integer functional on this primitive subgroup extends to $L$. By unimodularity it is pairing with some $\alpha\in L$, and on fixed vectors that pairing is also pairing with $P_0\alpha$. The reverse inclusion is immediate.

The pure group operator $U_\alpha$ in [D, Definition 4.19], unlike the full winding-loop image in Definition 4.22, commutes with the nonzero Heisenberg oscillators and therefore preserves the oscillator-vacuum subspace. Its torus commutation relation translates an oscillator-vacuum momentum fiber by $-P_0\alpha$; the opposite sign is the convention in [K, Lemma 4.7; see also (4.49) and (4.54)–(4.55)]. These operators are invertible, so every occupied oscillator-vacuum fiber is translated by all of $P_0L$. Since any starting momentum already lies in $P_0L$, its orbit is all of $P_0L$ and contains zero. Thus the zero-momentum oscillator-vacuum fiber is **occupied**, not merely an abstractly allowed charge. This uses the displayed torus commutator, not an unidentified scalar on the moving-lattice defect quotient.

The current restriction of the actual soliton is consequently
\[
\mathcal H_\sigma\big|_{\mathrm{currents}}
\cong\bigoplus_{p\in P_0L}\mathcal F_{\sigma,p}\otimes D_\sigma.
\tag{12}
\]
The finite defect multiplicity is constant across the fibers and has trivial current action. These are the Heisenberg and group-representation facts in [K, equation (4.55), Lemma 4.7, Theorem 4.2 and Remark 4.4] used by [D, §4]. No integration theorem for arbitrary twisted VOA fields is needed. Standardness and unimodularity are both material: without them an occupied coset can be shifted away from zero.

### E.3 The exact signed-cycle isometry

For a negative cycle on $\mathbb R^s$, choose
\[
\tau(x_0,\ldots,x_{s-1})=(x_1,\ldots,x_{s-1},-x_0).
\]
Here $N=2s$. Define
\[
K_-\widehat f=\frac{(\widehat f)_0}{\sqrt2},
\tag{13}
\]
where the subscript means the zeroth coordinate, not the mean. This scalar cover function changes sign under $t\mapsto t+1/2$. On the first $s$ branches it equals $f_j(2st-j)/\sqrt2$, and on the opposite branches it is the negative of the corresponding function. It is therefore exactly the odd unfolded function in (2)–(3).

Every component of $\widehat f$ is a translate, with the prescribed signs, of its zeroth coordinate. Translation preserves the Fourier inner products, and hence
\[
\begin{aligned}
\frac1{2s}\sum_{\ell>0}\ell
  \langle\widehat f_\ell,\widehat g_\ell\rangle
&=\frac12\sum_{\ell>0}\ell\,
  \overline{((\widehat f)_0)_\ell}((\widehat g)_0)_\ell\\
&=\sum_{\ell>0}\ell\,
  \overline{(K_-\widehat f)_\ell}(K_-\widehat g)_\ell.
\end{aligned}
\tag{14}
\]
Conversely, every odd scalar function reconstructs the equivariant vector function from its translates. Thus (13) extends to an onto complex positive-frequency one-particle isometry. Its second quantization intertwines the **bounded local Weyl operators** (10) with the geometric negative-factor operators in §D.

On a fixed direction the cover function is $f(Nt)$. Its Fourier indices are multiples of $N$, so the factor $1/N$ in its one-particle norm cancels those multiples and gives the ordinary current norm. Its constant character in (10) is the ordinary charge-$p$ character.

A constant orthogonal change of all real current coordinates preserves support, the Weyl form, the positive-frequency inner product and the vacuum stress. It need not preserve the lattice. After putting $\sigma$ into the required signed-cycle form, (12) becomes, on each joint charge fiber,
\[
\mathcal F_{\sigma,p}
\cong\mathcal F_p^{\mathrm{fixed}}
       \otimes\bigotimes_{\text{negative blocks}}\mathcal F_s^-.
\tag{15}
\]
The joint momentum set remains $P_0L$; no product decomposition of that lattice is asserted.

### E.4 Absolute stress normalization

The ordinary charged current representation and its integrated diffeomorphism action are given in [D, Lemma 3.5 and the paragraph before Proposition 3.6]. On the ordinary finite-particle core, writing $J_n^{(0)}$ for zero-charge modes with $J_0^{(0)}=0$, while $J_0^{(p)}=p$, one has
\[
L_n^{(p)}
=L_n^{(0)}+p\cdot J_n^{(0)}
  +\frac{\|p\|^2}{2}\delta_{n,0}.
\tag{16}
\]
In particular its generator is
\[
H_p^{\mathrm{fixed}}=\frac{\|p\|^2}{2}
       +\sum_{n>0}nN_n^{\mathrm{fixed}}.
\tag{17}
\]
The ordinary current relations give the coefficient in (16); identification with the represented net action uses [D, Proposition 3.9 and its proof], which places local vacuum diffeomorphism unitaries in the current algebra and compares their charged action. It is not inferred from a formal bracket calculation alone.

The intertwiners in (14)–(15), by local normality, intertwine the whole local current algebra and hence these existing bounded local diffeomorphism unitaries. The defect factor is the identity on them. Apply §C to those represented operators on the whole sum (12). This identifies its canonical generator with the direct sum of (17) plus the negative generators (6), tensored with the identity on $D_\sigma$. It excludes an additional Hamiltonian on the defect multiplicity or an independently chosen phase on any charge fiber.

The full current net is a subnet of the **parent** lattice net. It is not asserted to be a subnet of $\mathcal A_L^E$. The circle comparison for each $\sigma$ is between the cyclic current fixed net and $\mathcal A_L^{\langle\sigma\rangle}$ through their common Virasoro subnet and the same local diffeomorphism unitaries. For $\sigma\in E$, further restriction to $\mathcal A_L^E$ preserves that canonical action. The auxiliary order-eight element need not belong to $E$; its soliton is used only on $\mathcal A_L^{\langle g\rangle}$ for the cyclic anomaly test.

## F. The attained energies

Inputs 1–2 and real orthogonal spectral decomposition give the required signed-cycle forms. The zero-momentum fiber exists by (11)–(12), and all oscillator energies in (6) and (17) are nonnegative. Therefore the following minima are attained on the full solitons:

| Prescribed action | Real current blocks | Absolute ground energy |
|---|---|---:|
| Noncentral involution of $E$ | $64$ fixed directions, $64$ negative one-cycles | $4$ |
| $z=-I$ | $128$ negative one-cycles | $8$ |
| Order four in $E$, square $z$ | $64$ negative two-cycles | $6$ |
| Specified order-eight element $g$ | $32$ negative four-cycles | $11/2$ |

Every nontrivial $E$ soliton has energy at least four. Restriction to any constituent preserves the lower bound; a chosen constituent need not contain its full soliton's ground space.

## G. The intrinsic net anomaly and local extension

For an order-$n$ cyclic action on a holomorphic net, write $q\in\mathbb Z/n$ for its intrinsic anomaly parameter. The generator-flux spin formula [E, §2.2, equations (2.13)–(2.14)] is
\[
h_\ell\equiv \frac q{n^2}+\frac\ell n\pmod1.
\tag{18}
\]
Thus the cyclic anomaly vanishes if and only if one generator-flux constituent has $\theta^n=1$. Here $\theta=e^{2\pi i h}$ is the twist, after removing the common $e^{-2\pi i c/24}$ scalar in modular $T$.

The cyclic decomposition reduces the canonical Hamiltonian. An attained ground vector of the full soliton has a nonzero component in at least one constituent at the same energy. Its precise charge label is immaterial for (18). For involutions the table gives $2\rho=8$ or $16$; for the auxiliary order-eight element it gives $8\rho=44$. These are integers. In the latter case the spin is $-1$, but its eighth power is one.

The net anomaly therefore vanishes on every involution subgroup and on $C_8\subset Q_{16}$. Its restriction is natural: a subgroup uses the same twisted-sector representatives and multiplication intertwiners defining the associator class [B, §1; E, §3.2]. With $H^3(G,U(1))\cong H^4(G,\mathbb Z)$ for finite $G$, input 3 applies to this net class. The equal restriction kernels in $Q_{16}$ give zero on the actual common $Q_8$, without requiring the entire $Q_{16}$ anomaly to vanish. The extraspecial detector then gives zero for the actual $E$ action.

The local extension theorem [E, Corollary 2, equation (3.5), and §3.2] now gives the holomorphic extension associated to $K=E$ and trivial discrete torsion, after choosing an anomaly trivialization. Its vacuum branching over $\mathcal A_L^E$ is
\[
\mathcal H_{\mathcal B}\big|_{\mathcal A_L^E}
\cong\bigoplus_{[h]\subset E}\mathcal H_{[h,1]}.
\tag{19}
\]
The identity-flux term is exactly the fixed net's vacuum representation. Each other term is contained in a nontrivial soliton and has no energy below four by §F. The inclusion is conformal and retains the same Virasoro action.

Input 4 therefore implies that $\mathcal B$ has only Virasoro vacuum descendants below four, while its nonzero invariant weight-four primary remains primary. Its primary gap is exactly four, and its central charge is $128$.

The construction has tested the net anomaly directly and built a local extension in the net category. It does not identify $\mathcal B$ with the net of a particular full-orbifold VOA, integrate every twisted VOA field, establish a general VOA/net equivalence, or determine centralizer ground characters and light-state multiplicities.

## References

- **[KRR]** C. A. Keller, A. W. Roberts and J. Roberts, *CFTs with Large Gap from Barnes-Wall Lattice Orbifolds*, [arXiv:2411.13646v2](https://arxiv.org/pdf/2411.13646v2). Lattice normalization and prescribed finite action; inputs 1–4 refer to their specified realization as treated in the pinned main argument.
- **[G]** B. Gui, *Unbounded field operators in categorical extensions of conformal nets*, [arXiv:2001.03095v5](https://arxiv.org/pdf/2001.03095v5), Theorems 3.46 and 3.48.
- **[C]** S. Carpi, Y. Kawahigashi, R. Longo and M. Weiner, *From vertex operator algebras to conformal nets and back*, [arXiv:1503.01260v4](https://arxiv.org/pdf/1503.01260v4), §3.3, Theorem 6.9, Proposition 7.6, Corollary 8.2 and Example 8.6.
- **[D]** C. Dong and F. Xu, *Conformal Nets Associated With Lattices And Their Orbifolds*, [arXiv:math/0411499v2](https://arxiv.org/pdf/math/0411499v2), Theorem 2.4; Lemma 3.5, Propositions 3.6 and 3.9, Corollary 3.19; §4 opening; Definitions 4.5, 4.7, 4.19, 4.22 and 4.24, Remark 4.20, Lemma 4.23 and Proposition 4.25.
- **[X]** R. Longo and F. Xu, *Topological Sectors and a Dichotomy in Conformal Field Theory*, [arXiv:math/0309366v3](https://arxiv.org/pdf/math/0309366v3), §2 equations (13)–(15), §6 equation (33) and Theorem 6.3, and the current-net example in §7.3.1.
- **[F]** C. D’Antoni, K. Fredenhagen and S. Köster, *Implementation of conformal covariance by diffeomorphism symmetry*, [arXiv:math-ph/0312017v1](https://arxiv.org/pdf/math-ph/0312017v1), Proposition 2, Lemmas 3–4 and Theorem 5.
- **[K]** B. Bakalov and V. G. Kac, *Twisted Modules over Lattice Vertex Algebras*, [arXiv:math/0402315v3](https://arxiv.org/pdf/math/0402315v3), equations (4.18)–(4.20), (4.46)–(4.49) and (4.54)–(4.55), Lemma 4.7, Theorem 4.2 and Remark 4.4. Only representation and momentum facts, not a twisted energy formula, are used.
- **[E]** D. E. Evans and T. Gannon, *Reconstruction and Local Extensions for Twisted Group Doubles, and Permutation Orbifolds*, [arXiv:1804.11145v1](https://arxiv.org/pdf/1804.11145v1), §2.2 equations (2.13)–(2.14), Corollary 2 equation (3.5), and §3.2.
- **[B]** M. Bischoff, *A remark about the anomalies of cyclic holomorphic permutation orbifolds*, [arXiv:1812.11910v1](https://arxiv.org/pdf/1812.11910v1), §1, for the intrinsic anomaly defined by twisted sectors.
