# Canonical lifts on arbitrary small supports

`KRRSupport.lean` generalizes the fixed modulo-16 partition to any set
`s : Finset (Fin 7)` of numerical bit positions. Its block label is
`support i \ s.image Fin.val`, so equality of labels fixes every bit outside s
in the existing ordered coordinate basis.

Equal labels put the symmetric difference of two supports inside s. For
`s.card ≤ 3`, the resulting cardinality bound makes the concrete Gram exponent
at least two. Thus both G and the prescribed half-Gram matrix H have entries
divisible by four within each block. `H_even_of_same_block` exports the evenness
needed by the generic phase-composition theorem. No coordinate permutation,
basis reordering, new half-form or new cocycle transport is introduced.

`X_supported` and `Z_supported` prove that the literal integral Pauli matrices
preserve the partition whenever their active bit belongs to s. These two
statements do not require the cardinality bound. They use the actual support
toggle and integral rows already defined in `KRRPauli`.

`KRRSupportedLift.lean` supplies two direct specializations of `CanonicalLift`:
composition on all lattice-VOA states and composition in the conformal
automorphism group. Their explicit premises are a common set s with at most
three positions, preservation of its blocks, and preservation of G. Both use
the same identity coordinates, ordered H and global cocycle transport as
`KRRCanonical`. With row vectors and ordinary automorphism composition, their
order is `lift (R * T) = lift T * lift R`.

## Verification provenance

The original support source, SHA256
`615dc3b48d1287250d0bcb6587a723a008ba67abc2b7110dbe4ba13c155dccb9`,
compiled unchanged at the repository's pinned Lean and Mathlib versions in
2.47 seconds, with an empty diagnostic log. A separate 2.22-second run printed
the exact types and transitive axioms of `H_even_of_same_block`, `X_supported`
and `Z_supported`. All three used only `propext`, `Classical.choice` and
`Quot.sound`. The axiom log has SHA256
`028a2eb49cd6bfdbd5481f4f499cdb6bc3cdd08c0fdad010414ab6ea8be5f4f0`.

The integration copy updates only the status comment and license pointer;
imports and proof body are unchanged. Its SHA256 is
`a47d447d130bb4397a55b908809f1ba4c16cb3a842b666c31baad23ce4e06e63`.
The wrapper received independent internal source and API review and was
subsequently compiled with the complete VOA dependency closure in public CI.
Its integration SHA256 is
`2b87ddb52a607fbe93ecad0a4b008e24eba99ef384dc53d731fa231705700cfe`.
Both integration sources and all five declaration reports passed in
[run 45864728408](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45864728408)
at commit c8030261ec42a8d9554b8a831c40c01894091303. The complete eighteen-module
run had no local warnings or errors; all 172 local reports used only the
standard three axioms and all source/probe hashes matched that public commit.

## Scope

These lemmas allow different small-support arguments to use one fixed
canonical lift. They do not provide a common set of at most three positions
for all seven Pauli positions. They neither prove global multiplicativity of
the canonical section nor construct the full extraspecial-group action.
Concrete normalizer gates, a presentation and its correspondence with the
prescribed group, and downstream anomaly arguments remain separate work.
