# ConnLapPairing

## Role

This is the canonical non-DeTurck home for generic `L²` pairing and
covariant-gradient identities for `1 - Δ∇` and its smooth iterates.
`DeTurckPrincipalArmEnergyPairing` imports this module instead of owning those
general results privately.

## Relocated API

- The seven existing one-step and iterate pairing theorems retain their public
  names and statements, so downstream consumers do not need compatibility
  wrappers.
- Their proofs reuse the existing
  `rawTensorConnLapSmooth_l2Inner_selfAdjoint`; the DeTurck-local duplicate raw
  theorem remains untouched because later code in that file still owns it.
- The subtraction proof plumbing uses pointwise additive homomorphisms followed
  by scalar `integral_sub`. This avoids whole-function scalar multiplication on
  reducible tensor Hom models, which timed out during instance synthesis in the
  smaller producer module.

## Covariant-gradient chain

The formerly private DeTurck ladder has also moved here as genuine generic
machinery:

- `rawConnLap_add`
- `oneMinusConn_add`
- `connLapIter_map_add`
- `covGrad_oneMinus`
- `connLapIter_one`
- `covGrad_iterL`

The final theorem expands one covariant gradient of an iterate into the
iterated gradient plus the finite sum of curvature commutators. All new names
are at most twenty characters. The old DeTurck private declarations were
removed, and its two live consumers now use `covGrad_iterL` directly.

## Verification

The initial pairing-only producer passed focused verification without local
warnings. After adding the covariant-gradient chain, re-verification was
temporarily blocked before reaching this source by a missing upstream
`LeviCivita.Basic` object file while the shared workspace dependency refresh was
in progress. This is a stale-artifact/tooling blocker; rerun the producer check
after that narrow refresh, then refresh this module once before checking the
DeTurck consumer.
