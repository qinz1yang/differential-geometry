# Time-dependent tame forcing-space fixed point

## State — 2026-07-19

`TimeTameFixedPoint.lean` implements the non-autonomous analogue of
`partial_sol_tame`.  Its nonlinearity has the form

```text
N : ℝ → lowerStateRS g₀ r s a R → tensorHs g₀ r s a.
```

The theorem `time_partial_tame` assumes compositional measurability through
`TimeNemyMeas`, a uniform zero bound, and the same critical three-arm estimate
uniformly on `Icc 0 τ`.  It chooses one horizon

```text
min τ (min 1 (min (1 / (64 * (B + 1)^2))
  (((R / 4) / (2 * (D + 1)))^2)))
```

and returns the same Duhamel solution, almost-everywhere state membership,
forcing identity, zero trace, strong PDE identity, and forcing-radius fields
as the autonomous theorem.  The forcing identity is genuinely
time-dependent:

```text
gforce(t) = N(t, aeSetLift field t)  a.e.
```

## Tensor variance and HMF use

The existing `lowerState` wrapper was hard-coded to symmetric `(0,2)`
tensors, although the underlying maximal-regularity and Duhamel estimates are
generic in tensor variance.  This file therefore adds:

- `lowerStateRS`;
- `zero_mem_lowerRS`;
- `field_mem_lowerRS`.

The fixed-point theorem is generic in `r,s`; a vector-field harmonic-map-flow
coordinate equation can use `(r,s) = (1,0)`.  No tension-field or harmonic-map
heat-flow existence theorem is claimed here, because the repository does not
yet provide the geometric tension-field producer needed to instantiate `N`.

## Verification and honest accounting

This lane was required to remain source-only while another named Lean build
was active.  Static checks cover tensor-variance threading, the time-window
restriction, absence of autonomous `Nfun` residues, file size, and forbidden
placeholders.  No focused Lean elaboration was run in this lane.

- Exact checked theorem `time_partial_tame`: 0% until focused verification.
- Abstract source implementation: complete pending elaboration.
- Harmonic-map heat-flow existence: 0%.
- `ricci_flow_forward_unique`: 0%.

No `sorry`, `admit`, axiom, opaque replacement, foundational instance, or new
notation is introduced.

## 2026-07-25 REAL BUILD VERDICT: FAILED (B-lane planner verification)

First authoritative `lake build` of this module: elaboration FAILS. The
(r,s)-generalization claim above ("the underlying maximal-regularity and
Duhamel estimates are generic in tensor variance") is FALSE for at least two
consumed upstream lemmas, which are hard-coded to `(0,2)`:

- `:428` — `timeL2Inclusion_maxRegDuhamelSolField` (at
  `Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:155`)
  expects `timeL2 (tensorHs g₀ 0 2 a) T`; applied here at generic `r s`.
- `:644` — `maxRegDuhamelSolField_zero_zero` (same file `:237`), same mismatch.

Repair options (planner ruling: PARKED pending the forward-uniqueness route
decision, since this engine is only on the Route-G/HMF critical path):
(a) generalize the two (plus any further) upstream lemmas to (r,s) in place —
touches the (N)-lane engine file, coordinate first; (b) state (r,s)-generic
variants in a new TensorMaximalRegularity file (same proofs, no upstream edit).
Verified-progress accounting: `time_partial_tame` remains 0%; do not consume.
