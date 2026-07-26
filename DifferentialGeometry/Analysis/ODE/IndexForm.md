# IndexForm.lean

## 2026-07-19 created (option-1 lane, N-d half 1, foundational file)

The abstract index form of the Jacobi ODE `y'' + R(t)y = 0` over a real
inner-product space — manifold-free, fields carried as `(y, v)` pairs (same
currency as `SecondOrderLinearExistence.lean`).  All green, BUILD-verified,
no `sorry`:

- `IsJacobiSolOn` (structure; one-sided `Icc`-derivatives) + continuity
  projections.
- `indexIntegrand` / `indexForm` (+ `_def`, `_symm` under self-adjoint `R`,
  continuity, interval integrability, `indexForm_add_adjacent`,
  `indexForm_same`).
- `IsJacobiSolOn.hasDerivAt_inner` — the FTC pivot: for a Jacobi pair the
  integrand is literally `d/dt ⟪v, z⟫`.
- `IsJacobiSolOn.indexForm_eq_sub` — integration by parts = boundary term.
- `IsJacobiSolOn.indexForm_self_zero` — Jacobi field vanishing at both ends
  is a null direction.
- `indexIntegrand_add_smul` / `indexForm_add_smul` — quadratic expansion.
- `exists_indexForm_neg` — the negativity engine (null direction + nonzero
  cross term ⟹ strictly negative value; no positivity of the form needed).

Route reference: frenzymath `Ch01/IndexForm.lean` (statement shapes; proofs
re-derived).  Import note: FTC lives at
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` in this pin.

**CRITICAL ELABORATION LESSON (extends the false-green rule):** `lake env
lean` does NOT apply the lakefile's `leanOptions` — in particular
`autoImplicit` stays ON under a focused check but is OFF under `lake build`.
This file initially passed the focused check with three theorems whose `{R}`
binder was missing (auto-bound silently), then failed the build with
`Unknown identifier R`.  Always put `set_option autoImplicit false` at the
top of new files and treat a focused check as NOT verifying binder hygiene.

## Remaining half-1 chain (next bricks, per the reference and the
agreement-gate survey `Geometry/Exponential/AGREEMENT_GATE_REFERENCE.md`)

1. Interior-point uniqueness for `IsJacobiSolOn` (both directions from an
   interior time; time-reversal + shift of the Grönwall closer
   `ode2_pi_zero`) — needed for `v t₀ ≠ 0` at a conjugate time.
2. The truncated-field construction + nonzero cross term
   (reference `IndexFormConjugate.lean`, 164 lines).
3. Corner smoothing to a SMOOTH perpendicular negative-index witness
   (reference `IndexFormNegativeSmooth.lean`, 508 lines) — the one genuinely
   hard remaining brick of N-d.
4. Collision with the IN-TREE half 2 `indexForm_nonneg_of_minimising_geodesic`
   (`Variation/SecondVariationMinimiser.lean:535`) — needs a bridge between
   that file's geometric index form and this abstract one (frame reduction:
   `parInner_*`, `exists_intrFrame`, `gON_expand`).  The reference's six-file
   broken-variation cluster does NOT need porting.
