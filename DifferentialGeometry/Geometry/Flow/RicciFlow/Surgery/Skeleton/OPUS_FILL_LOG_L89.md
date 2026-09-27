# Lane L89 (DESIGN_C3B bricks 0, L8, L9) — 2026-09-26

File: `Surgery/Topology/CapWindowDerivativeTransfer.lean` (285 lines). Not wired into the root
aggregate, no git writes, no `lake build`.

## Failures first

- Brick 0 cannot be a wrapper over D2's statement. D2 states `∀ Θ C, ∃ Cbirth c C', …`. From the
  statement alone `C'` may depend on `C`, and `C` ranges over all of `ℝ≥0`, so no instantiation
  gives a `C'` that is uniform in `C`. Monotonicity in `C` does not help either, because no single
  `C₀` dominates every `C`. The swapped theorem is therefore proved in this file by re-running D2's
  proof with the bridge call moved after `∀ C`. It is a ~100-line near-copy of D2's body.
  **Lead action:** D2's headline is now a corollary of the swapped one. Deleting it or restating it
  as a corollary would remove the duplication, but that is D2's file, and this lane was not allowed
  to edit it.
- L8 as briefed ("witness on the slab flow at (y,t)") is a direct application of
  `exists_windowedModelWitness_scalar_derivative_bounds` on `G.flow`. I did not write DESIGN_C3B's
  alternative, the S→Gk scaling transfer of `∂ₜR`. The design's step 4 already moves the whole
  witness to `Gk` exactly, so the scaling transfer is redundant.

## Declarations (compiled; axioms propext/Classical.choice/Quot.sound; `#lint` 14 linters clean)

- `DifferentialGeometry.PDE.RicciFlow.exists_standard_time_le_of_close_scalar_mul_lt` (L9):
  `∃ c₀ > 0, ∀ τ ≥ 0, ∀ Q x T R, 0 ≤ T → T < 1 → |R − R_Q(x,T)| < 1 → T*R < τ →
  T ≤ (τ+1)/(τ+1+c₀)`. Here `c₀` is from `exists_standard_scalar_lower_bound`.
- `…Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_scalar_derivative_bounds_of_windowedModelWitness`
  (L8): `∃ Cw > 0, ∀ G : P.IncomingSlab a s, WindowedModelWitness eps kappa G.flow y t →
  eps ≤ 1/4 → Ioo (t − (eps R)⁻¹) t ⊆ Ioo a s → ∀ Ctime Cgrad : ℝ≥0, Cw ≤ Ctime →
  2Cw ≤ Cgrad →` the leaf's two clauses, in their exact shape.
- `…RetainedCoreHistory.exists_uniform_derivative_gradient_bounds_of_cap_window_trace` (brick 0):
  `∀ Θ, 0 < Θ → Θ < 1 → ∃ c C', 0 < c ∧ 0 < C' ∧ ∀ C : ℝ≥0, ∃ Cbirth, 0 < Cbirth ∧ ∀ D, …`.
  The rest is D2's statement verbatim.
- `…RetainedCoreHistory.exists_cap_window_scalar_derivative_gradient_constants` (L8+L9 combined, for
  brick 11):
  ```
  (τQ : ℝ) (hτQ : 0 ≤ τQ) :
  ∃ (Θ₂ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 0 < Θ₂ ∧ Θ₂ < 1 ∧
  (∀ Q x T R, 0 ≤ T → T < 1 → |R − R_Q(x,T)| < 1 → T * R < τQ → T ≤ Θ₂) ∧       -- case B trigger
  (∀ G …, WindowedModelWitness eps kappa G.flow y t → eps ≤ 1/4 → Ioo … ⊆ Ioo a s →
     ∀ Ctime Cgrad, Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad → clauses) ∧                     -- case A
  ∀ C : ℝ≥0, ∃ Cbirth > 0, ∀ D > 0, ∃ R m₀ ζ₀ δ₀ …, ∀ H p₀ … records …, (D2 hypotheses with
     θcap := Θ₂, i.e. t − time j.succ ≤ Θ₂ * scale⁻¹) →
     ∀ Ctime Cgrad, Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad → clauses                         -- case B
  ```
  The constants are `Θ₂ = (τQ+1)/(τQ+1+c₀)`, `Ctime₀ = max Cw C'(Θ₂)` and
  `Cgrad₀ = max (2Cw) C'(Θ₂)`. They depend on `τQ` only.
  How brick 11 splits the cases on the normalized age:
  - Case A, `τQ ≤ R(t − time j.succ)`: use the second conjunct with the witness transported to `Gk`.
  - Case B, `R(t − time j.succ) < τQ`: this equals `T·R_S(z,T)` with `T = q(t − time j.succ)`.
    The first conjunct needs `|R_S − R_Q| < 1`, which comes from the bridge closeness at `Θ` (chosen
    after θcap). It gives `T ≤ Θ₂`, and then the third conjunct applies.

## Compile

`LEAN_NUM_THREADS=2 lake env lean <file>` gives no output. The scratch copy with `#print axioms` and
`#lint` was deleted after the check.
