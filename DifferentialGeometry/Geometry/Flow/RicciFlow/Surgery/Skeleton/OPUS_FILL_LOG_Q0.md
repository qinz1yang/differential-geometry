# OPUS fill log Q0 (queue entry 16: variable derivative threshold)

- 2026-09-25 23:05 PDT. Read chain: every inner use of the fixed `q₀` is (a) per-flow
  (`scalar_deriv_bound_at_actual_source_reset`, the per-flow trace theorem of
  `CompactProductTraceSurvival`), (b) `q₀/scale ≤ 1` eventually (`ProspectiveNeckSurvival:2291`,
  `ProspectiveNeckConvergence:558`), or (c) `2 q₀ < c·Q` eventually (`CompactProductTraceSurvival:
  354-357`). All three follow from `q₀ᵢ/scaleᵢ → 0`. No blocking use found.
- New file `Topology/ProspectiveNeckSurvivalVariableThreshold.lean` (imports
  `ProspectiveNeckSurvival`, reaches private helpers by `open private`); no existing declaration
  touched. Chain copied with `q₀ : ℕ → ℝ`, `∀ i, 0 < q₀ i`, `Tendsto (q₀ i / scale i) → 0`.
  Headline `exists_threshold_uniform_selected_neck_append_backward`:
  `∀ δ k a phi, ∃ ηstar mstar Λ, … ∀ q₀ > 0, ∀ H …, Λ * max q₀ 1 ≤ O.scale → …`.
  Old theorem re-derived as private `exists_uniform_selected_neck_append_backward_of_threshold_uniform`.
- Waiting for the lead build's `ProspectiveNeckSurvival` olean before compiling.
- 2026-09-26 00:30 PDT. Lead build found 5 errors (a dropped `exact hh`, a `by` block broken by
  reflow, private `BackwardPointTrace.concat`); fixed (concat via `open private`). Now
  `LEAN_NUM_THREADS=2 lake env lean` exit 0, no output; with `weak.linter.mathlibStandardSet`
  also clean. Axioms of the headline and of the old-statement corollary: propext,
  Classical.choice, Quot.sound. Not in the root aggregate.
