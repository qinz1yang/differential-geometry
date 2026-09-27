# Lane C2U: `HistoryReducedVolumeLocalUpperBound` (Perelman I 7.3 through the history)

2026-09-26. Verdict: BLOCKED. No Lean file created; no compile.

- The leaf looks true, but the proof needs a per-geodesic Gaussian-tail mass bound for
  history minimizers. That in turn needs the L-exponential map and the Jacobian monotonicity
  through regular crossings. Nothing in the tree provides this.
- Why the collaborator's lemmas do not cover it: every history mass lemma
  (`HistoryMinimizingDensity.lean:158`, `:415`, `EventAction.lean`) needs one common flow `S`
  on a manifold `X`, injective local diffeomorphisms `f j` into every stage, and a compact
  barrier `K`. But `regularMinimizerEndpoints` only constrains a curve at the event times
  (`RegularCrossing`). Between events a minimizer may enter a horn that is discarded at the
  next event, or a new cap. No common `X` contains those regions. The complement of `K`
  therefore contributes (density up to `exp(-barrier/2v)`) × (total stage volume), and neither
  factor is uniform in `H`.
- The single-flow theorem exists: `exists_pos_redVolume_le_on_flowMetricBall`
  (`Perelman/LGeometry/ReducedVolume/BallEstimate/UniformUpperBound.lean:221`). It needs
  `[CompactSpace M] [ConnectedSpace M]`, `Ioc (t - r^2) t ⊆ D.regular` (no event in the
  window), and `r ≤ rho`, with `eps₀` depending on `rho`. The single-flow Gaussian tail lemma
  `lintegral_redDensity_image_lExp_le_volume_add_gaussian_tail` (`MinimizingMass.lean:711`)
  works on a noncompact `M`, but only for one flow.
- Interface note: the leaf's `σ` is independent of `r`, but the tree's `eps₀` depends on the
  radius bound `rho`. The assembly already knows `ρ = ε` when it calls `hupper`, and
  `NoncollapsedAboveBefore` carries `r ≤ ρ`. So the cheap restatement is
  `∃ C₀ > 0, ∀ η > 0, ∀ ρ > 0, ∃ σ ∈ (0,1], ∀ H t p r, r ≤ ρ → ball → …`.
- Missing bricks: (HT) history L-exp and Jacobian monotonicity across regular crossings, with
  the Gaussian tail bound for `reducedVolume`; (CF) confinement of `|Z| ≤ R` history
  L-geodesics in the traced parabolic ball, which needs Shi-type `|∇R|` bounds through
  crossings; (VC) comparing the traced ball's volume at `t - τ` with `vol_t B(p,r)` through
  events. A restriction to "no event in `(t - r^2, t]`" would reduce to the single-flow
  theorem, but it cannot feed the assembly: events close to `t` are exactly the surgery case.
