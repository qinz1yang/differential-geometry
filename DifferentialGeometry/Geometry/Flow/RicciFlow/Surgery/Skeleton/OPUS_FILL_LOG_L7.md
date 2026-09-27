# OPUS_FILL_LOG_L7 (brick L7 + L7b of DESIGN_C3B)

## 2026-09-26

- Design step 4 consumed: "restrict `S` to `[T_k, T]` (`orientedWitness_timeRestrict`) ... shift by
  `T_k` (`orientedWitness_paraSolution_iff` with `A = 1`) ... Push forward along `Φ` (L7), then undo
  the parabolic rescaling (`orientedWitness_paraSolution_iff`)."
- Items (1), (2), (4) already exist, unchanged:
  `orientedWitness_timeRestrict`, `orientedWitness_of_timeRestrict`,
  `orientedWitness_paraSolution_iff` (SelectedCountersequenceAdapter.lean:231-256; time shift is
  `A = 1`, rescaling undo is `A = q`, `parabolicTime τ A s = τ + s / A`; eps/kappa unchanged, the
  scalar scales by `A⁻¹` via `parabolicSolution_scalar`).
- New file `Perelman/CanonicalNeighborhood/WindowedModelLocalPull.lean` (471 lines), not registered
  in the root aggregate (brief: one file, edit nothing else).
  - L7b: `TangentOrientationSection.pullback (o) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)`
    and `TangentOrientationSection.preservesTangentOrientationAt_pullback`.
  - L7: `WindowedModelWitness.ofLocalPull`, `_model`, `_embedding`, `OrientedWitness.ofLocalPull`
    (orientation hypothesis: `Φ` preserves `oN → o` pointwise), `OrientedWitness.ofLocalPull_of_pullback`
    (design shape, `oN := o.pullback hΦl`, metric identity as `localPullMetric`).
  - Metric identity only on the window `Icc (t - (eps * S.scalar t x)⁻¹) t`; the comparison's
    all-time `pullback_eq` is met by a compact-support tensor extension outside the window.
  - Universe: `N : Type v`, `M : Type (max u v)`; the model is lifted by `ULift.{u}` + `pullback`
    (the window `standardCapWindow D : Type` vs the slab carrier `Type u` needed this; the design
    did not flag it). Same-universe use: `ofLocalPull.{w, w}`.
- Compile: `LEAN_NUM_THREADS=2 lake env lean <file>`: no output. Axioms (scratch copy): propext,
  Classical.choice, Quot.sound for all seven public declarations. Standard linters not run
  (no `lake build`).
- Not done here: L7a (`PartialDiffeomorph` from `Ξ`, source `univ`), and the check that
  `L.extendedMetric τ` restricts `Gk.flow.base.metric τ` on `[time k, t)`.
