# ConvexCombination.lean — route and gotchas

## Goal (DONE, verified GREEN, axiom-clean)

`SmoothRiemannianMetric.convexComb g₁ g₂ χ hχ hχ01 : SmoothRiemannianMetric I M`
with `inner x = χ x • g₁.inner x + (1 - χ x) • g₂.inner x`, plus:
- `@[simp] convexComb_inner` (the inner-product computation rule),
- `convexComb_eq_left_on` (locality: where `χ = 1`, agrees with `g₁`).

Verification: targeted build of the module passed GREEN, no `sorry`/`admit`.
`#print axioms` for all three = `[propext, Classical.choice, Quot.sound]`.

## Route used (the PREFERRED one)

Construction via `Geometry.smoothMetric_of_localCoeff` (`SmoothMetricFromCoeff.lean:189`):
take the fiberwise CLM form `convexCombForm g₁ g₂ χ x := χ x • g₁.inner x + (1-χ x) • g₂.inner x`,
feed `(hsymm, hpos, hcoeff)`, and use `.choose` / `.choose_spec`.

- `hsymm`: `convexCombForm_symm` — `add_apply`/`smul_apply` + `g₁.symm`, `g₂.symm`.
- `hpos`: `convexCombForm_pos` — copied the convexity boundary split from
  `MetricExistence.convex_posDefForms` (lines 225-234): `rcases lt_or_eq_of_le ha`,
  `positivity` in the interior case, boundary case `χ x = 0` reduces to `g₂.pos`.
- `hcoeff x₀ i j`: `convexCombForm_coeff_contMDiffOn` — the only real content.
  Rewrite the frame value to `χ·(g₁.inner · fvᵢ fvⱼ) + (1-χ)·(g₂.inner · fvᵢ fvⱼ)`
  via `convexCombForm_apply`, then on the base set combine
  `ContMDiffAt.mul` / `.add` / `.contMDiffWithinAt`. Each metric's frame coeff is smooth
  via `…CovariantDerivative.metric_inner_contMDiffAt` (`Field.lean:299`), and `χ` via `hχ x`.

## Gotchas (the things that cost iterations)

1. **`mdlBasis` is `private`** in `SmoothMetricFromCoeff.lean`'s `Geometry` namespace, so it
   cannot be referenced from a downstream file even inside `namespace Geometry`. It is *defeq*
   to `Module.finBasis ℝ E`; use that directly. (`frameVec x₀ i x = symmL ℝ x (Module.finBasis ℝ E i)`.)

2. **`frameVec` is not defeq to Mathlib `localFrame`** (the latter has an `if x ∈ baseSet` guard).
   To get `ContMDiffAt (T% frameVec x₀ i) x` for `x ∈ baseSet`, prove an eventual equality on the
   open base set and `congr_of_eventuallyEq` to `contMDiffAt_localFrame_of_mem`. The pointwise
   match is `symmL ℝ y (b i) = e.basisAt b hy i`, closed by
   `Bundle.Trivialization.basisAt` + `Module.Basis.map_apply` + `symmL_apply` +
   `linearEquivAt_symm_apply` (both sides become `e.symm y (b i)`). Use `change`, not `show`
   (style linter flags a goal-changing `show`).

3. **`contMDiffAt_localFrame_of_mem` argument order**: it is a `_root_` lemma whose section
   variables `n e b` come before the explicit `(i) (hx)`. Passing `e` positionally collides with
   `n`. Call with named args: `(I := I) (n := (∞ : WithTop ℕ∞)) (e := e) (b := b) (i := i) hx`.

4. **`congr_of_eventuallyEq` mono goal is not beta-reduced**: the goal is
   `(fun y => ⟨y, frameVec …⟩) y = (fun x => ⟨x, localFrame …⟩) y`, so `rw [hy]` fails to find the
   pattern. Use `congrArg (TotalSpace.mk' E y) hy` instead.

5. **`metric_inner_contMDiffAt` full path**: `DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt`,
   needs `[CompleteSpace E]` (free from `FiniteDimensional ℝ E`) and `hn : n ≤ ∞` (here `le_rfl`).

6. **`unusedSectionVars` (`FiniteDimensional`)**: the three pointwise CLM-form helpers
   (`convexCombForm_apply/_symm/_pos`) do not use finite-dimensionality; each carries an
   `omit [FiniteDimensional ℝ E] in`. The constructor/`hcoeff`/wrappers genuinely need it.

## Project placement

End goal: this is reusable metric infrastructure (gluing two metrics with a bump function),
the kind of lemma consumed by limit-metric / interpolation constructions (e.g. HCG Ch3/Ch4
metric assembly). It is a small, self-contained API brick — a tiny fraction of the whole HCG
compactness project — but a clean, sorry-free one, sitting in the `Geometry/Metric` layer next
to `SmoothMetricFromCoeff` and `MetricExistence` whose machinery it reuses.
