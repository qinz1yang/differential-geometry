# RicBoundAssembly.lean + MetricCovDerivArityBridge.lean — ric_bound assembly

## ✅ R4a/R4b/R4c/R4f GREEN sorry-free (2026-06-10) — the pointwise geometric core

The entire **pointwise** content of `ric_bound` (RicBound.lean) is now a verified
theorem, plus the metric-norm arity bridge.  Four bricks:

- **R4a `aN_component`** (RicBoundClaims.lean): the component `(A_N)` bound,
  generic in `chrG/chrH/gComp`, taking Claim-1's outputs (`hDlow` = lower-order
  difference-tower constants, `hDtop` = top tower bounded by `|∇_H^N g|`) as
  hypotheses.  = `claim2_component` + `mixed_descent` + compose (one `nlinarith`).
  Conclusion: `|∇_H^N T| ≤ Cpp·|∇_H^N g| + Cppp` on `u`.
- **R4b `tower_bound_to_intrinsic`** (RicBoundAssembly.lean): the `B5` lift — a
  component-tower inequality between two bundled `(0,2)` fields converts, at a
  `gRef`-ON point, to the `√normSq0S` inequality of their `iterCov` towers.
  Proof = `rw [← compL2_tower_eq, ← compL2_tower_eq]; exact hbound`.
- **R4c `aN_intrinsic_point`** (RicBoundAssembly.lean): the per-frame-point
  intrinsic `(A_N)`.  `claim1_LC` (totalize lower bounds via `choose` + the top
  bound at `m=N-1`) → `aN_component` (with `T := frameComp0S (ricciSection (LC g))
  frame`, `gComp := frameComp0S (metricTensorField g) frame`) →
  `tower_bound_to_intrinsic` at `y`.  Conclusion:
  `√normSq0S gRef y (2+N) (iterCov gRef 2 Ric N y) ≤ Cpp·√normSq0S gRef y (2+N)
  (iterCov gRef 2 (metric g) N y) + Cppp`.
- **R4f `metricCovDerivNorm_eq_iterCov`** (MetricCovDerivArityBridge.lean): the
  arity bridge `metricCovDerivNorm N h gRef x = √normSq0S gRef x (2+N) (iterCov
  gRef 2 (metric h) N x)` at a gRef-ON basis.  Built `acEquiv` (the `Fin (2+m) ≃
  Fin (m+2)` cast), `metricCovDerivStep_eq_covStep` (both = `totalNabla0SFun`),
  `covDerivOfField_eq_iterCov` (field cast identity by induction, mirroring
  `iterCov_shift`: `covStep_domDomCongr` + `← iterCov_succ`), then
  `normSq0S_domDomCongr`.

Together R4c + R4f express ric_bound's LHS and RHS at a gRef-ON point in matching
intrinsic form — the whole geometric inequality, pointwise.

## Lean lessons

- `domDomCongr_apply` (a `rfl` `@[simp]`) would NOT fire by `rw` OR `simp only`
  on `(MultilinearSection.domDomCongr … ) x` inside `normSq0S` — display matched
  but elaboration didn't (hidden DFunLike coe / instance args).  A `rfl`-typed
  `have key` ALSO failed to `rw`.  FIX: `show` the whole goal in the
  `ContinuousMultilinearMap.domDomCongr` form (defeq via the rfl) — `show` uses
  `isDefEq` and sees through it; then `rw [normSq0S_domDomCongr]` matches.
- `aN_component` generic in `chrG/chrH/gComp` (Claim-1 outputs as hyps) avoids the
  LC-spelling `set`-folding trap entirely; `aN_intrinsic_point` supplies the LC
  spelling inline (matching `claim1_LC`'s output verbatim — no `set`).

## REMAINING for the ric_bound sorry — ONE intertwined analytic brick (R4d+R4e)

`aN_intrinsic_point` needs, over the WHOLE frame domain `u` (not just at `y`):
- `hgB`: `|∇_gRef^j g|` component bounds (`(B_r)`, `1≤j≤N-1`);
- `hShi`: moving-connection Ricci-tower component bounds (`s ≤ N`);
- `hinv`/`hGinv`: the `g`-inverse component data + bound `C0`;
all in `compL2` (frame-component ℓ²) form, plus `hinvON` (gRef-ON AT `y`).

The component ℓ² over `u` relates to the intrinsic norm via the frame's Gram,
which varies over `u`.  So the remaining brick is the **good-frame construction**:
for each `x ∈ K`, a smooth local frame on a SMALL domain `u ∋ x`, gRef-ON at `x`
(constant Gram–Schmidt of the trivialization frame's gram at `x` — NOT a global
ON frame, much more tractable than feared), with Gram bounded within a factor (by
continuity on small `u`).  Then:
- convert intrinsic `(B_r)` (given on `K`) → `hgB` component form via the bounded
  Gram + `compL2_tower_eq`-style at `x` and continuity nearby;
- convert intrinsic moving Shi → `hShi` via `normSq0S_le_of_metric_equiv`
  (Comparison.lean:520, EXISTS — `normSq0S h ≤ C^s·normSq0S g` from eq 3.3) +
  `iterCovComp_eq_iterCov` (works for the moving Christoffel too) + bounded Gram;
- `hinv`/`hGinv`/`C0` from the gram inverse (Claim1Wiring `ginvCompField`/`gramE`
  machinery already builds these on a trivialization domain);
- finally apply `aN_intrinsic_point` at each `x`, take maxima over a finite
  subcover of compact `K` to uniformize `Cpp/Cppp`, and assemble in RicBound.lean
  using `metricCovDerivNorm_eq_iterCov` (R4f) for the RHS and the defeq
  `ricCovTower g gRef N = iterCov gRef 2 (ricciSection (LC g)) N` for the LHS.

This good-frame + intrinsic↔component conversion + compact-cover uniformization is
the genuine analytic frontier (multi-step).  The pointwise geometric core it
feeds is DONE.

## Build/architecture

RicBoundAssembly: namespace `PDE.RicciFlow`, imports RicBoundClaims + Claim1Wiring
(full instance block incl. Boundaryless + VectorBundle).  MetricCovDerivArityBridge:
namespace `HCGCompactness`, imports AllTimesBounds + ProductMFoldNorm.  Both
focus-checked green; neither imported downstream yet (build on first use).
