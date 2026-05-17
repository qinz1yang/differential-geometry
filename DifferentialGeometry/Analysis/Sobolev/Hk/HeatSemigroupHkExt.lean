import DifferentialGeometry.Analysis.Sobolev.Hk.HeatSemigroupHk

/-!
# The scalar heat semigroup extended to all real times

For a closed Riemannian manifold `(M, g)` and a spectral Sobolev exponent
`σ`, the scalar heat semigroup `e^{t Δ_g}` was previously defined as a
continuous linear endomorphism of `scalarHs g σ` only for **strictly
positive** time. This file packages it as a single
continuous-linear-endomorphism-valued function defined for **every** real
time `t`, by setting it to the identity at `t = 0` and (conventionally)
to the identity for `t < 0`. The resulting family
`heatSemigroupHkExt g σ t : scalarHs g σ →L[ℝ] scalarHs g σ`
is the natural object on which to state strong-continuity and the
semigroup law.

## Main definitions

* `heatSemigroupHkExt g σ t` — the heat semigroup at real time `t`,
  equal to `heatSemigroupHk` for `t > 0` and to the identity otherwise.

## Main results

* `heatSemigroupHkExt_zero`, `_of_pos`, `_of_neg`, `_of_nonpos` — the
  defining case-split lemmas.
* `heatSemigroupHkExt_add` — the semigroup law on `t, s ≥ 0`:
  `e^{(t+s)Δ} = e^{tΔ} ∘ e^{sΔ}`.
* `heatSemigroupHkExt_opNorm_le_one` — the contraction estimate on
  `t ≥ 0`: `‖e^{tΔ}‖ ≤ 1`.
* `heatSemigroupHkExt_coeff` — the coordinate formula on `t ≥ 0`:
  `(e^{tΔ} T).coeff i = exp(−λᵢ t) · T.coeff i`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hk

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.Spectral

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The extended heat semigroup -/

/-- The scalar heat semigroup `e^{t Δ_g}` on the spectral Sobolev space
`scalarHs g σ`, extended to all real times `t`. For `t > 0` this is the
heat semigroup `heatSemigroupHk`; for `t ≤ 0` it is the identity. -/
def heatSemigroupHkExt (g : SmoothRiemannianMetric I M) (σ : ℝ) (t : ℝ) :
    scalarHs (I := I) (M := M) g σ →L[ℝ] scalarHs (I := I) (M := M) g σ :=
  if h : 0 < t then
    heatSemigroupHk (I := I) (M := M) (g := g) h (a := σ) (b := σ)
  else
    ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ)

@[simp] theorem heatSemigroupHkExt_zero (g : SmoothRiemannianMetric I M)
    (σ : ℝ) :
    heatSemigroupHkExt (I := I) (M := M) g σ 0 =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHkExt
  simp

theorem heatSemigroupHkExt_of_pos {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : 0 < t) :
    heatSemigroupHkExt (I := I) (M := M) g σ t =
      heatSemigroupHk (I := I) (M := M) (g := g) ht (a := σ) (b := σ) := by
  unfold heatSemigroupHkExt
  simp [ht]

theorem heatSemigroupHkExt_of_neg {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : t < 0) :
    heatSemigroupHkExt (I := I) (M := M) g σ t =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHkExt
  have : ¬ 0 < t := not_lt.mpr ht.le
  simp [this]

theorem heatSemigroupHkExt_of_nonpos {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : t ≤ 0) :
    heatSemigroupHkExt (I := I) (M := M) g σ t =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHkExt
  have : ¬ 0 < t := not_lt.mpr ht
  simp [this]

/-! ## The semigroup law on `t ≥ 0` -/

/-- **Semigroup law on the non-negative half-line.** For `t, s ≥ 0`,
`e^{(t+s) Δ_g} = e^{t Δ_g} ∘ e^{s Δ_g}` on the spectral Sobolev space
`scalarHs g σ`. -/
theorem heatSemigroupHkExt_add {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    heatSemigroupHkExt (I := I) (M := M) g σ (t + s) =
      (heatSemigroupHkExt (I := I) (M := M) g σ t).comp
        (heatSemigroupHkExt (I := I) (M := M) g σ s) := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · -- `t = 0`: LHS = `heatSemigroupHkExt g σ s`, RHS = `id ∘ heatSemigroupHkExt g σ s`.
    subst ht_eq
    simp [heatSemigroupHkExt_zero]
  · rcases eq_or_lt_of_le hs with hs_eq | hs_pos
    · -- `s = 0`: symmetric case.
      subst hs_eq
      simp [heatSemigroupHkExt_zero]
    · -- Both `t, s > 0`: use the semigroup law from `heatSemigroupHk_add`.
      have hts : 0 < t + s := by linarith
      rw [heatSemigroupHkExt_of_pos (I := I) (M := M) (g := g) (σ := σ) hts,
          heatSemigroupHkExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos,
          heatSemigroupHkExt_of_pos (I := I) (M := M) (g := g) (σ := σ) hs_pos]
      exact heatSemigroupHk_add (I := I) (M := M) (g := g) ht_pos hs_pos (a := σ)

/-! ## The contraction estimate on `t ≥ 0` -/

/-- **Contraction on the non-negative half-line.** For `t ≥ 0`,
`‖e^{t Δ_g}‖_{Hˢ → Hˢ} ≤ 1`. -/
theorem heatSemigroupHkExt_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ‖heatSemigroupHkExt (I := I) (M := M) g σ t‖ ≤ 1 := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · -- `t = 0`: the operator is the identity, `‖id‖ ≤ 1`.
    subst ht_eq
    rw [heatSemigroupHkExt_zero]
    exact ContinuousLinearMap.norm_id_le
  · -- `t > 0`: apply the contraction bound for `heatSemigroupHk`.
    rw [heatSemigroupHkExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos]
    exact heatSemigroupHk_opNorm_le_one (I := I) (M := M) (g := g) ht_pos

/-! ## The coordinate formula on `t ≥ 0` -/

/-- **Coordinate formula on the non-negative half-line.** For `t ≥ 0`,
`(e^{t Δ_g} T).coeff i = exp(−λᵢ t) · T.coeff i`. -/
theorem heatSemigroupHkExt_coeff {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t : ℝ} (ht : 0 ≤ t) (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (heatSemigroupHkExt (I := I) (M := M) g σ t T).coeff i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * T.coeff i := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · -- `t = 0`: identity, and `exp(0) = 1`.
    subst ht_eq
    rw [heatSemigroupHkExt_zero]
    change T.coeff i = _
    rw [mul_zero, Real.exp_zero, one_mul]
  · -- `t > 0`: use the coordinate formula for `heatSemigroupHk`.
    rw [heatSemigroupHkExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos]
    exact heatSemigroupHk_coeff (I := I) (M := M) (g := g) ht_pos T i

end Hk
end Sobolev
end Analysis
end DifferentialGeometry

end
