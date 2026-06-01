import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupHs

/-!
# The scalar heat semigroup extended to all real times

For a closed Riemannian manifold `(M, g)` and a spectral Sobolev exponent
`σ`, the scalar heat semigroup `e^{t Δ_g}` was previously defined as a
continuous linear endomorphism of `scalarHs g σ` only for **strictly
positive** time. This file packages it as a single
continuous-linear-endomorphism-valued function defined for **every** real
time `t`, by setting it to the identity at `t = 0` and (conventionally)
to the identity for `t < 0`. The resulting family
`heatSemigroupHsExt g σ t : scalarHs g σ →L[ℝ] scalarHs g σ`
is the natural object on which to state strong-continuity and the
semigroup law.

## Main definitions

* `heatSemigroupHsExt g σ t` — the heat semigroup at real time `t`,
  equal to `heatSemigroupHs` for `t > 0` and to the identity otherwise.

## Main results

* `heatSemigroupHsExt_zero`, `_of_pos`, `_of_neg`, `_of_nonpos` — the
  defining case-split lemmas.
* `heatSemigroupHsExt_add` — the semigroup law on `t, s ≥ 0`:
  `e^{(t+s)Δ} = e^{tΔ} ∘ e^{sΔ}`.
* `heatSemigroupHsExt_opNorm_le_one` — the contraction estimate on
  `t ≥ 0`: `‖e^{tΔ}‖ ≤ 1`.
* `heatSemigroupHsExt_coeff` — the coordinate formula on `t ≥ 0`:
  `(e^{tΔ} T).coeff i = exp(−λᵢ t) · T.coeff i`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The scalar heat semigroup `e^{t Δ_g}` on the spectral Sobolev space
`scalarHs g σ`, extended to all real times `t`. For `t > 0` this is the
heat semigroup `heatSemigroupHs`; for `t ≤ 0` it is the identity. -/
def heatSemigroupHsExt (g : SmoothRiemannianMetric I M) (σ : ℝ) (t : ℝ) :
    scalarHs (I := I) (M := M) g σ →L[ℝ] scalarHs (I := I) (M := M) g σ :=
  if h : 0 < t then
    heatSemigroupHs (I := I) (M := M) (g := g) h (a := σ) (b := σ)
  else
    ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ)

@[simp] theorem heatSemigroupHsExt_zero (g : SmoothRiemannianMetric I M)
    (σ : ℝ) :
    heatSemigroupHsExt (I := I) (M := M) g σ 0 =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHsExt
  simp

theorem heatSemigroupHsExt_of_pos {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : 0 < t) :
    heatSemigroupHsExt (I := I) (M := M) g σ t =
      heatSemigroupHs (I := I) (M := M) (g := g) ht (a := σ) (b := σ) := by
  unfold heatSemigroupHsExt
  simp [ht]

theorem heatSemigroupHsExt_of_neg {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : t < 0) :
    heatSemigroupHsExt (I := I) (M := M) g σ t =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHsExt
  have : ¬ 0 < t := not_lt.mpr ht.le
  simp [this]

theorem heatSemigroupHsExt_of_nonpos {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : t ≤ 0) :
    heatSemigroupHsExt (I := I) (M := M) g σ t =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHsExt
  have : ¬ 0 < t := not_lt.mpr ht
  simp [this]

/-- **Semigroup law on the non-negative half-line.** For `t, s ≥ 0`,
`e^{(t+s) Δ_g} = e^{t Δ_g} ∘ e^{s Δ_g}` on the spectral Sobolev space
`scalarHs g σ`. -/
theorem heatSemigroupHsExt_add {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    heatSemigroupHsExt (I := I) (M := M) g σ (t + s) =
      (heatSemigroupHsExt (I := I) (M := M) g σ t).comp
        (heatSemigroupHsExt (I := I) (M := M) g σ s) := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    simp [heatSemigroupHsExt_zero]
  · rcases eq_or_lt_of_le hs with hs_eq | hs_pos
    · subst hs_eq
      simp [heatSemigroupHsExt_zero]
    · have hts : 0 < t + s := by linarith
      rw [heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) hts,
          heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos,
          heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) hs_pos]
      exact heatSemigroupHs_add (I := I) (M := M) (g := g) ht_pos hs_pos (a := σ)

/-- **Contraction on the non-negative half-line.** For `t ≥ 0`,
`‖e^{t Δ_g}‖_{Hˢ → Hˢ} ≤ 1`. -/
theorem heatSemigroupHsExt_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ‖heatSemigroupHsExt (I := I) (M := M) g σ t‖ ≤ 1 := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    rw [heatSemigroupHsExt_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos]
    exact heatSemigroupHs_opNorm_le_one (I := I) (M := M) (g := g) ht_pos

/-- **Coordinate formula on the non-negative half-line.** For `t ≥ 0`,
`(e^{t Δ_g} T).coeff i = exp(−λᵢ t) · T.coeff i`. -/
theorem heatSemigroupHsExt_coeff {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t : ℝ} (ht : 0 ≤ t) (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (heatSemigroupHsExt (I := I) (M := M) g σ t T).coeff i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * T.coeff i := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    rw [heatSemigroupHsExt_zero]
    change T.coeff i = _
    rw [mul_zero, Real.exp_zero, one_mul]
  · rw [heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos]
    exact heatSemigroupHs_coeff (I := I) (M := M) (g := g) ht_pos T i

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
