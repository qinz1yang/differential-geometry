import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# Consumers of the derivative-norm bridge and of scale invariance

* `curvatureDerivativesControlled_iff_curvDerivNorm`: the Collapse derivative-control predicate
  restated in the compactness/Shi norm `curvDerivNorm` (bridge T1), so that Shi and compactness
  output can feed it directly.
* `compactCarrier_exists_bound_curvDerivNorm`: on an actual compact carrier, finitely many
  compactness-side derivative norms are uniformly bounded (T1 with
  `exists_bound_curvatureDerivativeNorm_of_compactSpace`).
* `compactCarrier_normalized_curvatureScale`: on an actual compact carrier, any smooth metric `g`
  rescales to `c g` with every curvature scale at least `1`, the static predicates
  `volumeCollapsedAtCurvatureScale` and `curvatureDerivativesControlled` unchanged (T3), and the
  derivative norms multiplied by `ρ ^ (k + 2)` (T2), where `ρ` is the curvature-scale floor
  (A1 T3) and `c = ρ⁻²`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The Collapse derivative-control predicate in the compactness-side norm `curvDerivNorm`. -/
theorem curvatureDerivativesControlled_iff_curvDerivNorm {g : SmoothRiemannianMetric I M} {K : ℕ}
    {A : ℝ → ℝ} {w₀ : ℝ} :
    curvatureDerivativesControlled g K A w₀ ↔
      ∀ (p : M) (w r : ℝ), w₀ ≤ w → w < euclideanThreeUnitBallVolume →
        0 < r → ENNReal.ofReal r < curvatureRadius g p →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf g p r,
          CheegerGromovCompactness.curvDerivNorm k g q ≤ A w * (r ^ (k + 2))⁻¹ := by
  unfold curvatureDerivativesControlled
  simp only [curvatureDerivativeNorm_eq_curvDerivNorm]

end General

/-- On a compact carrier, the compactness-side derivative norms of orders `≤ K` are uniformly
bounded. -/
theorem compactCarrier_exists_bound_curvDerivNorm (W : GC.Endpoint.CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ K → ∀ x : W.Carrier,
      CheegerGromovCompactness.curvDerivNorm k g x ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_curvatureDerivativeNorm_of_compactSpace g K
  exact ⟨B, hB, fun k hk x => curvatureDerivativeNorm_eq_curvDerivNorm g k x ▸ hbound k hk x⟩

/-- Normalisation of the curvature scale on a compact carrier: `c = ρ⁻²` for a curvature-scale
floor `ρ` of `g` makes every curvature scale of `c g` at least `1`, keeps both static
predicates, and multiplies the `k`-th derivative norm by `ρ ^ (k + 2)`. -/
theorem compactCarrier_normalized_curvatureScale (W : GC.Endpoint.CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      (∀ p : W.Carrier, 1 ≤ curvatureRadius (scaleMetric (ρ ^ 2)⁻¹ (by positivity) g) p) ∧
      (∀ (w : ℝ) (p : W.Carrier),
        volumeCollapsedAtCurvatureScale (scaleMetric (ρ ^ 2)⁻¹ (by positivity) g) w p ↔
          volumeCollapsedAtCurvatureScale g w p) ∧
      (∀ (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ),
        curvatureDerivativesControlled (scaleMetric (ρ ^ 2)⁻¹ (by positivity) g) K A w₀ ↔
          curvatureDerivativesControlled g K A w₀) ∧
      ∀ (k : ℕ) (x : W.Carrier),
        curvatureDerivativeNorm (scaleMetric (ρ ^ 2)⁻¹ (by positivity) g) k x =
          ρ ^ (k + 2) * curvatureDerivativeNorm g k x := by
  obtain ⟨ρ, hρ, hfloor⟩ := exists_pos_le_curvatureRadius g
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hc : 0 < (ρ ^ 2)⁻¹ := by positivity
  have hsqrt : Real.sqrt (ρ ^ 2)⁻¹ = ρ⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq hρ.le]
  refine ⟨ρ, hρ, fun p => ?_, fun w p => volumeCollapsedAtCurvatureScale_scaleMetric_iff hdim _ hc,
    fun K A w₀ => curvatureDerivativesControlled_scaleMetric_iff hdim _ hc, fun k x => ?_⟩
  · rw [curvatureRadius_scaleMetric, hsqrt]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ρ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le), inv_mul_cancel₀ hρ.ne',
            ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal ρ⁻¹ * curvatureRadius g p := mul_le_mul' le_rfl (hfloor p)
  · rw [curvatureDerivativeNorm_scaleMetric_div, hsqrt, div_eq_mul_inv, mul_inv, inv_inv, inv_pow,
      inv_inv, pow_add]
    ring

end DifferentialGeometry.Geometry.Collapse
