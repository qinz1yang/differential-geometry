import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩
private local instance (O : Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt
    [BoundarylessManifold I M]
    (O : Opens (S2 × ℝ)) (g : SmoothRiemannianMetric I M) (f : O → M)
    (hf : IsLocalDiffeomorph IC I ∞ f) (hinj : Injective f)
    (q : ℝ) (hq : 0 < q) (K : Set O) (k : ℕ) (hk : 2 ≤ k)
    (η : ℝ) (hη : η ≤ 1 / 2)
    (hsmall : metricDerivENormSupOn K k
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) f hf hinj)
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen O)
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen O) < ENNReal.ofReal η)
    (x : O) (hx : x ∈ K) :
    |metricScalarAt g (f x) / q - 1| ≤ 4323 * η := by
  have h := abs_scalar_curvature_restricted_roundCylinder_sub_one_le O
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) f hf hinj) x η hη
    (fun j hj => (metricDerivNorm_lt_of_sup_lt K k _ _ _ hsmall (hj.trans hk) hx).le)
  rw [metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale] at h
  exact h

namespace normalizedDatum

variable [Fact (Module.finrank ℝ E = 3)] [I.Boundaryless]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem normalizedMetric_scalar (d : normalizedDatum g x₀ δ k)
    (x : bufferedCylinder δ) :
    metricScalarAt d.normalizedMetric x = metricScalarAt g (d.map x) / metricScalarAt g x₀ := by
  rw [normalizedMetric, metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale]

theorem normalizedMetric_scalar_center (d : normalizedDatum g x₀ δ k) :
    metricScalarAt d.normalizedMetric (cylinderCenter δ d.precision_pos) = 1 := by
  rw [d.normalizedMetric_scalar, d.center_eq, div_self (ne_of_gt d.scalar_pos)]

theorem abs_scalar_ratio_sub_one_le (d : normalizedDatum g x₀ δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (x : bufferedCylinder δ)
    (hx : x ∈ controlledCylinder δ) :
    |metricScalarAt g (d.map x) / metricScalarAt g x₀ - 1| ≤ 4323 * δ := by
  have h := abs_scalar_curvature_restricted_roundCylinder_sub_one_le
    (bufferedCylinder δ) d.normalizedMetric x δ hδ
    (fun j hj => (metricDerivNorm_lt_of_sup_lt (controlledCylinder δ) k _ _ _
      d.normalizedMetric_error_lt (hj.trans hk) hx).le)
  rw [d.normalizedMetric_scalar] at h
  exact h

theorem scalar_pos_of_controlled (d : normalizedDatum g x₀ δ k)
    (hk : 2 ≤ k) (hsmall : 4323 * δ < 1) (x : bufferedCylinder δ)
    (hx : x ∈ controlledCylinder δ) : 0 < metricScalarAt g (d.map x) := by
  have hδ : δ ≤ 1 / 2 := by linarith [d.precision_pos]
  have h := (abs_le.mp (d.abs_scalar_ratio_sub_one_le hk hδ x hx)).1
  have hratio : 0 < metricScalarAt g (d.map x) / metricScalarAt g x₀ := by linarith
  exact (div_pos_iff_of_pos_right d.scalar_pos).mp hratio

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
