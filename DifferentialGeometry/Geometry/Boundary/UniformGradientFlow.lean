import DifferentialGeometry.Geometry.Boundary.UniformFlow
import DifferentialGeometry.Geometry.Boundary.InwardVector
import DifferentialGeometry.Geometry.Boundary.Gradient
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Topology.Manifold.IntegralCurveHeight

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Gradient DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M]

theorem exists_normalizedGradient_lower_uniformFlow (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ y, mfderiv I 𝓘(ℝ) u y ≠ 0)
    {K : Set M} (hK : IsCompact K) (hboundary : K ⊆ I.boundary M)
    (hmin : ∀ x ∈ K, IsLocalMin u x) :
    ∃ ε > 0, ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ ∃ Φ : M × ℝ → M,
      (∀ y ∈ U, Φ (y, 0) = y) ∧
      ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (U ×ˢ Ico 0 ε) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) (normalizedGradient g u) (Ico 0 ε)) ∧
      (∀ y ∈ U, ∀ t ∈ Ico 0 ε, u (Φ (y, t)) = u y + t) ∧
      ∀ y ∈ U, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  have hv := contMDiff_normalizedGradient g u hu hreg
  have hinward : ∀ (x : BoundaryManifold I M), x.1 ∈ K →
      ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
        normalizedGradient g u x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x := by
    intro x hx
    apply (exists_pos_inward_decomposition_iff g x _).2
    exact normalizedGradient_inner_outwardNormal_neg_of_isLocalMin g (hmin x.1 hx)
      (hu.mdifferentiableAt (by simp)) (hreg x.1)
  obtain ⟨ε, hε, U, hU, hKU, Φ, hzero, hΦ, hcurve, hinside⟩ :=
    exists_inward_uniformFlow hK hboundary hv hinward
  refine ⟨ε, hε, U, hU, hKU, Φ, hzero, hΦ, hcurve, ?_, hinside⟩
  intro y hy t ht
  have h := height_eq_add_mul_time hε (hu.mdifferentiable (by simp))
    (fun z ↦ mfderiv_normalizedGradient g u z (hreg z)) (hcurve y hy) t ht
  simpa only [hzero y hy, one_mul] using h

theorem exists_normalizedGradient_upper_uniformFlow (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ y, mfderiv I 𝓘(ℝ) u y ≠ 0)
    {K : Set M} (hK : IsCompact K) (hboundary : K ⊆ I.boundary M)
    (hmax : ∀ x ∈ K, IsLocalMax u x) :
    ∃ ε > 0, ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ ∃ Φ : M × ℝ → M,
      (∀ y ∈ U, Φ (y, 0) = y) ∧
      ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (U ×ˢ Ico 0 ε) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) (-normalizedGradient g u) (Ico 0 ε)) ∧
      (∀ y ∈ U, ∀ t ∈ Ico 0 ε, u (Φ (y, t)) = u y - t) ∧
      ∀ y ∈ U, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  have hv := (contMDiff_normalizedGradient g u hu hreg).neg_section
  have hinward : ∀ (x : BoundaryManifold I M), x.1 ∈ K →
      ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
        (-normalizedGradient g u) x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x := by
    intro x hx
    apply (exists_pos_inward_decomposition_iff g x _).2
    rw [Pi.neg_apply, map_neg, neg_apply]
    exact neg_neg_of_pos (normalizedGradient_inner_outwardNormal_pos_of_isLocalMax g (hmax x.1 hx)
      (hu.mdifferentiableAt (by simp)) (hreg x.1))
  obtain ⟨ε, hε, U, hU, hKU, Φ, hzero, hΦ, hcurve, hinside⟩ :=
    exists_inward_uniformFlow hK hboundary hv hinward
  refine ⟨ε, hε, U, hU, hKU, Φ, hzero, hΦ, hcurve, ?_, hinside⟩
  intro y hy t ht
  have hunit : ∀ z, mfderiv I 𝓘(ℝ) u z ((-normalizedGradient g u) z) = (-1 : ℝ) := by
    intro z
    rw [Pi.neg_apply, map_neg, mfderiv_normalizedGradient g u z (hreg z)]
    rfl
  have h := height_eq_add_mul_time hε (hu.mdifferentiable (by simp)) hunit (hcurve y hy) t ht
  simpa only [hzero y hy, neg_one_mul, sub_eq_add_neg] using h

end DifferentialGeometry.Geometry.Boundary
