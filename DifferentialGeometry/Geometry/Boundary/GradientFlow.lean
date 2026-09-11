import DifferentialGeometry.Geometry.Boundary.LocalFlow
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
open DifferentialGeometry.Geometry.Gradient
open DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem exists_normalizedGradient_lower_localFlow (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ y, mfderiv I 𝓘(ℝ) u y ≠ 0)
    (x : BoundaryManifold I M) (hmin : IsLocalMin u x.1) :
    ∃ ε > 0, ∃ V : Set M, IsOpen V ∧ x.1 ∈ V ∧ ∃ Φ : M × ℝ → M,
      (∀ y ∈ V, Φ (y, 0) = y) ∧
      ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (V ×ˢ Ico 0 ε) ∧
      (∀ y ∈ V, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) (normalizedGradient g u) (Ico 0 ε)) ∧
      (∀ y ∈ V, ∀ t ∈ Ico 0 ε, u (Φ (y, t)) = u y + t) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  have hsign := normalizedGradient_inner_outwardNormal_neg_of_isLocalMin g hmin
    (hu.mdifferentiableAt (by simp)) (hreg x.1)
  obtain ⟨ε, hε, V, hV, hxV, Φ, hzero, hΦ, hcurve, hinside⟩ :=
    exists_inward_localFlow (contMDiff_normalizedGradient g u hu hreg) x
      ((exists_pos_inward_decomposition_iff g x _).2 hsign)
  refine ⟨ε, hε, V, hV, hxV, Φ, hzero, hΦ, hcurve, ?_, hinside⟩
  intro y hy t ht
  have h := height_eq_add_mul_time hε (hu.mdifferentiable (by simp))
    (fun z ↦ mfderiv_normalizedGradient g u z (hreg z)) (hcurve y hy) t ht
  simpa only [hzero y hy, one_mul] using h

theorem exists_normalizedGradient_upper_localFlow (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ y, mfderiv I 𝓘(ℝ) u y ≠ 0)
    (x : BoundaryManifold I M) (hmax : IsLocalMax u x.1) :
    ∃ ε > 0, ∃ V : Set M, IsOpen V ∧ x.1 ∈ V ∧ ∃ Φ : M × ℝ → M,
      (∀ y ∈ V, Φ (y, 0) = y) ∧
      ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (V ×ˢ Ico 0 ε) ∧
      (∀ y ∈ V, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) (-normalizedGradient g u) (Ico 0 ε)) ∧
      (∀ y ∈ V, ∀ t ∈ Ico 0 ε, u (Φ (y, t)) = u y - t) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  have hsign : g.inner x.1 (-normalizedGradient g u x.1) (outwardNormal g x) < 0 := by
    rw [map_neg, neg_apply]
    exact neg_neg_of_pos (normalizedGradient_inner_outwardNormal_pos_of_isLocalMax g hmax
      (hu.mdifferentiableAt (by simp)) (hreg x.1))
  obtain ⟨ε, hε, V, hV, hxV, Φ, hzero, hΦ, hcurve, hinside⟩ :=
    exists_inward_localFlow (contMDiff_normalizedGradient g u hu hreg).neg_section x
      ((exists_pos_inward_decomposition_iff g x _).2 hsign)
  refine ⟨ε, hε, V, hV, hxV, Φ, hzero, hΦ, hcurve, ?_, hinside⟩
  intro y hy t ht
  have hunit : ∀ z, mfderiv I 𝓘(ℝ) u z ((-normalizedGradient g u) z) = (-1 : ℝ) := by
    intro z
    rw [Pi.neg_apply, map_neg, mfderiv_normalizedGradient g u z (hreg z)]
    rfl
  have h := height_eq_add_mul_time hε (hu.mdifferentiable (by simp)) hunit (hcurve y hy) t ht
  simpa only [hzero y hy, neg_one_mul, sub_eq_add_neg] using h

end DifferentialGeometry.Geometry.Boundary
