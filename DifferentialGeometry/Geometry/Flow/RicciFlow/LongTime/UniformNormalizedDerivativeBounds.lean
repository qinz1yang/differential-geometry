import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PhysicalDerivativeNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SurgeryEventControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime

universe u

theorem exists_uniform_normalized_derivative_bound_of_physical {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (b T : ℝ → ℝ) (A : ℝ → ℕ → ℝ)
    (hphysical : ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation,
      T w ≤ s.time → ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
      ρ ≤ b w * Real.sqrt s.time →
      (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
      (∀ q ∈ riemannianBallOf s.metric p ρ,
        SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
        curvatureDerivativeNorm s.metric k q ≤ A w k * (ρ ^ (k + 2))⁻¹) :
    ∃ C : ℝ → ℝ, (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹ := by
  classical
  let C : ℝ → ℝ := fun w => max 1 ((Finset.range (K + 1)).sup' (by simp) (A w))
  have hC : ∀ w, 0 < C w :=
    fun w => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro w hw s hs p r hr hrb hnegative hsectional hvolume k hk q hq
  have hbound := s.curvatureDerivativeNorm_normalizedMetric_le_of_physical_whole_ball
    K w (b w) (A w) (hphysical w hw s hs) p r hr hrb hnegative hsectional hvolume
    k hk q hq
  have hAC : A w k ≤ C w :=
    (Finset.le_sup' (A w) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
      (le_max_right _ _)
  exact hbound.trans (mul_le_mul_of_nonneg_right hAC (inv_nonneg.mpr (pow_nonneg hr.le _)))

end GC.LongTime
