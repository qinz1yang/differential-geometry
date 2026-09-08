import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

theorem uhlenbeck_section_eq_and_inner_eq_of_ricciSharp_eq_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {J : Set ℝ} (hJ : J.OrdConnected)
    (hJreg : J ⊆ D.regular)
    (x : M) (Z : ℝ → TangentSpace I x)
    (hZ : ∀ t ∈ J,
      HasDerivWithinAt Z
        (ricciSharp (I := I) (S.family.metric t) x (Z t)) J t)
    (hzero : ∀ t ∈ J,
      ricciSharp (I := I) (S.family.metric t) x (Z t) = 0) :
    (∀ s ∈ J, ∀ t ∈ J, Z s = Z t) ∧
      (∀ s ∈ J, ∀ t ∈ J, ∀ w : TangentSpace I x,
        (S.family.metric s).inner x (Z s) w =
          (S.family.metric t).inner x (Z t) w) := by
  have hconv : Convex ℝ J := hJ.convex
  have hconstZ : ∀ s ∈ J, ∀ t ∈ J, Z s = Z t := by
    intro s hs t ht
    have hle : ‖Z t - Z s‖ ≤ (0 : ℝ) * ‖t - s‖ := by
      exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun r hr => (hZ r hr).hasFDerivWithinAt)
        (fun r hr => by
          rw [hzero r hr]
          simp only [ContinuousLinearMap.toSpanSingleton_zero, norm_zero, le_rfl])
        hs ht
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hle))).symm
  have hdual : ∀ s ∈ J, ∀ t ∈ J, ∀ w : TangentSpace I x,
      (S.family.metric s).inner x (Z s) w =
        (S.family.metric t).inner x (Z t) w := by
    intro s hs t ht w
    have hconstMetric : ∀ a b : J,
        (S.family.metric a).inner x (Z b) w =
          (S.family.metric b).inner x (Z b) w := by
      intro a b
      have hmetricZero : ∀ r ∈ J,
          HasFDerivWithinAt
            (fun s : ℝ => (S.family.metric s).inner x (Z b) w)
            (0 : ℝ →L[ℝ] ℝ) J r := by
        intro r hr
        have hmetric :=
          (metricDerivAt S hS ⟨r, hJreg hr⟩ x (Z b) w).hasDerivWithinAt (s := J)
        have hricci : ricciTensor (I := I) (S.family.metric r) x (Z b) w = 0 := by
          rw [← inner_ricciSharp (I := I) (S.family.metric r) x (Z b) w]
          rw [← hconstZ r hr b.1 b.2, hzero r hr]
          simp
        have hfd := hmetric.hasFDerivWithinAt
        simp only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
          metricRicciAt_apply_eq_ricciTensor] at hfd
        change ricciTensor (I := I) (S.base.metric r) x (Z b) w = 0 at hricci
        rw [hricci, mul_zero, ContinuousLinearMap.toSpanSingleton_zero] at hfd
        exact hfd
      have hle := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
        hmetricZero (fun _ _ => norm_zero.le) b.2 a.2
      exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hle))
    calc
      (S.family.metric s).inner x (Z s) w =
          (S.family.metric s).inner x (Z t) w := by rw [hconstZ s hs t ht]
      _ = (S.family.metric t).inner x (Z t) w := hconstMetric ⟨s, hs⟩ ⟨t, ht⟩
  exact ⟨hconstZ, hdual⟩

end DifferentialGeometry.PDE.RicciFlow
