import DifferentialGeometry.Geometry.Comparison.GlobalIntegerDimension
import DifferentialGeometry.Geometry.Comparison.CommonTangentDimension
import DifferentialGeometry.Geometry.Comparison.DirectionDimension
import DifferentialGeometry.Geometry.Comparison.LocalTangentDimension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_global_tangent_dimH_and_directions_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∀ q : X,
        letI : HasAnglesAt q := by
          obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
          exact hasAnglesAt_of_local_fourPointComparison
            (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
        dimH (univ : Set (TangentCone q)) = m ∧
          dimH (univ : Set (SpaceOfDirections q)) ≤ (m - 1 : ℕ) ∧
          (1 < m → ∀ a b : SpaceOfDirections q,
            ∃ f : Icc (0 : ℝ) 1 → SpaceOfDirections q,
              Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) := by
  obtain ⟨m, hmn, hglobal, hopen⟩ :=
    exists_global_integer_dimH_of_local_comparison_and_dimH hcurves hdim hlocal
  refine ⟨m, hmn, hglobal, hopen, ?_⟩
  intro q
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  have hdim8 : dimH (ball q (8 * (1 : ℝ))) ≤ m :=
    (dimH_mono (subset_univ _)).trans_eq hglobal
  have hlocal8 : ∀ z : ball q (8 * (1 : ℝ)), ∃ Ω : Set (ball q (8 * (1 : ℝ))),
      @IsOpen (ball q (8 * (1 : ℝ)))
        (intrinsicBallMetricSpace hcurves q (by norm_num : (0 : ℝ) < 8 * 1)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball q (8 * (1 : ℝ)))
        (intrinsicBallMetricSpace hcurves q (by norm_num : (0 : ℝ) < 8 * 1)) 1 Ω ∧ z ∈ Ω := by
    intro z
    exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves q
      (by norm_num : (0 : ℝ) < 8 * 1) z).mpr (hlocal z.val)
  obtain ⟨k, _, hclosed, hopenk, hT⟩ :=
    exists_common_tangent_dimH_of_intrinsic_eight_comparison_and_dimH
      hcurves q zero_lt_one hdim8 hlocal8
  have hhalfne : (ball q (1 / 2 : ℝ)).Nonempty :=
    ⟨q, mem_ball_self (by norm_num)⟩
  have hk : (k : ENNReal) = m :=
    (hopenk _ isOpen_ball hhalfne (Subset.refl _)).symm.trans
      (hopen _ isOpen_ball hhalfne)
  refine ⟨(hT q (mem_ball_self (by norm_num))).trans hk, ?_, ?_⟩
  · exact (direction_covering_and_dimH_of_local_comparison_and_dimH
      hcurves isOpen_univ hglobal.le (fun z _ => hlocal z) (mem_univ q)).2
  · intro hm
    have hlower : (1 : ENNReal) < dimH (closedBall q (1 : ℝ)) := by
      rw [hclosed, hk]
      exact_mod_cast hm
    exact directions_geodesic_of_intrinsic_eight_comparison_and_dimH_gt_one
      hcurves q zero_lt_one hdim8 hlocal8 (by omega) hlower
      (mem_ball_self (by norm_num))

end DifferentialGeometry.Geometry.Comparison.Toponogov
