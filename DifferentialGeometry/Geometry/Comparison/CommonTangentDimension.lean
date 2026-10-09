import DifferentialGeometry.Geometry.Comparison.LocalIntegerDimension
import DifferentialGeometry.Geometry.Comparison.IntrinsicLogDimension
import DifferentialGeometry.Geometry.Comparison.TangentDimension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_common_tangent_dimH_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (closedBall p R) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m) ∧
      ∀ (q : X) (hq : q ∈ ball p (R / 2)),
        letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
        dimH (univ : Set (TangentCone q)) = m := by
  obtain ⟨m, hmn, hclosed, hopen⟩ :=
    exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH hcurves p hR hdim hlocal
  refine ⟨m, hmn, hclosed, hopen, ?_⟩
  intro q hq
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
  have hhalf : dimH (ball p (R / 2)) = m :=
    hopen _ isOpen_ball ⟨p, mem_ball_self (half_pos hR)⟩ (Subset.refl _)
  have hlocalHalf : ∀ z ∈ ball p (R / 2),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω := by
    intro z hz
    have hz8 : z ∈ ball p (8 * R) := by
      change dist z p < 8 * R
      have hh : dist z p < R / 2 := hz
      linarith
    exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
      (by positivity : 0 < 8 * R) ⟨z, hz8⟩).mp (hlocal ⟨z, hz8⟩)
  apply le_antisymm
  · exact tangent_dimH_le_of_local_comparison_and_dimH hcurves isOpen_ball
      hhalf.le hlocalHalf hq
  · let : LocallyCompactSpace (ball p (8 * R)) :=
      locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
        (by positivity : 0 < 8 * R) hdim hlocal
    rw [← hclosed]
    exact dimH_closedBall_le_tangent_of_intrinsic_8_buffer hcurves p hR hlocal hq

end DifferentialGeometry.Geometry.Comparison.Toponogov
