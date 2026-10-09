import DifferentialGeometry.Geometry.Comparison.NearbyIntegerDimension
import DifferentialGeometry.Geometry.Comparison.LocalDimensionPropagation
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH
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
      ∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m := by
  rcases subsingleton_or_nontrivial X with hsub | hnontrivial
  · have hz (V : Set X) : dimH V = 0 :=
      Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)
    refine ⟨0, Nat.zero_le n, by simpa only [Nat.cast_zero] using hz _, ?_⟩
    intro V _ _ _
    simpa only [Nat.cast_zero] using hz V
  · let : LocallyCompactSpace (ball p (8 * R)) :=
      locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
        (by positivity : 0 < 8 * R) hdim hlocal
    have hdim' : dimH (ball p (8 * R)) ≤ n + 1 :=
      hdim.trans (by exact_mod_cast Nat.le_succ n)
    obtain ⟨m, _, _, q, hq, r, hr, hBr, hchart⟩ :=
      exists_ball_dimH_eq_nat_near_of_intrinsic_local_comparison hcurves p
        (L := 8 * R) (ε := R / 2) (by positivity) (half_pos hR)
        (n := n + 1) (by omega) (by simpa only [Nat.cast_add, Nat.cast_one] using hdim')
        (hlocal ⟨p, mem_ball_self (by positivity)⟩)
    have hhalf : ball p (R / 2) ⊆ closedBall p R := by
      intro x hx
      change dist x p ≤ R
      have hh : dist x p < R / 2 := hx
      linarith
    have hupper : dimH (closedBall p R) ≤ m :=
      (dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer
        hcurves p hR hlocal hq.2 hr).trans_eq hchart
    have hlower : (m : ENNReal) ≤ dimH (closedBall p R) := by
      rw [← hchart]
      exact dimH_mono (hBr.trans (inter_subset_right.trans hhalf))
    have heq : dimH (closedBall p R) = m := le_antisymm hupper hlower
    have hm : m ≤ n := by
      have houter : closedBall p R ⊆ ball p (8 * R) := by
        intro x hx
        change dist x p < 8 * R
        have hh : dist x p ≤ R := hx
        linarith
      have hbound := (dimH_mono houter).trans hdim
      rw [heq] at hbound
      exact_mod_cast hbound
    refine ⟨m, hm, heq, ?_⟩
    intro V hV hVne hVhalf
    obtain ⟨z, hz⟩ := hVne
    obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.mp hV z hz
    apply le_antisymm
    · exact (dimH_mono (hVhalf.trans hhalf)).trans_eq heq
    · rw [← heq]
      exact (dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer
        hcurves p hR hlocal (hVhalf hz) hs).trans (dimH_mono hsub)

end DifferentialGeometry.Geometry.Comparison.Toponogov
