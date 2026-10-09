import DifferentialGeometry.Geometry.Comparison.RoughLocalCompactness
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison
import DifferentialGeometry.Topology.MetricSpace.CompactNeighborhoods

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem locallyCompactSpace_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hdim : dimH U ≤ n)
    (hlocal : ∀ p ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    LocallyCompactSpace U := by
  apply locallyCompactSpace_subtype_of_compact_closedBalls
  intro p hp
  obtain ⟨Ω, hΩ, hcomp, hpΩ⟩ := hlocal p hp
  obtain ⟨r, hr, hsub, hcompact⟩ := exists_compact_closedBall_of_local_rough_dimension
    hcurves (hΩ.inter hU) (hcomp.mono inter_subset_left)
    (fun z _ => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩)
    ((dimH_mono inter_subset_right).trans hdim) ⟨hpΩ, hp⟩
  exact ⟨r, hr, hsub.trans inter_subset_right, hcompact⟩

theorem locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) {n : ℕ} (hdim : dimH (ball o L) ≤ n)
    (hlocal : ∀ p : ball o L, ∃ Ω : Set (ball o L),
      @IsOpen (ball o L) (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o L) (intrinsicBallMetricSpace hcurves o hL) 1 Ω ∧ p ∈ Ω) :
    LocallyCompactSpace (ball o L) := by
  apply locallyCompactSpace_of_local_comparison_and_dimH hcurves isOpen_ball hdim
  intro p hp
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves o hL ⟨p, hp⟩).mp
    (hlocal ⟨p, hp⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov
