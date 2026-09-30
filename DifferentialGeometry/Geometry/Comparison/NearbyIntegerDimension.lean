import DifferentialGeometry.Geometry.Comparison.CenteredPairedChart
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison

set_option autoImplicit false

open Set Metric Real
open scoped NNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_ball_dimH_eq_nat_near_of_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hn : 1 ≤ n) (hdim : dimH U ≤ n)
    {p : X} (hp : p ∈ U)
    (hlocal : ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ U ∩ ball p ε,
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ U ∩ ball p ε ∧ dimH (ball q r) = m := by
  obtain ⟨Ω, hΩ, hcomp, hpΩ⟩ := hlocal
  let V := Ω ∩ (U ∩ ball p ε)
  have hV : IsOpen V := hΩ.inter (hU.inter isOpen_ball)
  have hVsub : V ⊆ U ∩ ball p ε := inter_subset_right
  have hcompV : fourPointComparison 1 V := hcomp.mono inter_subset_left
  have hpV : p ∈ V := ⟨hpΩ, hp, mem_ball_self hε⟩
  have hdimV : dimH V ≤ n := (dimH_mono (hVsub.trans inter_subset_left)).trans hdim
  obtain ⟨m, hm1, hmn, q, hq, a, _, r, hr, hBr, W, hW, e, _, _, hlo, hhi⟩ :=
    exists_centered_distance_chart_in_open_set hcurves hcompV (Subset.refl V) hV ⟨p, hpV⟩
      (fun z _ => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩) hn hdimV
  let F : ball q r → PiLp 2 (fun _ : Fin m => ℝ) := fun z => (e z).val
  let D : ℝ≥0 := ⟨pairedChartDistortion n, (pairedChartDistortion_pos n).le⟩
  have hLip : LipschitzWith D F := LipschitzWith.of_dist_le_mul hhi
  have hAnti : AntilipschitzWith D F := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y ≤ pairedChartDistortion n * dist (e x) (e y)
    have hh := mul_le_mul_of_nonneg_left (hlo x y) (pairedChartDistortion_pos n).le
    simpa only [F, D, NNReal.coe_mk, Subtype.dist_eq, ← mul_assoc,
      mul_inv_cancel₀ (pairedChartDistortion_pos n).ne', one_mul] using hh
  have himage : F '' (univ : Set (ball q r)) = W := by
    rw [image_univ]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hz
      obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  have hsource : dimH (univ : Set (ball q r)) = dimH (ball q r) := by
    simpa only [image_univ, Subtype.range_coe] using
      (isometry_subtype_coe.dimH_image (univ : Set (ball q r))).symm
  have heq : dimH (ball q r) = dimH W := by
    apply le_antisymm
    · simpa only [himage, hsource] using hAnti.le_dimH_image (univ : Set (ball q r))
    · simpa only [himage, hsource] using hLip.dimH_image_le (univ : Set (ball q r))
  refine ⟨m, hm1, hmn, q, hVsub hq, r, hr, hBr.trans hVsub, heq.trans ?_⟩
  have hdW := Real.dimH_of_mem_nhds (hW.mem_nhds (e ⟨q, mem_ball_self hr⟩).property)
  simpa using hdW

theorem exists_ball_dimH_eq_nat_near_of_intrinsic_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (o : X) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH (ball o L) ≤ n)
    (hlocal : ∃ Ω : Set (ball o L),
      @IsOpen (ball o L) (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o L) (intrinsicBallMetricSpace hcurves o hL) 1 Ω ∧
      (⟨o, mem_ball_self hL⟩ : ball o L) ∈ Ω) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ ball o L ∩ ball o ε,
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ ball o L ∩ ball o ε ∧ dimH (ball q r) = m := by
  exact exists_ball_dimH_eq_nat_near_of_local_comparison hcurves isOpen_ball hn hdim
    (mem_ball_self hL)
    ((exists_local_fourPointComparison_intrinsicBall_iff hcurves o hL
      ⟨o, mem_ball_self hL⟩).mp hlocal) hε

end DifferentialGeometry.Geometry.Comparison.Toponogov
