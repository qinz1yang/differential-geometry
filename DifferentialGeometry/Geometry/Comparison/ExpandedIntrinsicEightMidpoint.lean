import DifferentialGeometry.Geometry.Comparison.LongShortMidpoint
import DifferentialGeometry.Geometry.Comparison.PerimeterBudgetInteriorComparison
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallLength
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallGeometry

set_option autoImplicit false


open Set Metric Real Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_cosh_midpoint_of_expanded_intrinsic_8_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    [LocallyCompactSpace (ball o (8 * R))]
    (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
      @IsOpen (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)
    {A : ℝ} (hA : 0 ≤ A) (σ : Icc (0 : ℝ) A → X) (hσ : Isometry σ)
    (hσmem : ∀ s, σ s ∈ closedBall o (3 * R / 2)) {z : X} (hz : z ∈ closedBall o (3 * R / 2))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) A)
    (hdist : dist z (σ ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) < 5 * R / 2) :
    ∃ h : ℝ, 0 < h ∧ h ≤ t ∧ t + h ≤ A ∧
      cosh (sqrt κ * dist z (IccExtend hA σ (t - h))) +
        cosh (sqrt κ * dist z (IccExtend hA σ (t + h))) ≤
        2 * cosh (sqrt κ * h) * cosh (sqrt κ * dist z (IccExtend hA σ t)) := by
  let U := ball o (8 * R)
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)
  let σ' : Icc (0 : ℝ) A → U := fun s => ⟨σ s, by
    have hd : dist (σ s) o ≤ 3 * R / 2 := hσmem s
    change dist (σ s) o < 8 * R
    linarith⟩
  let z' : U := ⟨z, by
    have hd : dist z o ≤ 3 * R / 2 := hz
    change dist z o < 8 * R
    linarith⟩
  have hlocally := intrinsicBallMetricSpace_locallyCompact hcurves o (by positivity : 0 < 8 * R)
  have hσiso : @Isometry (Icc (0 : ℝ) A) U inferInstance m.toPseudoEMetricSpace σ' := by
    apply @Isometry.of_dist_eq (Icc (0 : ℝ) A) U inferInstance m.toPseudoMetricSpace
    intro s v
    rw [intrinsicBall_dist_eq_on_inner_closedBall hcurves o (by positivity) (a := σ' s) (b := σ' v)
      (by positivity : 0 < 3 * R / 2)
      (by rw [dist_self]; linarith : dist o o + 4 * (3 * R / 2) < 8 * R)
      (hσmem s) (hσmem v)]
    exact hσ.dist_eq s v
  have hdist_eq (s : Icc (0 : ℝ) A) : @dist U m.toDist z' (σ' s) = dist z (σ s) := by
    exact intrinsicBall_dist_eq_on_inner_closedBall hcurves o (by positivity) (a := z') (b := σ' s)
      (by positivity : 0 < 3 * R / 2)
      (by rw [dist_self]; linarith : dist o o + 4 * (3 * R / 2) < 8 * R)
      (by have hd : dist z o ≤ 3 * R / 2 := hz; change dist z o ≤ 3 * R / 2; linarith)
      (hσmem s)
  have hc : @IsComplete U m.toUniformSpace (@closedBall U m.toPseudoMetricSpace z' (129 * R / 20)) :=
    isComplete_intrinsicBall_closedBall hcurves o (by positivity) z' (by
      change dist z o + 129 * R / 20 < 8 * R
      have hd : dist z o ≤ 3 * R / 2 := hz
      linarith)
  have hcurvesU := fun (a b : U) (ε : ℝ) (hε : 0 < ε) =>
    intrinsicBallMetricSpace_arbitrarily_short_curves hcurves o (by positivity : 0 < 8 * R) a b hε
  have hcmp : @endpointHingeComparison U m κ z' (10191 * R / 4040) := by
    have h := @endpointHingeComparison_of_complete_perimeter_budget_buffer U m hlocally κ
      hκ.le hcurvesU hlocal z' (129 * R / 20) hc
    convert h using 1; ring
  let t' : Icc (0 : ℝ) A := ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
  have hD : @dist U m.toDist (σ' t') z' < 5 * R / 2 := by rw [@dist_comm U m.toPseudoMetricSpace, hdist_eq]; exact hdist
  have hgap : 0 < 10191 * R / 4040 - @dist U m.toDist (σ' t') z' := by linarith
  obtain ⟨h, hh, hsmall⟩ := exists_between
    (lt_min ht.1 (lt_min (sub_pos.mpr ht.2) hgap))
  have hleft : h ≤ t := (hsmall.trans_le (min_le_left _ _)).le
  have hright : t + h ≤ A := by
    have h := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hsum : @dist U m.toDist (σ' t') z' + h < 10191 * R / 4040 := by
    have h := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  let _lcb := @IsOpen.locallyCompactSpace U m.toUniformSpace.toTopologicalSpace hlocally
      (@ball U m.toPseudoMetricSpace z' (129 * R / 20)) (@isOpen_ball U m.toPseudoMetricSpace _ _)
  obtain ⟨τ, hτ, hτ0, hτend, _⟩ :=
    @exists_isometric_segment_in_closedBall_of_half_perimeter_lt U m hcurvesU z'
      (129 * R / 20) _lcb hc (σ' t') z' (by
        rw [@dist_self U m.toPseudoMetricSpace]
        linarith)
  have hmid := @cosh_midpoint_le_of_endpoint_comparison U m κ A (10191 * R / 4040) t h
    hκ hA σ' hσiso t'.property hh hleft hright z' hcmp hsum τ hτ hτ0 hτend (hlocal (σ' t'))
  have hminus : t - h ∈ Icc (0 : ℝ) A := ⟨by linarith, by linarith [ht.2]⟩
  have hplus : t + h ∈ Icc (0 : ℝ) A := ⟨by linarith [ht.1], hright⟩
  rw [IccExtend_of_mem hA σ' hminus, IccExtend_of_mem hA σ' hplus,
    hdist_eq, hdist_eq, hdist_eq] at hmid
  refine ⟨h, hh, hleft, hright, ?_⟩
  rw [IccExtend_of_mem hA σ hminus, IccExtend_of_mem hA σ hplus,
    IccExtend_of_mem hA σ t'.property]
  exact hmid

end DifferentialGeometry.Geometry.Comparison.Toponogov
