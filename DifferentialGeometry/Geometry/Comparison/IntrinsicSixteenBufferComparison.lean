import DifferentialGeometry.Geometry.Comparison.BudgetInteriorComparison
import DifferentialGeometry.Geometry.Comparison.RegionFourPoint
import DifferentialGeometry.Geometry.Comparison.MetricTransfer
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallLength
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallGeometry

set_option autoImplicit false


open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison_ball_of_complete_vertex_budget_buffers
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {o : X} {L R : ℝ} (hR : 0 < R)
    (hcomplete : ∀ p ∈ ball o R, IsComplete (closedBall p L))
    (hbuffer : 44 * R ≤ 3 * L) : fourPointComparison κ (ball o R) := by
  apply fourPointComparison_of_endpoint_hinges (T := 4 * R) hκ
  · intro x hx y hy
    obtain ⟨σ, hσ, hσ0, hσ1, _⟩ :=
      exists_isometric_segment_in_ball_of_recentered_complete_buffer
        hcurves hR (hcomplete o (by simpa only [mem_ball, dist_self] using hR))
        (by rw [dist_self]; linarith) hx hy
    exact ⟨σ, hσ, hσ0, hσ1⟩
  · intro z hz
    exact hlocal z
  · intro p hp
    exact (endpointHingeComparison_of_complete_budget_buffer hκ hcurves hlocal
      (hcomplete p hp)).mono (by linarith)
  · intro x hx a ha b hb
    have hxa := dist_triangle x o a
    have hxb := dist_triangle x o b
    rw [dist_comm o a] at hxa
    rw [dist_comm o b] at hxb
    have hx' : dist x o < R := hx
    have ha' : dist a o < R := ha
    have hb' : dist b o < R := hb
    linarith

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (16 * R))]
variable (hlocal : ∀ z : ball o (16 * R), ∃ Ω : Set (ball o (16 * R)),
  @IsOpen (ball o (16 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (16 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem endpointHingeComparison_intrinsic_16_buffer
    {p : ball o (16 * R)} (hp : (p : X) ∈ ball o R) :
    @endpointHingeComparison (ball o (16 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)) κ p (45 * R / 11) := by
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)
  have hc := isComplete_intrinsicBall_closedBall hcurves o
    (by positivity : 0 < 16 * R) p (r := 15 * R) (by
      have hd : dist (p : X) o < R := hp
      linarith)
  have ht := @endpointHingeComparison_of_complete_budget_buffer (ball o (16 * R))
    m (intrinsicBallMetricSpace_locallyCompact hcurves o (by positivity)) κ hκ
    (fun a b ε hε => intrinsicBallMetricSpace_arbitrarily_short_curves hcurves o
      (by positivity) a b hε) hlocal p (15 * R) hc
  convert ht using 1; ring

theorem fourPointComparison_intrinsic_ball_of_16_buffer :
    @fourPointComparison (ball o (16 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)) κ
      (@ball (ball o (16 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)).toPseudoMetricSpace
        ⟨o, by simpa only [mem_ball, dist_self] using (by positivity : 0 < 16 * R)⟩ R) := by
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)
  let p : ball o (16 * R) :=
    ⟨o, by simpa only [mem_ball, dist_self] using (by positivity : 0 < 16 * R)⟩
  have hLip := intrinsicBallMetricSpace_lipschitzWith_coe hcurves o
    (by positivity : 0 < 16 * R)
  have hc : ∀ a ∈ @ball (ball o (16 * R)) m.toPseudoMetricSpace p R,
      @IsComplete (ball o (16 * R)) m.toUniformSpace
        (@closedBall (ball o (16 * R)) m.toPseudoMetricSpace a (15 * R)) := by
    intro a ha
    have hd := @LipschitzWith.dist_le_mul (ball o (16 * R)) X
      m.toPseudoMetricSpace _ 1 _ hLip a p
    simp only [NNReal.coe_one, one_mul] at hd
    have ha' : dist (a : X) o < R := hd.trans_lt ha
    exact isComplete_intrinsicBall_closedBall hcurves o (by positivity) a (by linarith)
  exact @fourPointComparison_ball_of_complete_vertex_budget_buffers (ball o (16 * R)) m
    (intrinsicBallMetricSpace_locallyCompact hcurves o (by positivity)) κ hκ
    (fun a b ε hε => intrinsicBallMetricSpace_arbitrarily_short_curves hcurves o
      (by positivity) a b hε) hlocal p (15 * R) R hR hc (by linarith)

theorem fourPointComparison_ambient_ball_of_intrinsic_16_buffer :
    fourPointComparison κ (ball o R) := by
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 16 * R)
  let p : ball o (16 * R) :=
    ⟨o, by simpa only [mem_ball, dist_self] using (by positivity : 0 < 16 * R)⟩
  let s := @ball (ball o (16 * R)) m.toPseudoMetricSpace p R
  have hLip := intrinsicBallMetricSpace_lipschitzWith_coe hcurves o
    (by positivity : 0 < 16 * R)
  have hmem (a : ball o (16 * R)) (ha : a ∈ s) : (a : X) ∈ closedBall o R := by
    have hd := @LipschitzWith.dist_le_mul (ball o (16 * R)) X
      m.toPseudoMetricSpace _ 1 _ hLip a p
    simp only [NNReal.coe_one, one_mul] at hd
    exact (hd.trans_lt ha).le
  have heq := intrinsicBall_ball_image hcurves o (by positivity : 0 < 16 * R)
    hR (by linarith : 4 * R < 16 * R)
  change (fun y : ball o (16 * R) => (y : X)) '' s = ball o R at heq
  rw [← heq]
  apply (@fourPointComparison_image_iff_of_dist_eq X (ball o (16 * R)) _ m κ
    (fun y => (y : X)) s ?_).mpr
  · exact fourPointComparison_intrinsic_ball_of_16_buffer hcurves o hκ hR hlocal
  · intro a ha b hb
    exact (intrinsicBall_dist_eq_on_inner_closedBall hcurves o (by positivity) hR
      (by rw [dist_self]; linarith : dist o o + 4 * R < 16 * R)
      (hmem a ha) (hmem b hb)).symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
