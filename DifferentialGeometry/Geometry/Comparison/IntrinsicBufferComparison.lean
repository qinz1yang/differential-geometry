import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallLength
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallGeometry
import DifferentialGeometry.Geometry.Comparison.AmbientBufferComparison

set_option autoImplicit false

open Set Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (256 * R))]
variable (hlocal : ∀ z : ball o (256 * R), ∃ Ω : Set (ball o (256 * R)),
  @IsOpen (ball o (256 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (256 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem endpointHingeComparison_intrinsic_256_buffer
    {p : ball o (256 * R)} (hp : (p : X) ∈ ball o (4 * R)) :
    @endpointHingeComparison (ball o (256 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)) κ p (10 * R) := by
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)
  have hc := isComplete_intrinsicBall_closedBall hcurves o
    (by positivity : 0 < 256 * R) p (r := 200 * R) (by
      have hd : dist (p : X) o < 4 * R := hp
      linarith)
  have ht := @endpointHingeComparison_of_complete_interior_buffer (ball o (256 * R))
    m (intrinsicBallMetricSpace_locallyCompact hcurves o (by positivity)) κ hκ
    (fun a b ε hε => intrinsicBallMetricSpace_arbitrarily_short_curves hcurves o
      (by positivity) a b hε) hlocal p (200 * R) hc
  convert ht using 1; ring

theorem fourPointComparison_intrinsic_two_ball_of_256_buffer :
    @fourPointComparison (ball o (256 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)) κ
      (@ball (ball o (256 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)).toPseudoMetricSpace
        ⟨o, by simpa only [mem_ball, dist_self] using (by positivity : 0 < 256 * R)⟩
        (2 * R)) := by
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)
  let p : ball o (256 * R) :=
    ⟨o, by simpa only [mem_ball, dist_self] using (by positivity : 0 < 256 * R)⟩
  have hc := isComplete_intrinsicBall_closedBall hcurves o
    (by positivity : 0 < 256 * R) p (r := 200 * R)
    (by change dist o o + 200 * R < 256 * R; rw [dist_self]; linarith)
  exact @fourPointComparison_ball_of_complete_buffer (ball o (256 * R)) m
    (intrinsicBallMetricSpace_locallyCompact hcurves o (by positivity)) κ hκ
    (fun a b ε hε => intrinsicBallMetricSpace_arbitrarily_short_curves hcurves o
      (by positivity) a b hε) hlocal p (200 * R) (2 * R) (by positivity) hc (by linarith)

theorem fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer :
    fourPointComparison κ (ball o (2 * R)) := by
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)
  let p : ball o (256 * R) :=
    ⟨o, by simpa only [mem_ball, dist_self] using (by positivity : 0 < 256 * R)⟩
  let s := @ball (ball o (256 * R)) m.toPseudoMetricSpace p (2 * R)
  have hLip := intrinsicBallMetricSpace_lipschitzWith_coe hcurves o
    (by positivity : 0 < 256 * R)
  have hmem (a : ball o (256 * R)) (ha : a ∈ s) : (a : X) ∈ closedBall o (2 * R) := by
    have hd := @LipschitzWith.dist_le_mul (ball o (256 * R)) X
      m.toPseudoMetricSpace _ 1 _ hLip a p
    simp only [NNReal.coe_one, one_mul] at hd
    exact (hd.trans_lt ha).le
  have heq := intrinsicBall_ball_image hcurves o (by positivity : 0 < 256 * R)
    (by positivity : 0 < 2 * R) (by linarith : 4 * (2 * R) < 256 * R)
  change (fun y : ball o (256 * R) => (y : X)) '' s = ball o (2 * R) at heq
  rw [← heq]
  apply (@fourPointComparison_image_iff_of_dist_eq X (ball o (256 * R)) _ m κ
    (fun y => (y : X)) s ?_).mpr
  · exact fourPointComparison_intrinsic_two_ball_of_256_buffer hcurves o hκ hR hlocal
  · intro a ha b hb
    exact (intrinsicBall_dist_eq_on_inner_closedBall hcurves o (by positivity)
      (by positivity : 0 < 2 * R)
      (by rw [dist_self]; linarith : dist o o + 4 * (2 * R) < 256 * R)
      (hmem a ha) (hmem b hb)).symm

theorem fourPointComparison_ambient_ball_of_intrinsic_256_buffer :
    fourPointComparison κ (ball o R) :=
  (fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer hcurves o hκ hR hlocal).mono
    (ball_subset_ball (by linarith))

end DifferentialGeometry.Geometry.Comparison.Toponogov
