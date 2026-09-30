import DifferentialGeometry.Topology.MetricSpace.LipschitzBufferCompleteness
import DifferentialGeometry.Geometry.Comparison.MetricTransfer
import DifferentialGeometry.Geometry.Comparison.InteriorBallComparison

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem endpointHingeComparison_of_embedded_256_buffer
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    {f : Y → X} (hf : IsEmbedding f) (hLip : LipschitzWith 1 f)
    {o : X} (hrange : range f = ball o (256 * R))
    (hcurves : ∀ a b : Y, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Y, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : Y, ∃ Ω : Set Y, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {p : Y} (hp : f p ∈ ball o (4 * R)) : endpointHingeComparison κ p (10 * R) := by
  have ht := endpointHingeComparison_of_complete_interior_buffer hκ hcurves hlocal
    (hf.isComplete_closedBall_of_256_radius_buffer hLip hR hrange hp)
  convert ht using 1; ring

theorem fourPointComparison_of_embedded_256_buffer
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    {f : Y → X} (hf : IsEmbedding f) (hLip : LipschitzWith 1 f)
    {o : X} (hrange : range f = ball o (256 * R))
    (hcurves : ∀ a b : Y, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Y, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : Y, ∃ Ω : Set Y, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {p : Y} (hp : f p = o)
    (hdist : ∀ a : Y, f a ∈ ball o (4 * R) → ∀ b : Y, f b ∈ ball o (4 * R) →
      dist (f a) (f b) = dist a b) : fourPointComparison κ (ball o R) := by
  have hcomplete : IsComplete (closedBall p (200 * R)) :=
    hf.isComplete_closedBall_of_256_radius_buffer hLip hR hrange
      (by rw [hp]; simpa only [mem_ball, dist_self] using (by positivity : 0 < 4 * R))
  have hcomp := fourPointComparison_ball_of_complete_buffer hκ hcurves hlocal hR
    hcomplete (by linarith : 81 * R ≤ 200 * R)
  have hmem (y : Y) (hy : y ∈ ball p R) : f y ∈ ball o R := by
    have hd : dist (f y) (f p) ≤ dist y p := by
      simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul y p
    rw [hp] at hd
    exact hd.trans_lt hy
  have hlarge (y : Y) (hy : y ∈ ball p R) : f y ∈ ball o (4 * R) :=
    (show dist (f y) o < R from hmem y hy).trans_le (by linarith)
  have himage : f '' ball p R = ball o R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hmem y hy
    · intro hx
      have hxrange : x ∈ range f := by
        rw [hrange]
        exact (show dist x o < R from hx).trans_le (by linarith)
      obtain ⟨y, rfl⟩ := hxrange
      have hyp := hdist y ((show dist (f y) o < R from hx).trans_le (by linarith)) p
        (by rw [hp]; simpa only [mem_ball, dist_self] using (by positivity : 0 < 4 * R))
      rw [hp] at hyp
      exact ⟨y, by change dist y p < R; rw [← hyp]; exact hx, rfl⟩
  rw [← himage]
  exact (fourPointComparison_image_iff_of_dist_eq
    (fun a ha b hb => hdist a (hlarge a ha) b (hlarge b hb))).mpr hcomp

end DifferentialGeometry.Geometry.Comparison.Toponogov
