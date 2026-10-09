import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section
open Set Metric

namespace DifferentialGeometry.Analysis

private theorem exists_radial_shortening_for_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} {R e : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e) (hv : ‖v‖ ≤ R + e) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖t • v‖ ≤ R ∧ ‖v - t • v‖ ≤ e := by
  by_cases hi : ‖v‖ ≤ R
  · exact ⟨1, by norm_num, le_rfl, by simpa using hi, by simpa using he⟩
  have hpos : 0 < ‖v‖ := by linarith [norm_nonneg v]
  let t := R / ‖v‖
  have ht : 0 ≤ t := div_nonneg hR hpos.le
  have ht1 : t ≤ 1 := (div_le_one hpos).mpr (le_of_lt (lt_of_not_ge hi))
  have hmul : t * ‖v‖ = R := div_mul_cancel₀ R hpos.ne'
  refine ⟨t, ht, ht1, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hmul]
  · have heq : v - t • v = (1 - t) • v := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)]
    nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem normal_graph_truncation_witnesses
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (T W : Set H) (s a d : ℝ)
    (ha : 0 < a) (hd : 0 < d) (has : 2 * a < s) (hds : 3 * d < s)
    (hgraph : ∀ t : L, ‖t‖ ≤ s →
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hheight : ∀ t : L, ‖t‖ ≤ s → ‖g t‖ ≤ a)
    (hsheet : ∀ w ∈ W ∩ closedBall o s,
      ∃ t : L, w = o + orthogonalCoordinateSum L (t, g t))
    (hnormal : ∀ q ∈ T ∩ closedBall o s,
      ‖(q - o) - L.starProjection (q - o)‖ ≤ d)
    (hcloud : ∀ t : L, ‖t‖ ≤ s → ∃ q ∈ T, dist (o + (t : H)) q < 2 * d) :
    (∀ q ∈ T ∩ closedBall o s, ∃ w ∈ W ∩ ball o s, dist q w ≤ d + 3 * a) ∧
      (∀ w ∈ W ∩ closedBall o s, ∃ q ∈ T ∩ ball o s, dist w q < a + 5 * d) := by
  constructor
  · intro q hq
    let t : L := L.orthogonalProjectionOnto (q - o)
    have ht : ‖t‖ ≤ s := (L.norm_orthogonalProjectionOnto_apply_le (q - o)).trans
      (by simpa only [mem_closedBall, dist_eq_norm] using hq.2)
    obtain ⟨c, _hc0, _hc1, hshort, hmove⟩ := exists_radial_shortening_for_graph
      (by linarith : 0 ≤ s - 2 * a) (by positivity : 0 ≤ 2 * a)
      (by linarith : ‖t‖ ≤ (s - 2 * a) + 2 * a)
    let v : L := c • t
    have hv : ‖v‖ ≤ s := by change ‖c • t‖ ≤ s; linarith
    have hvheight := hheight v hv
    have hsum : ‖orthogonalCoordinateSum L (v, g v)‖ ≤ ‖v‖ + a := by
      change ‖(v : H) + (g v : H)‖ ≤ ‖v‖ + a
      refine (norm_add_le _ _).trans ?_
      change ‖v‖ + ‖g v‖ ≤ ‖v‖ + a
      linarith
    have hwball : o + orthogonalCoordinateSum L (v, g v) ∈ ball o s := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      change ‖c • t‖ ≤ s - 2 * a at hshort
      change ‖orthogonalCoordinateSum L (v, g v)‖ ≤ ‖c • t‖ + a at hsum
      linarith
    refine ⟨o + orthogonalCoordinateSum L (v, g v), ⟨hgraph v hv, hwball⟩, ?_⟩
    have hqt : dist q (o + (t : H)) ≤ d := by
      rw [dist_eq_norm]
      change ‖q - (o + L.starProjection (q - o))‖ ≤ d
      simpa only [sub_add_eq_sub_sub] using hnormal q hq
    have htv : dist (o + (t : H)) (o + (v : H)) ≤ 2 * a := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub]
      exact hmove
    have hvg : dist (o + (v : H))
        (o + orthogonalCoordinateSum L (v, g v)) ≤ a := by
      rw [dist_eq_norm]
      have heq : (o + (v : H)) - (o + orthogonalCoordinateSum L (v, g v)) =
          -(g v : H) := by
        change (o + (v : H)) - (o + ((v : H) + (g v : H))) = _
        abel
      rw [heq, norm_neg]
      exact hvheight
    have h1 := dist_triangle q (o + (t : H)) (o + (v : H))
    have h2 := dist_triangle q (o + (v : H))
      (o + orthogonalCoordinateSum L (v, g v))
    linarith
  · intro w hw
    obtain ⟨t, ht⟩ := hsheet w hw
    have hdecomp : w - o = (t : H) + (g t : H) := by
      rw [ht]
      change (o + ((t : H) + (g t : H))) - o = _
      abel
    have hproj : L.orthogonalProjectionOnto (w - o) = t := by
      rw [hdecomp, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property, add_zero]
    have htnorm : ‖t‖ ≤ s := by
      have hh := L.norm_orthogonalProjectionOnto_apply_le (w - o)
      rw [hproj] at hh
      exact hh.trans (by simpa only [mem_closedBall, dist_eq_norm] using hw.2)
    have htheight := hheight t htnorm
    obtain ⟨c, _hc0, _hc1, hshort, hmove⟩ := exists_radial_shortening_for_graph
      (by linarith : 0 ≤ s - 3 * d) (by positivity : 0 ≤ 3 * d)
      (by linarith : ‖t‖ ≤ (s - 3 * d) + 3 * d)
    let v : L := c • t
    have hv : ‖v‖ ≤ s := by change ‖c • t‖ ≤ s; linarith
    obtain ⟨q, hq, hqclose⟩ := hcloud v hv
    have hvcenter : dist (o + (v : H)) o ≤ s - 3 * d := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hshort
    have hqball : q ∈ ball o s := by
      have hh := dist_triangle q (o + (v : H)) o
      rw [dist_comm q (o + (v : H))] at hh
      change dist q o < s
      linarith
    refine ⟨q, ⟨hq, hqball⟩, ?_⟩
    have hwt : dist w (o + (t : H)) ≤ a := by
      rw [ht, dist_eq_norm]
      have heq : (o + orthogonalCoordinateSum L (t, g t)) - (o + (t : H)) =
          (g t : H) := by
        change (o + ((t : H) + (g t : H))) - (o + (t : H)) = _
        abel
      rw [heq]
      exact htheight
    have htv : dist (o + (t : H)) (o + (v : H)) ≤ 3 * d := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub]
      exact hmove
    have h1 := dist_triangle w (o + (t : H)) (o + (v : H))
    have h2 := dist_triangle w (o + (v : H)) q
    linarith

theorem hausdorffEDist_normal_graph_truncations_le
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (T W : Set H) (s a d : ℝ)
    (ha : 0 < a) (hd : 0 < d) (has : 2 * a < s) (hds : 3 * d < s)
    (hgraph : ∀ t : L, ‖t‖ ≤ s →
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hheight : ∀ t : L, ‖t‖ ≤ s → ‖g t‖ ≤ a)
    (hsheet : ∀ w ∈ W ∩ closedBall o s,
      ∃ t : L, w = o + orthogonalCoordinateSum L (t, g t))
    (hnormal : ∀ q ∈ T ∩ closedBall o s,
      ‖(q - o) - L.starProjection (q - o)‖ ≤ d)
    (hcloud : ∀ t : L, ‖t‖ ≤ s → ∃ q ∈ T, dist (o + (t : H)) q < 2 * d) :
    hausdorffEDist (T ∩ closedBall o s) (W ∩ closedBall o s) ≤
        ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) ∧
      hausdorffEDist (T ∩ ball o s) (W ∩ ball o s) ≤
        ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) := by
  obtain ⟨hforward, hbackward⟩ := normal_graph_truncation_witnesses
    L o g T W s a d ha hd has hds hgraph hheight hsheet hnormal hcloud
  constructor
  · apply hausdorffEDist_le_of_mem_edist
    · intro q hq
      obtain ⟨w, hw, hdist⟩ := hforward q hq
      refine ⟨w, ⟨hw.1, ball_subset_closedBall hw.2⟩, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist.trans (le_max_left _ _))
    · intro w hw
      obtain ⟨q, hq, hdist⟩ := hbackward w hw
      refine ⟨q, ⟨hq.1, ball_subset_closedBall hq.2⟩, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist.le.trans (le_max_right _ _))
  · apply hausdorffEDist_le_of_mem_edist
    · intro q hq
      obtain ⟨w, hw, hdist⟩ := hforward q ⟨hq.1, ball_subset_closedBall hq.2⟩
      refine ⟨w, hw, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist.trans (le_max_left _ _))
    · intro w hw
      obtain ⟨q, hq, hdist⟩ := hbackward w ⟨hw.1, ball_subset_closedBall hw.2⟩
      refine ⟨q, hq, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist.le.trans (le_max_right _ _))

end DifferentialGeometry.Analysis
