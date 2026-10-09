import DifferentialGeometry.Geometry.Metric.HausdorffRescaling
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphCloudTruncation

set_option autoImplicit false
noncomputable section
open Set Metric

namespace DifferentialGeometry.Analysis

theorem hausdorffEDist_rescaled_normal_graph_truncations_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (T W : Set H) (r b a d ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hd : 0 < d)
    (hab : 2 * a < b) (hdb : 3 * d < b) (hbρ : b < ρ)
    (hgraph : ∀ t : L, ‖t‖ ≤ r * b →
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hheight : ∀ t : L, ‖t‖ ≤ r * b → ‖g t‖ ≤ a * r)
    (hsheet : ∀ w ∈ W ∩ closedBall o (r * b),
      ∃ t : L, w = o + orthogonalCoordinateSum L (t, g t))
    (htest : hausdorffEDist (T ∩ ball o (r * ρ))
      ((AffineSubspace.mk' o L : Set H) ∩ ball o (r * ρ)) ≤ ENNReal.ofReal (d * r)) :
    hausdorffEDist (((fun x => r⁻¹ • (x - o)) '' T) ∩ closedBall 0 b)
        (((fun x => r⁻¹ • (x - o)) '' W) ∩ closedBall 0 b) ≤
        ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) ∧
      hausdorffEDist (((fun x => r⁻¹ • (x - o)) '' T) ∩ ball 0 b)
        (((fun x => r⁻¹ • (x - o)) '' W) ∩ ball 0 b) ≤
        ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) := by
  have har : 2 * (a * r) < r * b := by
    nlinarith [mul_lt_mul_of_pos_left hab hr]
  have hdr : 3 * (d * r) < r * b := by
    nlinarith [mul_lt_mul_of_pos_left hdb hr]
  obtain ⟨hclosed, hopen⟩ := hausdorffEDist_normal_graph_truncations_le_of_affine_test
    L o g T W (r * b) (a * r) (d * r) (r * ρ)
    (mul_pos ha hr) (mul_pos hd hr) har hdr (mul_lt_mul_of_pos_left hbρ hr)
    hgraph hheight hsheet htest
  have hnum : max (d * r + 3 * (a * r)) (a * r + 5 * (d * r)) ≤
      r * max (d + 3 * a) (a + 5 * d) := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left
        (le_max_left (d + 3 * a) (a + 5 * d)) hr.le]
    · nlinarith [mul_le_mul_of_nonneg_left
        (le_max_right (d + 3 * a) (a + 5 * d)) hr.le]
  have hscale : ENNReal.ofReal r⁻¹ *
      ENNReal.ofReal (max (d * r + 3 * (a * r)) (a * r + 5 * (d * r))) ≤
      ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) := by
    calc
      _ ≤ ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r * max (d + 3 * a) (a + 5 * d)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hnum) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), ← mul_assoc,
          inv_mul_cancel₀ hr.ne', one_mul]
  constructor
  · rw [GC.MetricGeometry.hausdorffEDist_rescaled_closedBall o hr]
    exact (mul_le_mul_right hclosed _).trans hscale
  · rw [GC.MetricGeometry.hausdorffEDist_rescaled_ball o hr]
    exact (mul_le_mul_right hopen _).trans hscale

theorem hausdorffEDist_rescaled_normal_graph_truncations_le_of_accuracy_bounds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (T W : Set H) (r ε a d : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10)
    (ha : 0 < a) (haε : a ≤ ε / 8) (hd : 0 < d) (hdε : d ≤ ε / 16)
    (hgraph : ∀ t : L, ‖t‖ ≤ r * ε⁻¹ →
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hheight : ∀ t : L, ‖t‖ ≤ r * ε⁻¹ → ‖g t‖ ≤ a * r)
    (hsheet : ∀ w ∈ W ∩ closedBall o (r * ε⁻¹),
      ∃ t : L, w = o + orthogonalCoordinateSum L (t, g t))
    (htest : hausdorffEDist (T ∩ ball o (r * d⁻¹))
      ((AffineSubspace.mk' o L : Set H) ∩ ball o (r * d⁻¹)) ≤ ENNReal.ofReal (d * r)) :
    hausdorffEDist (((fun x => r⁻¹ • (x - o)) '' T) ∩ closedBall 0 ε⁻¹)
        (((fun x => r⁻¹ • (x - o)) '' W) ∩ closedBall 0 ε⁻¹) ≤
        ENNReal.ofReal (7 * ε / 16) ∧
      hausdorffEDist (((fun x => r⁻¹ • (x - o)) '' T) ∩ ball 0 ε⁻¹)
        (((fun x => r⁻¹ • (x - o)) '' W) ∩ ball 0 ε⁻¹) ≤
        ENNReal.ofReal (7 * ε / 16) := by
  have hinv : 1 < ε⁻¹ := (one_lt_inv₀ hε).mpr (by linarith)
  have hab : 2 * a < ε⁻¹ := by linarith
  have hdb : 3 * d < ε⁻¹ := by linarith
  have htestRadius : ε⁻¹ < d⁻¹ := (inv_lt_inv₀ hε hd).mpr (by linarith)
  obtain ⟨hclosed, hopen⟩ := hausdorffEDist_rescaled_normal_graph_truncations_le
    L o g T W r ε⁻¹ a d d⁻¹ hr ha hd hab hdb htestRadius
    hgraph hheight hsheet htest
  have hbound : max (d + 3 * a) (a + 5 * d) ≤ 7 * ε / 16 := by
    apply max_le <;> linarith
  exact ⟨hclosed.trans (ENNReal.ofReal_le_ofReal hbound),
    hopen.trans (ENNReal.ofReal_le_ofReal hbound)⟩

end DifferentialGeometry.Analysis
