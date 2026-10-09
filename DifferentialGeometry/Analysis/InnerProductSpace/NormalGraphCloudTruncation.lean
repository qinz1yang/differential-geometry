import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphTruncation
import DifferentialGeometry.Analysis.InnerProductSpace.AffineProjectionDistance

set_option autoImplicit false
noncomputable section
open Set Metric

namespace DifferentialGeometry.Analysis

theorem hausdorffEDist_normal_graph_truncations_le_of_affine_test
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (T W : Set H) (s a d ρ : ℝ)
    (ha : 0 < a) (hd : 0 < d) (has : 2 * a < s) (hds : 3 * d < s) (hsρ : s < ρ)
    (hgraph : ∀ t : L, ‖t‖ ≤ s →
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hheight : ∀ t : L, ‖t‖ ≤ s → ‖g t‖ ≤ a)
    (hsheet : ∀ w ∈ W ∩ closedBall o s,
      ∃ t : L, w = o + orthogonalCoordinateSum L (t, g t))
    (htest : hausdorffEDist (T ∩ ball o ρ)
      ((AffineSubspace.mk' o L : Set H) ∩ ball o ρ) ≤ ENNReal.ofReal d) :
    hausdorffEDist (T ∩ closedBall o s) (W ∩ closedBall o s) ≤
        ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) ∧
      hausdorffEDist (T ∩ ball o s) (W ∩ ball o s) ≤
        ENNReal.ofReal (max (d + 3 * a) (a + 5 * d)) := by
  apply hausdorffEDist_normal_graph_truncations_le
    L o g T W s a d ha hd has hds hgraph hheight hsheet
  · intro q hq
    have hqtest : q ∈ T ∩ ball o ρ :=
      ⟨hq.1, (show dist q o ≤ s from hq.2).trans_lt hsρ⟩
    have he : infEDist q (AffineSubspace.mk' o L : Set H) ≤ ENNReal.ofReal d :=
      (infEDist_anti inter_subset_left).trans
        ((infEDist_le_hausdorffEDist_of_mem hqtest).trans htest)
    have hreal : infDist q (AffineSubspace.mk' o L : Set H) ≤ d := by
      simpa only [Metric.infDist, ENNReal.toReal_ofReal hd.le] using
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top he)
    rw [← L.norm_sub_starProjection_eq_infDist_affine] at hreal
    exact hreal
  · intro t ht
    have hplane : o + (t : H) ∈ (AffineSubspace.mk' o L : Set H) := by
      change (o + (t : H)) - o ∈ L
      simpa only [add_sub_cancel_left] using t.property
    have hnear : o + (t : H) ∈ ball o ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      change ‖t‖ < ρ
      exact ht.trans_lt hsρ
    have hstrict : ENNReal.ofReal d < ENNReal.ofReal (2 * d) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      linarith
    have hswap : hausdorffEDist
        ((AffineSubspace.mk' o L : Set H) ∩ ball o ρ) (T ∩ ball o ρ) <
          ENNReal.ofReal (2 * d) := by
      rw [hausdorffEDist_comm]
      exact htest.trans_lt hstrict
    have hsource : o + (t : H) ∈ ((AffineSubspace.mk' o L : Set H) ∩ ball o ρ) :=
      ⟨hplane, hnear⟩
    obtain ⟨q, hq, hclose⟩ := exists_edist_lt_of_hausdorffEDist_lt hsource hswap
    exact ⟨q, hq.1, edist_lt_ofReal.mp hclose⟩

end DifferentialGeometry.Analysis
