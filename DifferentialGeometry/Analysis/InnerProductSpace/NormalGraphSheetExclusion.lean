import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric
namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem zeroSet_inter_ball_eq_normalGraph_of_error_le
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (η : H → H) (g : L → Lᗮ) (r b : ℝ)
    (hr : 0 < r) (hb : 1 ≤ b)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * b * r),
      η (o + orthogonalCoordinateSum L (t, g t)) = 0)
    (hunique : ∀ t ∈ ball (0 : L) (4 * b * r), ∀ n ∈ closedBall (0 : Lᗮ) r,
      η (o + orthogonalCoordinateSum L (t, n)) = 0 → n = g t)
    (herror : ∀ z ∈ ball o (3 * b * r),
      ‖η z - Lᗮ.starProjection (z - o)‖ ≤ r / 4) :
    {z : H | η z = 0} ∩ ball o (3 * b * r) =
      {z : H | ∃ t ∈ ball (0 : L) (4 * b * r),
        z = o + orthogonalCoordinateSum L (t, g t)} ∩ ball o (3 * b * r) := by
  ext z
  constructor
  · rintro ⟨hz,hball⟩
    let t : L := L.orthogonalProjectionOnto (z - o)
    let n : Lᗮ := Lᗮ.orthogonalProjectionOnto (z - o)
    have ht : t ∈ ball (0 : L) (4 * b * r) := by
      rw [mem_ball, dist_zero_right]
      have hp : ‖t‖ ≤ ‖z - o‖ := L.norm_orthogonalProjectionOnto_apply_le (z - o)
      have hzdist : ‖z - o‖ < 3 * b * r := by simpa only [mem_ball, dist_eq_norm] using hball
      have hbpos : 0 < b := zero_lt_one.trans_le hb
      nlinarith [mul_pos hbpos hr]
    have hn : n ∈ closedBall (0 : Lᗮ) r := by
      rw [mem_closedBall, dist_zero_right]
      have he := herror z hball
      rw [hz, zero_sub, norm_neg] at he
      have hnsmall : ‖n‖ ≤ r / 4 := he
      exact hnsmall.trans (by linarith)
    have hdecomp : o + orthogonalCoordinateSum L (t,n) = z := by
      change o + (L.starProjection (z - o) + Lᗮ.starProjection (z - o)) = z
      rw [L.starProjection_add_starProjection_orthogonal]
      abel
    have hnval : n = g t := hunique t ht n hn (by rw [hdecomp]; exact hz)
    refine ⟨⟨t,ht,?_⟩,hball⟩
    rw [← hnval]
    exact hdecomp.symm
  · rintro ⟨⟨t,ht,rfl⟩,hball⟩
    exact ⟨hgraph t ht,hball⟩

end DifferentialGeometry.Analysis
