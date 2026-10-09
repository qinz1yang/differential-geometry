import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraph
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphStationarity

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology
namespace DifferentialGeometry.Analysis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_sub_affine_projection_le_of_isMinOn_buffered_normal_graph
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : DifferentiableOn ℝ g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t))
    (z y : H) (hz : z ∈ ball o R) (hy : y ∈ W)
    (hmin : IsMinOn (fun w => dist z w) W y) :
    ‖y - (o + L.starProjection (z - o))‖ ≤ 3 * a * R := by
  let u : L := L.orthogonalProjectionOnto (z - o)
  let v : Lᗮ := Lᗮ.orthogonalProjectionOnto (z - o)
  have huz : o + orthogonalCoordinateSum L (u, v) = z := by
    change o + (L.starProjection (z - o) + Lᗮ.starProjection (z - o)) = z
    rw [L.starProjection_add_starProjection_orthogonal]
    abel
  obtain ⟨_, _, t, ht, hyrep⟩ := minimizer_mem_buffered_normal_graph L o g W R a
    hR ha hvalue hgraph hsheet z y hz hy hmin
  have ht4 : t ∈ ball (0 : L) (4 * R) := by
    have hh : dist t 0 < 5 * R / 2 := ht
    change dist t 0 < 4 * R
    linarith
  have hmin' : IsMinOn (fun w => dist (o + orthogonalCoordinateSum L (u, v)) w)
      W (o + orthogonalCoordinateSum L (t, g t)) := by
    rw [huz, ← hyrep]
    exact hmin
  have hstation := normal_equation_of_isMinOn_normal_graph L o g (ball 0 (4 * R))
    W u t v (isOpen_ball.mem_nhds ht4)
    (hg.differentiableAt (isOpen_ball.mem_nhds ht4)) hgraph hmin'
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hfirst t ht4)
  have hv : ‖v‖ ≤ R :=
    (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans
      (by simpa only [mem_ball, dist_eq_norm] using (show dist z o < R from hz).le)
  have hres : ‖g t - v‖ ≤ (a + 1) * R := by
    calc
      ‖g t - v‖ ≤ ‖g t‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ a * R + R := add_le_add (hvalue t ht4) hv
      _ = (a + 1) * R := by ring
  have htu : ‖t - u‖ ≤ a * ((a + 1) * R) := by
    rw [eq_neg_of_add_eq_zero_left hstation, norm_neg]
    calc
      ‖(ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v)‖ ≤
          ‖ContinuousLinearMap.adjoint (fderiv ℝ g t)‖ * ‖g t - v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g t‖ * ‖g t - v‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ a * ((a + 1) * R) := mul_le_mul (hfirst t ht4) hres (norm_nonneg _) ha0
  have heq : y - (o + L.starProjection (z - o)) =
      ((t - u : L) : H) + (g t : H) := by
    rw [hyrep]
    change (o + ((t : H) + (g t : H))) - (o + (u : H)) =
      ((t : H) - (u : H)) + (g t : H)
    abel
  rw [heq]
  calc
    ‖((t - u : L) : H) + (g t : H)‖ ≤ ‖t - u‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ a * ((a + 1) * R) + a * R := add_le_add htu (hvalue t ht4)
    _ ≤ 3 * a * R := by
      nlinarith [mul_le_mul_of_nonneg_right (show a ≤ 1 by linarith)
        (mul_nonneg ha0 hR.le)]

end DifferentialGeometry.Analysis
