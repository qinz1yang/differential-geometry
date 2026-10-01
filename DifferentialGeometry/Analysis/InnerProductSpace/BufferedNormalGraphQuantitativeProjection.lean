import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphProjection
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphValue
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphRank

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_contDiffOn_unique_nearest_buffered_normal_graph_with_bounds
    (L : Submodule ℝ H) [FiniteDimensional ℝ L]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ (m + 1 : ℕ) g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t)) :
    ∃ P : H → H, ContDiffOn ℝ m P (ball o R) ∧
      ∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun y => dist z y) W (P z) ∧
        (∀ y ∈ W, IsMinOn (fun w => dist z w) W y → y = P z) ∧
        ‖P z - (o + L.starProjection (z - o))‖ ≤ 3 * a * R ∧
        ‖fderiv ℝ P z - L.starProjection‖ ≤ 7 * a ∧
        Module.finrank ℝ (LinearMap.range (fderiv ℝ P z).toLinearMap) =
          Module.finrank ℝ L := by
  obtain ⟨P, hP, hmin⟩ := exists_contDiffOn_unique_nearest_buffered_normal_graph
    L o g W R a m hm hR ha hg hvalue hfirst hsecond hgraph hsheet
  have hg2 : ContDiffOn ℝ 2 g (ball 0 (4 * R)) := hg.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hgd : DifferentiableOn ℝ g (ball 0 (4 * R)) := hg2.differentiableOn (by norm_num)
  have hm0 : (m : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  refine ⟨P, hP, ?_⟩
  intro z hz
  have hzmin := hmin z hz
  refine ⟨hzmin.1, hzmin.2.1, hzmin.2.2, ?_, ?_, ?_⟩
  · exact norm_sub_affine_projection_le_of_isMinOn_buffered_normal_graph L o g W R a
      hR ha hgd hvalue hfirst hgraph hsheet z (P z) hz hzmin.1 hzmin.2.1
  · exact norm_fderiv_nearest_map_sub_starProjection_le L o g W P R a hR ha hg2
      hvalue hfirst hsecond hgraph hsheet (fun y hy => ⟨(hmin y hy).1, (hmin y hy).2.1⟩)
      z hz ((hP.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt hm0)
  · exact finrank_range_fderiv_nearest_map_eq L o g W P R a hR ha hg2
      hvalue hfirst hsecond hgraph hsheet (fun y hy => ⟨(hmin y hy).1, (hmin y hy).2.1⟩)
      z hz ((hP.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt hm0)

theorem exists_smooth_unique_nearest_buffered_normal_graph_with_bounds
    (L : Submodule ℝ H) [FiniteDimensional ℝ L]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ ∞ g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t)) :
    ∃ P : H → H, ContDiffOn ℝ ∞ P (ball o R) ∧
      ∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun y => dist z y) W (P z) ∧
        (∀ y ∈ W, IsMinOn (fun w => dist z w) W y → y = P z) ∧
        ‖P z - (o + L.starProjection (z - o))‖ ≤ 3 * a * R ∧
        ‖fderiv ℝ P z - L.starProjection‖ ≤ 7 * a ∧
        Module.finrank ℝ (LinearMap.range (fderiv ℝ P z).toLinearMap) =
          Module.finrank ℝ L := by
  obtain ⟨P, hP, hmin⟩ := exists_smooth_unique_nearest_buffered_normal_graph
    L o g W R a hR ha hg hvalue hfirst hsecond hgraph hsheet
  have hg2 : ContDiffOn ℝ 2 g (ball 0 (4 * R)) := hg.of_le (by simp)
  have hgd : DifferentiableOn ℝ g (ball 0 (4 * R)) := hg2.differentiableOn (by norm_num)
  refine ⟨P, hP, ?_⟩
  intro z hz
  have hzmin := hmin z hz
  refine ⟨hzmin.1, hzmin.2.1, hzmin.2.2, ?_, ?_, ?_⟩
  · exact norm_sub_affine_projection_le_of_isMinOn_buffered_normal_graph L o g W R a
      hR ha hgd hvalue hfirst hgraph hsheet z (P z) hz hzmin.1 hzmin.2.1
  · exact norm_fderiv_nearest_map_sub_starProjection_le L o g W P R a hR ha hg2
      hvalue hfirst hsecond hgraph hsheet (fun y hy => ⟨(hmin y hy).1, (hmin y hy).2.1⟩)
      z hz ((hP.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp))
  · exact finrank_range_fderiv_nearest_map_eq L o g W P R a hR ha hg2
      hvalue hfirst hsecond hgraph hsheet (fun y hy => ⟨(hmin y hy).1, (hmin y hy).2.1⟩)
      z hz ((hP.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp))

end DifferentialGeometry.Analysis
