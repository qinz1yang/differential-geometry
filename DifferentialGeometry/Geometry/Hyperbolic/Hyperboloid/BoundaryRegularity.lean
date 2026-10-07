import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryDiskControl
import DifferentialGeometry.Analysis.Complex.DirectionalRegularity

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "H3" => Hyperboloid E3

private theorem distortion_bounds_mono {f : H3 → H3} {L₀ C₀ L C : ℝ}
    (hL₀ : 0 < L₀) (hL : L₀ ≤ L) (hC : C₀ ≤ C)
    (hf : ∀ x y : H3, L₀⁻¹ * dist x y - C₀ ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ L₀ * dist x y + C₀) (x y : H3) :
    L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C := by
  have hinv : L⁻¹ ≤ L₀⁻¹ := (inv_le_inv₀ (hL₀.trans_le hL) hL₀).mpr hL
  refine ⟨?_, ?_⟩
  · exact (sub_le_sub (mul_le_mul_of_nonneg_right hinv dist_nonneg) hC).trans (hf x y).1
  · exact (hf x y).2.trans (add_le_add (mul_le_mul_of_nonneg_right hL dist_nonneg) hC)

variable (f g : C(H3, H3))
  (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
    L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
  (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
    L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
  (hgf : ∃ C : ℝ, ∀ x : H3, dist (g (f x)) x ≤ C)
  (hfg : ∃ C : ℝ, ∀ x : H3, dist (f (g x)) x ≤ C)
  (hnorth : boundaryMap f hf sphereNorthPole = sphereNorthPole)

private theorem exists_boundaryPlaneHomeomorph_disk_bounds :
    ∃ κ : ℝ, ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth z) ρ ⊆
        (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth) '' Metric.ball z r ∧
      (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth) '' Metric.closedBall z r ⊆
        Metric.closedBall (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth z) R ∧ R ≤ κ * ρ := by
  obtain ⟨Lf, Cf, hLf, hCf, hfxy⟩ := hf
  obtain ⟨Lg, Cg, hLg, hCg, hgxy⟩ := hg
  let L := max Lf Lg
  let C := max Cf Cg
  have hL : 1 ≤ L := hLf.trans (le_max_left _ _)
  have hC : 0 ≤ C := hCf.trans (le_max_left _ _)
  have hf' (x y : H3) : L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ L * dist x y + C :=
    distortion_bounds_mono (zero_lt_one.trans_le hLf) (le_max_left _ _) (le_max_left _ _) hfxy x y
  have hg' (x y : H3) : L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧
      dist (g x) (g y) ≤ L * dist x y + C :=
    distortion_bounds_mono (zero_lt_one.trans_le hLg) (le_max_right _ _) (le_max_right _ _) hgxy x y
  obtain ⟨κ, _, hdisk⟩ := exists_boundaryPlaneHomeomorph_disk_inclusions L C hL hC
  refine ⟨κ, ?_⟩
  intro z r hr
  obtain ⟨ρ, R, hρ, _, hin, hout, hratio⟩ := hdisk f g hf' hg' hgf hfg hnorth z r hr
  exact ⟨ρ, R, hρ, hin, hout, hratio⟩

theorem ae_lineDifferentiableAt_boundaryPlaneHomeomorph (v : ℂ) :
    ∀ᵐ z : ℂ ∂MeasureTheory.volume,
      LineDifferentiableAt ℝ (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth) z v := by
  obtain ⟨κ, hdisk⟩ := exists_boundaryPlaneHomeomorph_disk_bounds f g hf hg hgf hfg hnorth
  exact (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth).ae_lineDifferentiableAt κ hdisk v

theorem volume_pos_rational_lineDifferentiableAt_and_lineDeriv_ne_zero_boundaryPlaneHomeomorph
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    let h := boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth
    let S := {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
      (∀ p q : ℚ, LineDifferentiableAt ℝ h z
        (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)) ∧
      lineDeriv ℝ h z (1 : ℂ) ≠ 0}
    MeasurableSet S ∧ 0 < MeasureTheory.volume S := by
  obtain ⟨κ, hdisk⟩ := exists_boundaryPlaneHomeomorph_disk_bounds f g hf hg hgf hfg hnorth
  exact Homeomorph.volume_pos_rational_lineDifferentiableAt_and_lineDeriv_ne_zero
    (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth) κ hdisk a b c d hab hcd

end DifferentialGeometry.Hyperboloid
