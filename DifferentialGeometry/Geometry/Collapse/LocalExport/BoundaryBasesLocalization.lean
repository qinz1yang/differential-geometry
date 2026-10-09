import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageRank

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 1): ratio pieces and the marker route to
whole-preimage localization

The BASES bases of the boundary chain are the relatively open ratio sets
`O_st = ⋃_i {v_i > .9R_i, R_i‖κ_i‖ < 3.9 ℓ_i v_i}` of `H^∂` (closed GAF07 shape with the ratio `4`
replaced by `3.9`, so that the whole-preimage localization lands strictly inside the original
threshold-`4.01` domains). This file proves the generic localization arithmetic and its chain
instances for the circle stage:

* `ratioPiece_BBP κ v R ℓ`, `isOpen_ratioPiece_BBP`;
* `ratio_arith_BBP`, `loc_of_piece_BBP`, `piece_of_orig_BBP` (a final value `y` with `‖y − z‖ ≤ R/400`
  against the clean value `z` with `v z = Rζ`, `‖κ z‖ = ζ a`);
* chain level (any marker `m`): `final_err_le_BBP` (`ζ_m(p) > 0 ⟹ ‖E p − F_∂ p‖ ≤ ρ_m/400`),
  `final_marker_pos_BBP` (`v_m(E p) > .9ρ_m ⟹ ζ_m(p) > 0`, through the retained marker `(AM0)`);
* circle: `circle_final_loc_BBP` (`f₀(p) ∈ piece_j ⟹ p` in the chart domain with `‖η_j‖ < 4.01`),
  `circle_orig_piece_BBP` (`‖η_j‖ ≤ 3.5` in the chart domain `⟹ f₀(p) ∈ piece_j`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Generic

variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The ratio piece `{v > .9R, R‖κ‖ < 3.9 ℓ v}` of a marked chart (`κ = R⁻¹u`, `v` the marker). -/
def ratioPiece_BBP (κ : H →L[ℝ] F) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) : Set H :=
  {y | 9 / 10 * R < v y ∧ R * ‖κ y‖ < 39 / 10 * ℓ * v y}

theorem isOpen_ratioPiece_BBP (κ : H →L[ℝ] F) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) :
    IsOpen (ratioPiece_BBP κ v R ℓ) :=
  (isOpen_lt continuous_const v.continuous).inter
    (isOpen_lt (continuous_const.mul (continuous_norm.comp κ.continuous))
      (continuous_const.mul v.continuous))

/-- The localization arithmetic: values `vy`, `uy` within `δ ≤ ρ/400` of `ρζ`, `ρζa` and in the
ratio piece force `ζ > .897` and `a < 4.01ℓ`. -/
theorem ratio_arith_BBP {ρ ζ ℓ a δ vy uy : ℝ} (hρ : 0 < ρ) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ ρ / 400) (hv : |vy - ρ * ζ| ≤ δ) (hu : |uy - ρ * ζ * a| ≤ δ)
    (h9 : 9 / 10 * ρ < vy) (hr : uy < 39 / 10 * ℓ * vy) :
    897 / 1000 < ζ ∧ a < 401 / 100 * ℓ := by
  obtain ⟨hv1, hv2⟩ := abs_le.mp hv
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  have hP : 897 / 1000 * ρ < ρ * ζ := by linarith
  have hζ0 : 897 / 1000 < ζ := lt_of_mul_lt_mul_left (by linarith : ρ * (897 / 1000) < ρ * ζ) hρ.le
  refine ⟨hζ0, ?_⟩
  by_contra hn
  have hn' : 401 / 100 * ℓ ≤ a := not_lt.mp hn
  have h1 : ρ * ζ * (401 / 100 * ℓ) ≤ ρ * ζ * a :=
    mul_le_mul_of_nonneg_left hn' (by linarith)
  have h2 : ℓ * vy ≤ ℓ * (ρ * ζ + δ) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : ℓ * δ ≤ ℓ * (ρ / 400) := mul_le_mul_of_nonneg_left hδ (by linarith)
  have h4 : 897 / 1000 * ρ * ℓ ≤ ρ * ζ * ℓ := mul_le_mul_of_nonneg_right hP.le (by linarith)
  have h5 : 0 ≤ ρ * ℓ := by positivity
  nlinarith

/-- **Localization from a piece**: a value `y` of the final map in the ratio piece, at distance
`≤ R/400` from the clean value `z` (`v z = Rζ`, `‖κ z‖ = ζ a`), has `ζ > 0` and `a < 4.01ℓ`. -/
theorem loc_of_piece_BBP {κ : H →L[ℝ] F} {v : H →L[ℝ] ℝ} {R ℓ ζ a : ℝ} (hR : 0 < R)
    (hℓ : 1 ≤ ℓ) (hκ : ‖κ‖ ≤ R⁻¹) (hv1 : ‖v‖ ≤ 1) {y z : H}
    (hyz : ‖y - z‖ ≤ R / 400) (hzv : v z = R * ζ) (hzk : ‖κ z‖ = ζ * a)
    (hy : y ∈ ratioPiece_BBP κ v R ℓ) : 897 / 1000 < ζ ∧ a < 401 / 100 * ℓ := by
  have hv : |v y - R * ζ| ≤ R / 400 := by
    rw [← hzv, ← map_sub]
    exact (v.le_opNorm _).trans (by nlinarith [norm_nonneg (y - z)])
  have hu : |R * ‖κ y‖ - R * ζ * a| ≤ R / 400 := by
    have e : R * ζ * a = R * ‖κ z‖ := by rw [hzk]; ring
    rw [e, ← mul_sub]
    have h1 : |‖κ y‖ - ‖κ z‖| ≤ ‖κ (y - z)‖ := by
      rw [map_sub]
      exact abs_norm_sub_norm_le _ _
    have h2 : ‖κ (y - z)‖ ≤ R⁻¹ * (R / 400) :=
      (κ.le_opNorm _).trans (mul_le_mul hκ hyz (norm_nonneg _) (inv_nonneg.mpr hR.le))
    rw [abs_mul, abs_of_pos hR]
    calc R * |‖κ y‖ - ‖κ z‖| ≤ R * (R⁻¹ * (R / 400)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hR.le
      _ = R / 400 := by field_simp
  exact ratio_arith_BBP hR hℓ le_rfl hv hu hy.1 hy.2

/-- **Original points lie in the piece**: `ζ = 1`, `a ≤ 3.5ℓ` and the final value within `R/400` of
the clean value put the final value in the ratio piece. -/
theorem piece_of_orig_BBP {κ : H →L[ℝ] F} {v : H →L[ℝ] ℝ} {R ℓ a : ℝ} (hR : 0 < R)
    (hℓ : 1 ≤ ℓ) (hκ : ‖κ‖ ≤ R⁻¹) (hv1 : ‖v‖ ≤ 1) {y z : H} (hyz : ‖y - z‖ ≤ R / 400)
    (hzv : v z = R * 1) (hzk : ‖κ z‖ = 1 * a) (ha : a ≤ 7 / 2 * ℓ) :
    y ∈ ratioPiece_BBP κ v R ℓ := by
  have hv : |v y - R * 1| ≤ R / 400 := by
    rw [← hzv, ← map_sub]
    exact (v.le_opNorm _).trans (by nlinarith [norm_nonneg (y - z)])
  have hk : |‖κ y‖ - ‖κ z‖| ≤ R⁻¹ * (R / 400) := by
    have h1 : |‖κ y‖ - ‖κ z‖| ≤ ‖κ (y - z)‖ := by
      rw [map_sub]
      exact abs_norm_sub_norm_le _ _
    exact h1.trans ((κ.le_opNorm _).trans
      (mul_le_mul hκ hyz (norm_nonneg _) (inv_nonneg.mpr hR.le)))
  have hRR : R⁻¹ * (R / 400) = 1 / 400 := by field_simp
  rw [hRR] at hk
  obtain ⟨hv1', hv2'⟩ := abs_le.mp hv
  obtain ⟨hk1, hk2⟩ := abs_le.mp hk
  rw [hzk] at hk1 hk2
  refine ⟨by linarith, ?_⟩
  have h3 : R * ‖κ y‖ ≤ R * (1 * a + 1 / 400) := mul_le_mul_of_nonneg_left (by linarith) hR.le
  have h4 : ℓ * (R * 399 / 400) ≤ ℓ * v y :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h6 : R * a ≤ R * (7 / 2 * ℓ) := mul_le_mul_of_nonneg_left ha hR.le
  have h7 : R * 1 ≤ R * ℓ := mul_le_mul_of_nonneg_left hℓ hR.le
  nlinarith

end Generic

end DifferentialGeometry.Geometry.Collapse
