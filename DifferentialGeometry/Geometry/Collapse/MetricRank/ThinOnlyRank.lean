import DifferentialGeometry.Geometry.Collapse.MetricRank.ApproxRankWiring
import DifferentialGeometry.Geometry.Collapse.MetricRank.SplittingOfThinProduct

/-!
# Rank exactness from the thin product approximation alone (S-X144c, group G10)

`ApproxRankWiring` (S-X144b, G7) concludes `scaledSplittingRank = 1` (line) / `= 2` (plane) from a
thin product approximation *and* an explicit splitting `h1` / `h2`. Here the splitting is derived
from the approximation itself (`SplittingOfThinProduct`: translation, the isometry
`prodCongrLeft_SMR`, and the relaxation `2 δ ≤ β k < 1` of group G9), so the only inputs are

* `f` : a Kleiner-Lott `δ`-approximation of the rescaled metric into `A ×₂ Z`
  (`A = ℝ` for the line, `A = ℝ²` for the plane) at the base point `p ↦ (a, z)`;
* `hZ`, `hε` : the thin factor, `dist ≤ D` and `δ + D ≤ 1/100` (as in G7);
* the register: `β 2, β 3 ≤ 3/20`, and `2 δ ≤ β k < 1` for the rank `k` to be realised
  (`k = 1` for the line, `k = 2` for the plane).

Since `δ + D ≤ 1/100` and `D ≥ 0` force `δ ≤ 1/100`, the condition `2 δ ≤ β k` holds for every
register with `1/50 ≤ β k` (`…_of_hundredth_SMR`), independently of `δ`.

Universes: the factor `Z : Type w` of the approximation is the factor of the splitting, so the
rank is `scaledSplittingRank.{u, w}`.

Names: the statements with an explicit `h1`/`h2` keep their names in `ApproxRankWiring`; these
are `…_only_SMR` (the name `…_of_thin_only_SMR` of the brief, with the shape inserted).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u w

section RankLevel

variable {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}
  {Z : Type w} [MetricSpace Z] {z : Z} {δ D : ℝ}

/-- **Thin line, rank exactly one, no `h1`.** -/
theorem scaledSplittingRank_eq_one_of_thin_line_only_SMR {a : ℝ}
    (f : @KleinerLottApprox M (WithLp 2 (ℝ × Z)) (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
      (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₁ : 2 * δ ≤ β 1) (hβ₁1 : β 1 < 1) (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, w} ρ hρ β p = 1 :=
  scaledSplittingRank_eq_one_of_thin_line_SMR f hZ hε
    (@exists_splitting_of_thin_product_line_SMR M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p δ
      (β 1) Z _ z a f hβ₁ hβ₁1) hβ₂ hβ₃

/-- **Thin plane, rank exactly two, no `h2`.** -/
theorem scaledSplittingRank_eq_two_of_thin_plane_only_SMR {a : EuclideanSpace ℝ (Fin 2)}
    (f : @KleinerLottApprox M (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z))
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₂ : 2 * δ ≤ β 2) (hβ₂1 : β 2 < 1) (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, w} ρ hρ β p = 2 :=
  scaledSplittingRank_eq_two_of_thin_plane_SMR f hZ hε
    (@exists_splitting_of_thin_product_plane_SMR M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p δ
      (β 2) Z _ z a f hβ₂ hβ₂1) hβ₃

/-- The tolerance condition `2 δ ≤ β k` for every register value `β k ≥ 1/50`, from `δ + D ≤ 1/100`
and `0 ≤ D` (which follows from the thin factor, `D ≥ dist z z`). -/
theorem two_mul_le_of_thin_SMR (hD : 0 ≤ D) (hε : δ + D ≤ 1 / 100) {b : ℝ} (hb : 1 / 50 ≤ b) :
    2 * δ ≤ b := by
  linarith

/-- **Thin line, rank exactly one, register form**: `1/50 ≤ β 1 < 1`, `β 2, β 3 ≤ 3/20`. -/
theorem scaledSplittingRank_eq_one_of_thin_line_only_of_hundredth_SMR {a : ℝ}
    (f : @KleinerLottApprox M (WithLp 2 (ℝ × Z)) (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
      (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₁ : 1 / 50 ≤ β 1) (hβ₁1 : β 1 < 1) (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, w} ρ hρ β p = 1 :=
  scaledSplittingRank_eq_one_of_thin_line_only_SMR f hZ hε
    (two_mul_le_of_thin_SMR (le_trans dist_nonneg (hZ z z)) hε hβ₁) hβ₁1 hβ₂ hβ₃

/-- **Thin plane, rank exactly two, register form**: `1/50 ≤ β 2 < 1`, `β 3 ≤ 3/20`. -/
theorem scaledSplittingRank_eq_two_of_thin_plane_only_of_hundredth_SMR
    {a : EuclideanSpace ℝ (Fin 2)}
    (f : @KleinerLottApprox M (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z))
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₂ : 1 / 50 ≤ β 2) (hβ₂1 : β 2 < 1) (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, w} ρ hρ β p = 2 :=
  scaledSplittingRank_eq_two_of_thin_plane_only_SMR f hZ hε
    (two_mul_le_of_thin_SMR (le_trans dist_nonneg (hZ z z)) hε hβ₂) hβ₂1 hβ₃

end RankLevel

end GC.MetricGeometry
