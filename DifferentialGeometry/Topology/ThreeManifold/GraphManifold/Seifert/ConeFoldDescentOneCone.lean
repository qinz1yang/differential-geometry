import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeFoldData

/-!
# The one-cone block carries an `H² × ℝ` geometry

For `p ≥ 2` the shape `oneConeOfOrder p` has a cone of angle `π/p` at the first vertex and a cusp
at `0` (`θ₁ = π/p`, `θ₂ = 0`). Its two-dimensional fold `oneConeFoldData` (lane A4b2) satisfies
the interface `ConeShape.FoldData`, so the descent of `ConeFoldDescentAssembly` gives an interior
geometry of model `.hyperbolicProduct` on the standard one-cone carrier for every primitive
`(p, q)` (`oneConeBlock_interiorGeometry`), the input of the filled-pants assembly.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint GC.Geometry
open scoped Manifold ContDiff

universe u

namespace GC.Seifert

def ConeShape.oneConeOfOrder (p : ℕ) (hp : 2 ≤ p) : ConeShape where
  θ₁ := Real.pi / p
  θ₂ := 0
  θ₁_pos := div_pos Real.pi_pos (by positivity)
  θ₁_le := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h2
  θ₂_nonneg := le_rfl
  θ₂_le := by positivity
  sum_lt := by
    have h2 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    rw [add_zero]
    exact div_lt_self Real.pi_pos h2

theorem ConeShape.oneConeOfOrder_mul (p : ℕ) (hp : 2 ≤ p) :
    (ConeShape.oneConeOfOrder p hp).θ₁ * p = Real.pi := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  change Real.pi / p * p = Real.pi
  field_simp

theorem oneConeBlock_interiorGeometry (p : ℕ) (q : ℤ) (hp : 2 ≤ p)
    (hpq : Int.gcd (p : ℤ) q = 1) :
    ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct :=
  oneConeBlock_interiorGeometry_of_foldData hp hpq (ConeShape.oneConeOfOrder_mul p hp) rfl
    ((ConeShape.oneConeOfOrder p hp).oneConeFoldData rfl (ConeShape.oneConeOfOrder_mul p hp))

end GC.Seifert
