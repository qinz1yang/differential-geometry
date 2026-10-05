import DifferentialGeometry.Geometry.Exponential.Flat.AffineScrewPeriods
import DifferentialGeometry.Geometry.Exponential.Flat.FiniteTorusDeckQuotient

/-!
The axis displacement of an actual free lattice deck motion has precisely the period of its
actual rotation in the translation lattice. Finite torus freeness proves the forward direction;
the constructed axis and affine linear part prove the converse without an integral axis premise.
-/

set_option autoImplicit false

noncomputable section

open Module Set GC.GraphManifold.FlatTorus

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineScrew_lattice_period {G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)}
    {b : Basis (Fin 3) ℝ E3} (hb : Submodule.span ℤ (range b) = affineTranslationModule G)
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E3, g.val x ≠ x) (g : G) {p q : E3}
    (hp : g.val p = p + q) (hq : g.val.linearIsometryEquiv q = q) {m : ℕ} :
    (m : ℝ) • q ∈ affineTranslationModule G ↔ orderOf g.val.linearIsometryEquiv ∣ m := by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro hmem
    have he : periodicTriple b p = periodicTriple b ((g.val ^ m) p) := by
      apply periodicTriple_eq_iff.mpr
      rw [affineAxis_pow_apply g.val hp hq, add_sub_cancel_left]
      rw [← hb, Submodule.mem_span_range_iff_exists_fun ℤ] at hmem
      exact exists_congr (fun c => eq_comm) |>.mp hmem
    have hfix : finiteTorusDeckHom G b hb (QuotientGroup.mk (g ^ m)) (periodicTriple b p) =
        periodicTriple b p := by
      rw [finiteTorusDeckHom_apply]
      exact he.symm
    have hk := (QuotientGroup.eq_one_iff (g ^ m)).mp
      (finiteTorusDeckHom_eq_one_of_fixed G b hb hfree _ _ hfix)
    have hL := mem_affineTranslationKernel.mp hk
    change affineLinearHom (g.val ^ m) = 1 at hL
    rw [map_pow] at hL
    exact hL
  · intro hL
    have hLm : (g.val ^ m).linearIsometryEquiv = 1 := by
      change affineLinearHom (g.val ^ m) = 1
      rw [map_pow]
      exact hL
    have hzero : (g.val ^ m) 0 = (m : ℝ) • q := by
      have he := affineAxis_pow_apply g.val hp hq m
      rw [affineIsometry_apply, hLm] at he
      change p + (g.val ^ m) 0 = p + (m : ℝ) • q at he
      exact add_left_cancel he
    have htr : g.val ^ m = AffineIsometryEquiv.constVAdd ℝ E3 ((m : ℝ) • q) := by
      apply AffineIsometryEquiv.ext
      intro x
      rw [affineIsometry_apply, hLm, hzero]
      change x + (m : ℝ) • q = (m : ℝ) • q + x
      exact add_comm x _
    change AffineIsometryEquiv.constVAdd ℝ E3 ((m : ℝ) • q) ∈ G
    rw [← htr]
    exact G.pow_mem g.property m

end DifferentialGeometry.Geometry.FlatSurface
