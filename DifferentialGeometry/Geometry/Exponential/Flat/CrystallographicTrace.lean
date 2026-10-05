import DifferentialGeometry.Geometry.Exponential.Flat.LatticeHolonomyMatrices
import DifferentialGeometry.Geometry.Exponential.Flat.CentralDeckAxis
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
An actual free affine motion has a nonzero fixed displacement direction. An orthonormal
basis extending its normalization bounds the linear trace between minus one and three.
The same actual translation lattice makes this trace one of five integral values.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem fixedVector_trace_bounds (L : E3 ≃ₗᵢ[ℝ] E3) (q : E3) (hq : q ≠ 0)
    (hfix : L q = q) :
    -1 ≤ LinearMap.trace ℝ E3 L.toLinearMap ∧ LinearMap.trace ℝ E3 L.toLinearMap ≤ 3 := by
  classical
  let u := ‖q‖⁻¹ • q
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq)]
  have hLu : L u = u := by simp only [u, map_smul, hfix]
  let v : Fin 3 → E3 := Pi.single 0 u
  have ho : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have hi : i.val = 0 := i.property
    simpa [v, Set.domRestrict, hi] using hu
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = u := by simpa [v] using hb 0 (by simp)
  have hfirst : inner ℝ (b 0) (L (b 0)) = 1 := by
    rw [hb0, hLu, real_inner_self_eq_norm_sq, hu]
    norm_num
  have hnorm (i : Fin 3) : ‖L (b i)‖ = 1 := (L.norm_map (b i)).trans (b.norm_eq_one i)
  have hlow (i : Fin 3) : -1 ≤ inner ℝ (b i) (L (b i)) :=
    neg_one_le_real_inner_of_norm_eq_one (b.norm_eq_one i) (hnorm i)
  have hhigh (i : Fin 3) : inner ℝ (b i) (L (b i)) ≤ 1 :=
    real_inner_le_one_of_norm_eq_one (b.norm_eq_one i) (hnorm i)
  rw [LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_three]
  change -1 ≤ inner ℝ (b 0) (L (b 0)) + inner ℝ (b 1) (L (b 1)) +
      inner ℝ (b 2) (L (b 2)) ∧
    inner ℝ (b 0) (L (b 0)) + inner ℝ (b 1) (L (b 1)) + inner ℝ (b 2) (L (b 2)) ≤ 3
  rw [hfirst]
  constructor <;> linarith [hlow 1, hlow 2, hhigh 1, hhigh 2]

theorem affineFree_trace_cases (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (γ : G) (hpos : 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap) :
    LinearMap.trace ℝ E3 γ.val.linearIsometryEquiv.toLinearMap = -1 ∨
    LinearMap.trace ℝ E3 γ.val.linearIsometryEquiv.toLinearMap = 0 ∨
    LinearMap.trace ℝ E3 γ.val.linearIsometryEquiv.toLinearMap = 1 ∨
    LinearMap.trace ℝ E3 γ.val.linearIsometryEquiv.toLinearMap = 2 ∨
    LinearMap.trace ℝ E3 γ.val.linearIsometryEquiv.toLinearMap = 3 := by
  by_cases he : γ = 1
  · subst γ
    right; right; right; right
    change LinearMap.trace ℝ E3 (1 : E3 →ₗ[ℝ] E3) = 3
    simp [LinearMap.trace_one]
  · obtain ⟨p, q, hp, hq⟩ := exists_affineAxis_point γ.val
    have hq0 : q ≠ 0 := by
      intro hz
      exact hfree γ he p (by simpa only [hz, add_zero] using hp)
    have hbounds := fixedVector_trace_bounds γ.val.linearIsometryEquiv q hq0 hq
    obtain ⟨A, hA, hdet, z, hz⟩ := exists_affineLinear_integerMatrix G b hb γ hpos
    rw [hz] at hbounds
    have hlo : (-1 : ℤ) ≤ z := by exact_mod_cast hbounds.1
    have hhi : z ≤ (3 : ℤ) := by exact_mod_cast hbounds.2
    have hcases : z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by omega
    rcases hcases with h | h | h | h | h <;> simp [hz, h]

end DifferentialGeometry.Geometry.FlatSurface
