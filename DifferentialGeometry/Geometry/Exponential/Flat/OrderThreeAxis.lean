import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalOrderThree
import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
An actual nontrivial positive order-three rotation has a one-dimensional fixed space.
Its actual cyclic representation has character average one, and the existing invariant
projection theorem gives the rank. A normalizing motion preserves that fixed line up to
sign, and an actual free affine lift supplies a nonzero vector without an axis premise.
-/

set_option autoImplicit false

noncomputable section

open Module
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem orderThree_trace_pair (L : E3 ≃ₗᵢ[ℝ] E3) (hp : L ^ 3 = 1)
    (hne : L ≠ 1) (hpos : 0 < LinearMap.det L.toLinearMap) :
    LinearMap.trace ℝ E3 L.toLinearMap = 0 ∧
      LinearMap.trace ℝ E3 (L ^ 2).toLinearMap = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let A := LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap
  have hlin : L.toLinearMap ^ 3 = 1 :=
    congrArg (fun K : E3 ≃ₗᵢ[ℝ] E3 => K.toLinearMap) hp
  have hA3 : A ^ 3 = 1 := by
    change (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap) ^ 3 = 1
    rw [LinearMap.toMatrix_pow, hlin, LinearMap.toMatrix_one]
  have hu := L.toMatrix_mem_unitaryGroup e e
  have horth : A.transpose * A = 1 := by
    have hs := Unitary.star_mul_self_of_mem hu
    change (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap).transpose *
      LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap = 1
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hs
  have hdetpos : 0 < A.det := by
    change 0 < (LinearMap.toMatrix e.toBasis e.toBasis L.toLinearMap).det
    rw [LinearMap.det_toMatrix]
    exact hpos
  have hdet : A.det = 1 :=
    (pow_eq_one_iff_of_nonneg hdetpos.le (by decide : (3 : ℕ) ≠ 0)).mp
      (by rw [← Matrix.det_pow, hA3, Matrix.det_one])
  have hAn : A ≠ 1 := by
    intro he
    apply hne
    have hl : L.toLinearMap = 1 :=
      (LinearMap.toMatrix e.toBasis e.toBasis).injective
        (he.trans (LinearMap.toMatrix_one e.toBasis).symm)
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun f : E3 →ₗ[ℝ] E3 => f x) hl
  have htrA : A.trace = 0 := orthogonal_nontrivial_cube_trace A horth hdet hA3 hAn
  have htrace : LinearMap.trace ℝ E3 L.toLinearMap = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ e.toBasis]
    exact htrA
  have htrace2 : LinearMap.trace ℝ E3 (L ^ 2).toLinearMap = 0 := by
    have hl2 : (L ^ 2).toLinearMap = L.toLinearMap ^ 2 := rfl
    rw [hl2, LinearMap.trace_eq_matrix_trace ℝ e.toBasis, ← LinearMap.toMatrix_pow]
    exact (orthogonal_cube_trace_square A horth hA3).trans htrA
  exact ⟨htrace, htrace2⟩

theorem orderThree_fixedVector_uniqueLine (L : E3 ≃ₗᵢ[ℝ] E3) (hp : L ^ 3 = 1)
    (hne : L ≠ 1) (hpos : 0 < LinearMap.det L.toLinearMap) (q v : E3)
    (hq : q ≠ 0) (hfixq : L q = q) (hfixv : L v = v) : ∃ a : ℝ, v = a • q := by
  classical
  obtain ⟨htrace, htrace2⟩ := orderThree_trace_pair L hp hne hpos
  have horder : orderOf L = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hp) with h | h
    · exact False.elim (hne (orderOf_eq_one_iff.mp h))
    · exact h
  have hf : IsOfFinOrder L := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hp⟩
  let H := Subgroup.zpowers L
  let instFinite : Finite H := finite_zpowers.mpr hf
  let instFintype : Fintype H := Fintype.ofFinite H
  let rho : Representation ℝ H E3 :=
    { toFun := fun g => g.val.toLinearMap
      map_one' := rfl
      map_mul' := by intro g h; rfl }
  have hcard : Nat.card H = 3 := (Nat.card_zpowers L).trans horder
  let instInverse : Invertible (Nat.card H : ℝ) :=
    invertibleOfNonzero (by rw [hcard]; norm_num)
  have htraceOne : LinearMap.trace ℝ E3 (1 : E3 ≃ₗᵢ[ℝ] E3).toLinearMap = 3 := by
    change LinearMap.trace ℝ E3 (1 : E3 →ₗ[ℝ] E3) = 3
    simp [LinearMap.trace_one]
  have hsum : (∑ g : H, Representation.character rho g) = 3 := by
    have he : (∑ g : H, Representation.character rho g) =
        ∑ i : Fin (orderOf L), LinearMap.trace ℝ E3 (L ^ (i : ℕ)).toLinearMap := by
      symm
      exact Fintype.sum_equiv (finEquivZPowers hf) _ _ (by intro i; rfl)
    rw [he, horder, Fin.sum_univ_three]
    norm_num [htrace, htrace2, htraceOne, LinearMap.trace_one]
  have hrank : finrank ℝ (Representation.invariants rho) = 1 := by
    have he := Representation.card_inv_mul_sum_char_eq_finrank rho
    rw [hcard, hsum] at he
    norm_num at he
    exact_mod_cast he.symm
  let g0 : H := ⟨L, Subgroup.mem_zpowers L⟩
  have hg0 : ∀ x : H, x ∈ Subgroup.zpowers g0 := by
    intro x
    obtain ⟨n, hn⟩ := x.property
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  have hqm : q ∈ Representation.invariants rho :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers rho g0 hg0 q).mpr hfixq
  have hvm : v ∈ Representation.invariants rho :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers rho g0 hg0 v).mpr hfixv
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hrank hqm hq] at hvm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvm
  exact ⟨a, ha.symm⟩

theorem orderThree_normalizer_preserves_axis (L K : E3 ≃ₗᵢ[ℝ] E3)
    (hp : L ^ 3 = 1) (hne : L ≠ 1) (hpos : 0 < LinearMap.det L.toLinearMap)
    (hconj : K * L * K⁻¹ = L ∨ K * L * K⁻¹ = L⁻¹)
    (q : E3) (hq : q ≠ 0) (hfixq : L q = q) : K q = q ∨ K q = -q := by
  have hc : (K * L * K⁻¹) (K q) = K q := by
    change K (L (K.symm (K q))) = K q
    rw [K.symm_apply_apply, hfixq]
  have hf : L (K q) = K q := by
    rcases hconj with h | h
    · rw [h] at hc
      exact hc
    · rw [h] at hc
      have he := congrArg L hc
      change L (L.symm (K q)) = L (K q) at he
      rw [L.apply_symm_apply] at he
      exact he.symm
  obtain ⟨a, ha⟩ := orderThree_fixedVector_uniqueLine L hp hne hpos q (K q) hq hfixq hf
  have hm : |a| * ‖q‖ = 1 * ‖q‖ := by
    have hn := K.norm_map q
    rw [ha, norm_smul, Real.norm_eq_abs] at hn
    simpa only [one_mul] using hn
  have habs : |a| = 1 := mul_right_cancel₀ (norm_ne_zero_iff.mpr hq) hm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · left
    rw [h, one_smul] at ha
    exact ha
  · right
    rw [h, neg_one_smul] at ha
    exact ha

theorem exists_orderThree_normalizerDeck_axis (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g : G) (hp : g.val.linearIsometryEquiv ^ 3 = 1)
    (hne : g.val.linearIsometryEquiv ≠ 1)
    (hconj : ∀ γ : G, γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹) :
    ∃ q : E3, q ≠ 0 ∧ ∀ γ : G, γ.val.linearIsometryEquiv q = q ∨
      γ.val.linearIsometryEquiv q = -q := by
  have hg : g ≠ 1 := by
    intro he
    apply hne
    rw [he]
    rfl
  obtain ⟨p, q, hpoint, hfixed⟩ := exists_affineAxis_point g.val
  have hq : q ≠ 0 := by
    intro hz
    exact hfree g hg p (by simpa only [hz, add_zero] using hpoint)
  refine ⟨q, hq, ?_⟩
  intro γ
  exact orderThree_normalizer_preserves_axis g.val.linearIsometryEquiv
    γ.val.linearIsometryEquiv hp hne (hpos g) (hconj γ) q hq hfixed

end DifferentialGeometry.Geometry.FlatSurface
