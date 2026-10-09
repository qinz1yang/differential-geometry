import DifferentialGeometry.Geometry.Exponential.Flat.AffineScrewPeriods
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
A common nonzero fixed vector of the finite actual linear group produces an invariant
integer covector. Finite averaging of actual lattice coordinates is nonzero on that vector.
Multiplication by the group cardinality makes every affine increment integral. Neither a
coordinate nor cyclic holonomy is supplied.
-/

set_option autoImplicit false

noncomputable section

open Module Function
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]
  {ι : Type*}

theorem exists_invariantAxis_integerCovector
    (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (q : V) (hq : q ≠ 0) (hfix : ∀ γ : G, γ.val.linearIsometryEquiv q = q) :
    ∃ ell : V →L[ℝ] ℝ, Surjective ell ∧
      (∀ γ : G, ∀ v : V, ell (γ.val.linearIsometryEquiv v) = ell v) ∧
      (∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) ∧
      ∀ v ∈ affineTranslationModule G, ∃ m : ℤ, ell v = m := by
  classical
  let H := (affineLinearHom.comp G.subtype).range
  let instFintype : Fintype H := Fintype.ofFinite H
  let N := Fintype.card H
  have hN : 0 < N := Fintype.card_pos
  let r := (affineLinearHom.comp G.subtype).rangeRestrict
  obtain ⟨i, hi⟩ : ∃ i, b.coord i q ≠ 0 := by
    by_contra! hz
    apply hq
    apply b.repr.injective
    ext i
    simpa only [Basis.coord_apply, map_zero, Finsupp.zero_apply] using hz i
  let ell0 : V →L[ℝ] ℝ := ∑ a : H,
    (b.coord i).toContinuousLinearMap.comp a.val.toContinuousLinearMap
  have heval (v : V) : ell0 v = ∑ a : H, b.coord i (a.val v) := by simp [ell0]
  have hinv (γ : G) (v : V) : ell0 (γ.val.linearIsometryEquiv v) = ell0 v := by
    rw [heval, heval]
    exact Fintype.sum_equiv (Equiv.mulRight (r γ)) _ _ (by intro a; rfl)
  have hfixed (a : H) : a.val q = q := by
    obtain ⟨γ, hγ⟩ := (affineLinearHom.comp G.subtype).rangeRestrict_surjective a
    have he := congrArg Subtype.val hγ
    change γ.val.linearIsometryEquiv = a.val at he
    rw [← he]
    exact hfix γ
  have hnq : ell0 q ≠ 0 := by
    rw [heval]
    simp only [hfixed, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast hN.ne') hi
  have hL (v : V) (hv : v ∈ affineTranslationModule G) :
      ∃ m : ℤ, ell0 v = m := by
    have hmem (a : H) : a.val v ∈ affineTranslationModule G := by
      obtain ⟨γ, hγ⟩ := (affineLinearHom.comp G.subtype).rangeRestrict_surjective a
      have he := congrArg Subtype.val hγ
      change γ.val.linearIsometryEquiv = a.val at he
      rw [← he]
      exact affineTranslationModule_linear_mem G γ hv
    have hcoord (a : H) : ∃ m : ℤ, b.coord i (a.val v) = m := by
      have hc := (b.mem_span_iff_repr_mem ℤ (a.val v)).mp (hb.symm ▸ hmem a) i
      obtain ⟨m, hm⟩ := hc
      exact ⟨m, by simpa only [Basis.coord_apply, algebraMap_int_eq,
        Int.coe_castRingHom] using hm.symm⟩
    choose z hz using hcoord
    refine ⟨∑ a : H, z a, ?_⟩
    rw [heval]
    simp_rw [hz]
    norm_cast
  have hinc (γ : G) : ∃ m : ℤ, (N : ℝ) * ell0 (γ.val 0) = m := by
    have hp : γ.val.linearIsometryEquiv ^ N = 1 := by
      have he := congrArg Subtype.val (pow_card_eq_one (x := r γ))
      exact he
    obtain ⟨p, v, hpoint, hv⟩ := exists_affineAxis_point γ.val
    have hpow : (γ.val ^ N).linearIsometryEquiv = 1 := by
      change affineLinearHom (γ.val ^ N) = 1
      rw [map_pow]
      exact hp
    have hz : (γ.val ^ N) 0 = (N : ℝ) • v := by
      have he := affineAxis_pow_apply γ.val hpoint hv N
      rw [affineIsometry_apply, hpow] at he
      exact add_left_cancel he
    have htrans : (γ.val ^ N) 0 ∈ affineTranslationModule G := by
      change AffineIsometryEquiv.constVAdd ℝ V ((γ.val ^ N) 0) ∈ G
      have he : AffineIsometryEquiv.constVAdd ℝ V ((γ.val ^ N) 0) = γ.val ^ N := by
        ext x
        change (γ.val ^ N) 0 + x = (γ.val ^ N) x
        conv_rhs => rw [affineIsometry_apply, hpow]
        exact add_comm _ _
      rw [he]
      exact G.pow_mem γ.property N
    obtain ⟨m, hm⟩ := hL _ htrans
    have hvalue : ell0 (γ.val 0) = ell0 v := by
      have he := congrArg ell0 hpoint
      rw [affineIsometry_apply, map_add, hinv, map_add] at he
      exact add_left_cancel he
    refine ⟨m, ?_⟩
    rw [hvalue, ← smul_eq_mul, ← map_smul, ← hz]
    exact hm
  refine ⟨(N : ℝ) • ell0, ?_, ?_, hinc, ?_⟩
  · intro y
    refine ⟨(y / ((N : ℝ) * ell0 q)) • q, ?_⟩
    simp only [smul_apply, map_smul, smul_eq_mul]
    field_simp
  · intro γ v
    change (N : ℝ) * ell0 (γ.val.linearIsometryEquiv v) = (N : ℝ) * ell0 v
    rw [hinv]
  · intro v hv
    obtain ⟨m, hm⟩ := hL v hv
    refine ⟨(N : ℤ) * m, ?_⟩
    simp only [smul_apply, smul_eq_mul, hm, Int.cast_mul, Int.cast_natCast]

end DifferentialGeometry.Geometry.FlatSurface
