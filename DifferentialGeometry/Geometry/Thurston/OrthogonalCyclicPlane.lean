import Mathlib.Analysis.InnerProductSpace.Spectrum
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors

/-!
The symmetric part of a real orthogonal map supplies a unit recurrence vector. Freeness excludes
fixed vectors for a nonidentity spherical action and forces an involution to be antipodal. A free
element of order greater than two has two nondegenerate rotation blocks in an orthonormal basis.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry.Topology
open scoped InnerProductSpace

namespace GC.Geometry.SphericalCyclic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def symmetricOrthogonalSum (A : E ≃ₗᵢ[ℝ] E) : E →ₗ[ℝ] E :=
  A.toLinearEquiv.toLinearMap + A.symm.toLinearEquiv.toLinearMap

private theorem symmetricOrthogonalSum_symmetric (A : E ≃ₗᵢ[ℝ] E) :
    (symmetricOrthogonalSum A).IsSymmetric := by
  intro x y
  change inner ℝ (A x + A.symm x) y = inner ℝ x (A y + A.symm y)
  rw [inner_add_left, inner_add_right, A.inner_map_eq_flip, A.symm.inner_map_eq_flip]
  simp only [LinearIsometryEquiv.symm_symm]
  ring

theorem exists_unit_orthogonal_recurrence [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E ≃ₗᵢ[ℝ] E) : ∃ v : E, ∃ c : ℝ,
    ‖v‖ = 1 ∧ A (A v) = (2 * c) • A v - v := by
  let h := symmetricOrthogonalSum_symmetric A
  let b := h.eigenvectorBasis rfl
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let μ := h.eigenvalues rfl i
  refine ⟨b i, μ / 2, b.norm_eq_one i, ?_⟩
  have hv : A (b i) + A.symm (b i) = μ • b i := h.apply_eigenvectorBasis rfl i
  have ha := congrArg A hv
  rw [map_add, A.apply_symm_apply, map_smul] at ha
  rw [show 2 * (μ / 2) = μ by ring]
  exact eq_sub_of_add_eq ha

private theorem free_isometry_no_fixed_vector (G : SphericalSpaceFormGroup) (γ : G.group)
    (hγ : γ ≠ 1) (x : EuclideanSpace ℝ (Fin 4)) (hx : γ.val x = x) : x = 0 := by
  by_contra hzero
  let y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.mpr hzero]⟩
  have hy : DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val y = y := by
    apply Subtype.ext
    change γ.val (‖x‖⁻¹ • x) = ‖x‖⁻¹ • x
    rw [map_smul, hx]
  exact hγ (G.free γ y hy)

theorem free_involution_eq_neg (G : SphericalSpaceFormGroup) (γ : G.group)
    (hγ : γ ≠ 1) (hpow : γ ^ 2 = 1) : γ.val = LinearIsometryEquiv.neg ℝ := by
  ext1 x
  have hs : γ.val (γ.val x) = x := by
    have h := congrArg (fun g : G.group => g.val x) hpow
    simpa only [pow_two, Subgroup.coe_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply, Subgroup.coe_one, LinearIsometryEquiv.coe_one, id_eq] using h
  have hf : γ.val (γ.val x + x) = γ.val x + x := by
    rw [map_add, hs, add_comm]
  have hz := free_isometry_no_fixed_vector G γ hγ (γ.val x + x) hf
  exact eq_neg_of_add_eq_zero_left hz

theorem exists_rotation_plane [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E ≃ₗᵢ[ℝ] E) (hfix : ∀ x, A x = x → x = 0)
    (hfix2 : ∀ x, A (A x) = x → x = 0) : ∃ v w : E,
    Orthonormal ℝ ![v, w] ∧ ∃ c s : ℝ, 0 < s ∧ c ^ 2 + s ^ 2 = 1 ∧
      A v = c • v + s • w ∧ A w = (-s) • v + c • w := by
  obtain ⟨v, c, hv, hrec⟩ := exists_unit_orthogonal_recurrence A
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hp : A v ≠ v := by
    intro h
    exact hv0 (hfix v h)
  have hm : A v ≠ -v := by
    intro h
    apply hv0
    apply hfix2 v
    rw [h, map_neg, h, neg_neg]
  have hi : inner ℝ (A v) v = c := by
    have ha := congrArg A.symm hrec
    rw [A.symm_apply_apply, map_sub, map_smul, A.symm_apply_apply] at ha
    have hh := congrArg (fun x => inner ℝ x v) ha
    rw [inner_sub_left, inner_smul_left, A.symm.inner_map_eq_flip,
      LinearIsometryEquiv.symm_symm, real_inner_comm v, real_inner_self_eq_norm_sq, hv] at hh
    norm_num at hh
    nlinarith [real_inner_comm (A v) v]
  have hi' : inner ℝ v (A v) = c := (real_inner_comm (A v) v).trans hi
  have hn : ‖A v‖ = 1 := (A.norm_map v).trans hv
  have hc1 : c < 1 := by
    have hs := norm_sub_sq_real (A v) v
    have hp0 : 0 < ‖A v - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
    rw [hn, hv, hi] at hs
    nlinarith [sq_pos_of_pos hp0]
  have hcm : -1 < c := by
    have hs := norm_add_sq_real (A v) v
    have hm0 : A v + v ≠ 0 := fun h => hm (eq_neg_of_add_eq_zero_left h)
    have hp0 : 0 < ‖A v + v‖ := norm_pos_iff.mpr hm0
    rw [hn, hv, hi] at hs
    nlinarith [sq_pos_of_pos hp0]
  have hc : 0 < 1 - c ^ 2 := by nlinarith
  let s := Real.sqrt (1 - c ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr hc
  have hss : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hc.le
  let w := s⁻¹ • (A v - c • v)
  have hvw : inner ℝ v w = 0 := by
    dsimp [w]
    rw [inner_smul_right, inner_sub_right, inner_smul_right,
      hi', real_inner_self_eq_norm_sq, hv]
    ring
  have hw : ‖w‖ = 1 := by
    have hnorm := norm_sub_sq_real (A v) (c • v)
    rw [hn, norm_smul, hv, Real.norm_eq_abs, inner_smul_right, hi] at hnorm
    have hnorm' : ‖A v - c • v‖ ^ 2 = s ^ 2 := by
      nlinarith [sq_abs c]
    have hroot : ‖A v - c • v‖ = s := by
      nlinarith [norm_nonneg (A v - c • v)]
    dsimp [w]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), hroot,
      inv_mul_cancel₀ hs.ne']
  have hav : A v = c • v + s • w := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    module
  have haw : A w = (-s) • v + c • w := by
    have hh : s • A w = c • A v - v := by
      dsimp [w]
      rw [map_smul, map_sub, map_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, hrec]
      module
    apply (smul_right_injective (M := E) hs.ne')
    change s • A w = s • ((-s) • v + c • w)
    rw [hh, hav]
    have hcoef : c * c - 1 = -(s * s) := by nlinarith [hss]
    calc
      c • (c • v + s • w) - v = (c * c - 1) • v + (c * s) • w := by module
      _ = s • ((-s) • v + c • w) := by rw [hcoef]; module
  refine ⟨v, w, ?_, c, s, hs, by nlinarith [hss], hav, haw⟩
  simp [orthonormal_vecCons_iff, hv, hw, hvw]


theorem exists_free_rotation_plane (G : SphericalSpaceFormGroup) (γ : G.group)
    (horder : 2 < orderOf γ) : ∃ v w : EuclideanSpace ℝ (Fin 4),
    Orthonormal ℝ ![v, w] ∧ ∃ c s : ℝ, 0 < s ∧ c ^ 2 + s ^ 2 = 1 ∧
      γ.val v = c • v + s • w ∧ γ.val w = (-s) • v + c • w := by
  have hγ : γ ≠ 1 := by intro h; simp [h] at horder
  have hγ2 : γ ^ 2 ≠ 1 := by
    intro h
    have ho := orderOf_le_of_pow_eq_one (by decide : 0 < 2) h
    omega
  apply exists_rotation_plane γ.val
  · exact free_isometry_no_fixed_vector G γ hγ
  · intro x hx
    apply free_isometry_no_fixed_vector G (γ ^ 2) hγ2 x
    exact hx


theorem exists_free_rotation_basis (G : SphericalSpaceFormGroup) (γ : G.group)
    (horder : 2 < orderOf γ) :
    ∃ b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)), ∃ c s d t : ℝ,
      0 < s ∧ 0 < t ∧ c ^ 2 + s ^ 2 = 1 ∧ d ^ 2 + t ^ 2 = 1 ∧
      γ.val (b 0) = c • b 0 + s • b 1 ∧ γ.val (b 1) = (-s) • b 0 + c • b 1 ∧
      γ.val (b 2) = d • b 2 + t • b 3 ∧ γ.val (b 3) = (-t) • b 2 + d • b 3 := by
  obtain ⟨v, w, hon, c, s, hs, hcs, hav, haw⟩ := exists_free_rotation_plane G γ horder
  let K := Submodule.span ℝ (Set.range ![v, w])
  have hvK : v ∈ K := Submodule.subset_span ⟨0, rfl⟩
  have hwK : w ∈ K := Submodule.subset_span ⟨1, rfl⟩
  have hdim : Module.finrank ℝ K = 2 := finrank_span_eq_card hon.linearIndependent
  have hmap : K.map γ.val.toLinearEquiv.toLinearMap = K := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · change γ.val v ∈ K
        rw [hav]
        exact K.add_mem (K.smul_mem c hvK) (K.smul_mem s hwK)
      · change γ.val w ∈ K
        rw [haw]
        exact K.add_mem (K.smul_mem (-s) hvK) (K.smul_mem c hwK)
    · exact LinearEquiv.finrank_map_eq γ.val.toLinearEquiv K
  have horthmap : Kᗮ.map γ.val.toLinearEquiv.toLinearMap = Kᗮ := by
    have hr : γ.val.toLinearIsometry.range = ⊤ :=
      LinearMap.range_eq_top.mpr γ.val.surjective
    have hm := Submodule.map_orthogonal K γ.val.toLinearIsometry
    change Kᗮ.map γ.val.toLinearEquiv.toLinearMap =
      (K.map γ.val.toLinearEquiv.toLinearMap)ᗮ ⊓ γ.val.toLinearIsometry.range at hm
    simpa only [hmap, hr, inf_top_eq] using hm
  have horthdim : Module.finrank ℝ Kᗮ = 2 := by
    have hd := K.finrank_add_finrank_orthogonal
    rw [hdim, finrank_euclideanSpace] at hd
    norm_num at hd
    omega
  have orthogonalNontrivial : Nontrivial Kᗮ :=
    Module.nontrivial_of_finrank_pos (by rw [horthdim]; norm_num)
  let B : Kᗮ ≃ₗᵢ[ℝ] Kᗮ :=
    (γ.val.submoduleMap Kᗮ).trans
      (LinearIsometryEquiv.ofEq (Kᗮ.map γ.val.toLinearEquiv.toLinearMap) Kᗮ horthmap)
  have hB (x : Kᗮ) : (B x : EuclideanSpace ℝ (Fin 4)) = γ.val x := by
    change (LinearIsometryEquiv.ofEq (Kᗮ.map γ.val.toLinearEquiv.toLinearMap) Kᗮ
      horthmap (γ.val.submoduleMap Kᗮ x) : EuclideanSpace ℝ (Fin 4)) = γ.val x
    exact LinearIsometryEquiv.coe_ofEq_apply horthmap (γ.val.submoduleMap Kᗮ x)
  have hγ : γ ≠ 1 := by intro h; simp [h] at horder
  have hγ2 : γ ^ 2 ≠ 1 := by
    intro h
    have ho := orderOf_le_of_pow_eq_one (by decide : 0 < 2) h
    omega
  have hfix : ∀ x : Kᗮ, B x = x → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply free_isometry_no_fixed_vector G γ hγ x.val
    exact congrArg Subtype.val hx
  have hfix2 : ∀ x : Kᗮ, B (B x) = x → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply free_isometry_no_fixed_vector G (γ ^ 2) hγ2 x.val
    exact congrArg Subtype.val hx
  obtain ⟨z, a, hon2, d, t, ht, hdt, haz, haa⟩ := exists_rotation_plane B hfix hfix2
  have hnz : ‖z.val‖ = 1 := hon2.norm_eq_one 0
  have hna : ‖a.val‖ = 1 := hon2.norm_eq_one 1
  have hza : inner ℝ z.val a.val = 0 := hon2.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
  have hvw : inner ℝ v w = 0 := hon.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
  have hvz : inner ℝ v z.val = 0 := K.inner_right_of_mem_orthogonal hvK z.property
  have hva : inner ℝ v a.val = 0 := K.inner_right_of_mem_orthogonal hvK a.property
  have hwz : inner ℝ w z.val = 0 := K.inner_right_of_mem_orthogonal hwK z.property
  have hwa : inner ℝ w a.val = 0 := K.inner_right_of_mem_orthogonal hwK a.property
  have hon4 : Orthonormal ℝ ![v, w, z.val, a.val] := by
    rw [orthonormal_vecCons_iff]
    refine ⟨hon.norm_eq_one 0, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hvw
      · exact hvz
      · exact hva
    · simp [orthonormal_vecCons_iff, show ‖w‖ = 1 from hon.norm_eq_one 1,
        hnz, hna, hwz, hwa, hza]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![v, w, z.val, a.val]) := by
    apply le_of_eq
    symm
    apply Submodule.eq_top_of_finrank_eq
    simpa using finrank_span_eq_card hon4.linearIndependent
  let b := OrthonormalBasis.mk hon4 hspan
  refine ⟨b, c, s, d, t, hs, ht, hcs, hdt, ?_, ?_, ?_, ?_⟩
  · simpa [b, OrthonormalBasis.coe_mk] using hav
  · simpa [b, OrthonormalBasis.coe_mk] using haw
  · simpa [b, OrthonormalBasis.coe_mk, hB] using congrArg Subtype.val haz
  · simpa [b, OrthonormalBasis.coe_mk, hB] using congrArg Subtype.val haa

end GC.Geometry.SphericalCyclic
