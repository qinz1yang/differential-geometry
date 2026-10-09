import DifferentialGeometry.Geometry.Thurston.OrthogonalCyclicPlane
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensCover
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
The two real rotation blocks determine actual circle multipliers in the lens coordinates. The
change of orthonormal basis is an orthogonal conjugacy of the original linear action.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Topology GC.Seifert GC.GraphManifold
open scoped InnerProductSpace

namespace GC.Geometry.SphericalCyclic

private def rotationCircle (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Circle :=
  ⟨⟨c, s⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    have hn : ‖(⟨c, s⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hcs]
    nlinarith [norm_nonneg (⟨c, s⟩ : ℂ)]⟩

theorem rotation_basis_lens_conjugacy
    (A : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
    (c s d t : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hdt : d ^ 2 + t ^ 2 = 1)
    (ha0 : A (b 0) = c • b 0 + s • b 1)
    (ha1 : A (b 1) = (-s) • b 0 + c • b 1)
    (ha2 : A (b 2) = d • b 2 + t • b 3)
    (ha3 : A (b 3) = (-t) • b 2 + d • b 3) :
    ∃ u v : Circle, b.repr * A * b.repr.symm = lensPairRotation u v := by
  refine ⟨rotationCircle c s hcs, rotationCircle d t hdt, ?_⟩
  apply (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.ext_linearIsometryEquiv
  intro i
  change (b.repr * A * b.repr.symm) (EuclideanSpace.basisFun (Fin 4) ℝ i) = _
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, b.repr_symm_single]
  apply lensCoordinates.injective
  rw [lensCoordinates_lensPairRotation]
  rw [WithLp.ext_iff]
  apply Prod.ext
  · change (lensCoordinates (b.repr (A (b i)))).fst =
      (rotationCircle c s hcs : ℂ) * (lensCoordinates (EuclideanSpace.single i 1)).fst
    rw [lensCoordinates_fst, lensCoordinates_fst]
    fin_cases i <;> apply Complex.ext <;>
      simp [ha0, ha1, ha2, ha3, map_add, map_smul, b.repr_self,
        pairCoordinates_apply, rotationCircle]
  · change (lensCoordinates (b.repr (A (b i)))).snd =
      (rotationCircle d t hdt : ℂ) * (lensCoordinates (EuclideanSpace.single i 1)).snd
    rw [lensCoordinates_snd, lensCoordinates_snd]
    fin_cases i <;> apply Complex.ext <;>
      simp [ha0, ha1, ha2, ha3, map_add, map_smul, b.repr_self,
        pairCoordinates_apply, rotationCircle]


theorem lens_conjugacy_primitive_roots (G : SphericalSpaceFormGroup) (γ : G.group)
    (u v : Circle)
    (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (hconj : φ * γ.val * φ.symm = lensPairRotation u v) :
    IsPrimitiveRoot u (orderOf γ) ∧ IsPrimitiveRoot v (orderOf γ) := by
  have hpair (n : ℕ) :
      (lensPairRotation u v) ^ n = lensPairRotation (u ^ n) (v ^ n) := by
    induction n with
    | zero => simpa using lensPairRotation_one.symm
    | succ n hn => rw [pow_succ, hn, pow_succ, pow_succ, lensPairRotation_mul]
  have hp (n : ℕ) : φ * (γ ^ n).val * φ.symm = lensPairRotation (u ^ n) (v ^ n) := by
    have hc : MulAut.conj φ γ.val = lensPairRotation u v := hconj
    have hh := map_pow (MulAut.conj φ) γ.val n
    rw [hc, hpair] at hh
    exact hh
  have hfixed (n : ℕ) (i : Fin 4)
      (hi : lensPairRotation (u ^ n) (v ^ n) (EuclideanSpace.single i 1) =
        EuclideanSpace.single i 1) : γ ^ n = 1 := by
    let x := φ.symm (EuclideanSpace.single i 1)
    have hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      dsimp [x]
      rw [φ.symm.norm_map]
      simpa only [EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one i
    apply G.free (γ ^ n) ⟨x, hx⟩
    apply Subtype.ext
    change (γ ^ n).val x = x
    apply φ.injective
    have hh := congrArg (fun f => f (EuclideanSpace.single i 1)) (hp n)
    simpa only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hi,
      x, φ.apply_symm_apply] using hh
  have hleft (n : ℕ) : u ^ n = 1 ↔ γ ^ n = 1 := by
    constructor
    · intro hu
      apply hfixed n 0
      apply lensCoordinates.injective
      rw [lensCoordinates_lensPairRotation]
      rw [WithLp.ext_iff]
      apply Prod.ext <;> simp [hu, lensCoordinates_fst, lensCoordinates_snd,
        pairCoordinates_apply, Complex.ext_iff]
    · intro hγ
      have hh := hp n
      simp only [hγ, Subgroup.coe_one, mul_one] at hh
      change φ * φ⁻¹ = lensPairRotation (u ^ n) (v ^ n) at hh
      rw [mul_inv_cancel] at hh
      apply lensPairRotation_left_eq_one (x := EuclideanSpace.single (0 : Fin 4) 1)
      · norm_num [lensCoordinates_fst, pairCoordinates_apply, Complex.ext_iff]
      · rw [← hh]
        rfl
  have hright (n : ℕ) : v ^ n = 1 ↔ γ ^ n = 1 := by
    constructor
    · intro hv
      apply hfixed n 2
      apply lensCoordinates.injective
      rw [lensCoordinates_lensPairRotation]
      rw [WithLp.ext_iff]
      apply Prod.ext <;> simp [hv, lensCoordinates_fst, lensCoordinates_snd,
        pairCoordinates_apply, Complex.ext_iff]
    · intro hγ
      have hh := hp n
      simp only [hγ, Subgroup.coe_one, mul_one] at hh
      change φ * φ⁻¹ = lensPairRotation (u ^ n) (v ^ n) at hh
      rw [mul_inv_cancel] at hh
      apply lensPairRotation_right_eq_one (x := EuclideanSpace.single (2 : Fin 4) 1)
      · norm_num [lensCoordinates_snd, pairCoordinates_apply, Complex.ext_iff]
      · rw [← hh]
        rfl
  constructor
  · exact ⟨(hleft (orderOf γ)).mpr (pow_orderOf_eq_one γ),
      fun n hn => orderOf_dvd_of_pow_eq_one ((hleft n).mp hn)⟩
  · exact ⟨(hright (orderOf γ)).mpr (pow_orderOf_eq_one γ),
      fun n hn => orderOf_dvd_of_pow_eq_one ((hright n).mp hn)⟩

theorem exists_free_lens_rotation (G : SphericalSpaceFormGroup) (γ : G.group)
    (horder : 2 < orderOf γ) : ∃ u v : Circle,
    ∃ φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
      φ * γ.val * φ.symm = lensPairRotation u v ∧
      IsPrimitiveRoot u (orderOf γ) ∧ IsPrimitiveRoot v (orderOf γ) := by
  obtain ⟨b, c, s, d, t, hs, ht, hcs, hdt, ha0, ha1, ha2, ha3⟩ :=
    exists_free_rotation_basis G γ horder
  obtain ⟨u, v, hconj⟩ := rotation_basis_lens_conjugacy
    γ.val b c s d t hcs hdt ha0 ha1 ha2 ha3
  exact ⟨u, v, b.repr, hconj, lens_conjugacy_primitive_roots G γ u v b.repr hconj⟩


private theorem lensPairRotation_neg :
    lensPairRotation (-1) (-1) = LinearIsometryEquiv.neg ℝ := by
  ext1 x
  apply lensCoordinates.injective
  rw [lensCoordinates_lensPairRotation]
  simp [Circle.coe_neg, map_neg, WithLp.ext_iff, Prod.ext_iff]

theorem exists_free_lens_rotation_all_orders (G : SphericalSpaceFormGroup) (γ : G.group) :
    ∃ u v : Circle, ∃ φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
      φ * γ.val * φ.symm = lensPairRotation u v ∧
      IsPrimitiveRoot u (orderOf γ) ∧ IsPrimitiveRoot v (orderOf γ) := by
  by_cases hlarge : 2 < orderOf γ
  · exact exists_free_lens_rotation G γ hlarge
  have hpos := orderOf_pos γ
  have hcases : orderOf γ = 1 ∨ orderOf γ = 2 := by omega
  rcases hcases with hone | htwo
  · have hγ : γ = 1 := orderOf_eq_one_iff.mp hone
    have hc : (LinearIsometryEquiv.refl ℝ _) * γ.val *
        (LinearIsometryEquiv.refl ℝ _).symm = lensPairRotation 1 1 := by
      change 1 * γ.val * 1 = lensPairRotation 1 1
      simpa only [hγ, Subgroup.coe_one, one_mul, mul_one] using lensPairRotation_one.symm
    exact ⟨1, 1, LinearIsometryEquiv.refl ℝ _, hc,
      lens_conjugacy_primitive_roots G γ 1 1 (LinearIsometryEquiv.refl ℝ _) hc⟩
  · have hγ : γ ≠ 1 := by intro h; simp [h] at htwo
    have hpow : γ ^ 2 = 1 := by rw [← htwo]; exact pow_orderOf_eq_one γ
    have hn := free_involution_eq_neg G γ hγ hpow
    have hc : (LinearIsometryEquiv.refl ℝ _) * γ.val *
        (LinearIsometryEquiv.refl ℝ _).symm = lensPairRotation (-1) (-1) := by
      change 1 * γ.val * 1 = lensPairRotation (-1) (-1)
      simpa only [hn, one_mul, mul_one] using lensPairRotation_neg.symm
    exact ⟨-1, -1, LinearIsometryEquiv.refl ℝ _, hc,
      lens_conjugacy_primitive_roots G γ (-1) (-1) (LinearIsometryEquiv.refl ℝ _) hc⟩

end GC.Geometry.SphericalCyclic
