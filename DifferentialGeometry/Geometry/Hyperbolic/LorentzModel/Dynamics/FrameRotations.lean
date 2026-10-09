/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Conformal.Euclidean.BoundaryRealization
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.ChartAction
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Generation

noncomputable section

open Set Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.FrameRotations

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary BoundaryTopology
open Horospherical EuclideanBoundary MobiusBoundary GeodesicFlow
open LorentzGenerators TransverseGeneration BoundaryChartAction

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)

def rotation (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) : IsometryGroup m :=
  QuotientGroup.mk' _ (rotLor (DifferentialGeometry.LiouvilleBoundary.conformalMatrix_orthogonal R.toLinearIsometry))

theorem rotation_embed (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) (x : Horizontal m) :
    rotation R • embed x = embed (R x) := by
  change (QuotientGroup.mk' _ (rotLor _) : IsometryGroup m) •
    horo (DifferentialGeometry.LiouvilleBoundary.eucEquiv x) = horo (DifferentialGeometry.LiouvilleBoundary.eucEquiv (R x))
  calc
    _ = horo (DifferentialGeometry.LiouvilleBoundary.conformalMatrix R.toLinearIsometry *ᵥ
        DifferentialGeometry.LiouvilleBoundary.eucEquiv x) :=
      rot_po_smul_horo (DifferentialGeometry.LiouvilleBoundary.conformalMatrix_orthogonal R.toLinearIsometry) _
    _ = _ := by
      rw [← DifferentialGeometry.LiouvilleBoundary.transLinear_eq_mulVec, DifferentialGeometry.LiouvilleBoundary.transLinear_apply,
        ContinuousLinearEquiv.symm_apply_apply]
      rfl

theorem rotation_infty (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) :
    rotation R • (ptInfty : BoundaryH (m + 1)) = ptInfty := by
  by_contra h
  have he : rotation R • embed (R.symm (coords (rotation R • ptInfty))) =
      rotation R • ptInfty := by
    rw [rotation_embed, R.apply_symm_apply, embed_coords h]
  exact embed_ne_infty _ (MulAction.injective (rotation R) he)

variable [Nonempty (Fin m)]

theorem eq_of_embed {g h : IsometryGroup m}
    (he : ∀ x : Horizontal m, g • embed x = h • embed x) : g = h := by
  apply LorentzGenerators.eq_of_horo (by
    have h : 0 < m := by
      simpa using Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin m))
    omega)
  intro x
  exact he ((EuclideanSpace.equiv (Fin m) ℝ).symm x)

theorem rotation_mul (R S : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) :
    rotation (R * S) = rotation R * rotation S := by
  apply eq_of_embed
  intro x
  simp only [mul_smul, rotation_embed, LinearIsometryEquiv.coe_mul, Function.comp_def]

theorem rotation_one : rotation (1 : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) = 1 := by
  apply eq_of_embed
  intro x
  rw [rotation_embed, one_smul]
  rfl

theorem rotation_inv (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) :
    rotation R⁻¹ = (rotation R)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← rotation_mul, mul_inv_cancel, rotation_one]

theorem rotation_translation (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) (b : Horizontal m) :
    rotation R * translation (fun i => b i) * (rotation R)⁻¹ =
      translation (fun i => R b i) := by
  apply eq_of_embed
  intro x
  rw [← rotation_inv]
  simp only [mul_smul, rotation_embed, BoundaryMeasure.translation_embed,
    map_add, LinearIsometryEquiv.coe_inv, R.apply_symm_apply]

omit [Nonempty (Fin m)] in
theorem inversion_embed_zero :
    (inversion : IsometryGroup m) • embed (0 : Horizontal m) = ptInfty := by
  change (inversion : IsometryGroup m) • horo (0 : Fin m → ℝ) = ptInfty
  rw [← inversion_infty, ← mul_smul, inversion_sq, one_smul]

omit [Nonempty (Fin m)] in
theorem inversion_embed {x : Horizontal m} (hx : x ≠ 0) :
    (inversion : IsometryGroup m) • embed x = embed ((‖x‖ ^ 2)⁻¹ • x) := by
  have hp : (fun i => x i) ≠ (0 : Fin m → ℝ) := by
    intro h
    apply hx
    exact (EuclideanSpace.equiv (Fin m) ℝ).injective h
  change (QuotientGroup.mk' _ invertLor : IsometryGroup m) • horo (fun i => x i) = _
  calc
    _ = horo ((normSq (fun i => x i))⁻¹ • (fun i => x i)) := invert_po_smul_horo _ hp
    _ = _ := by rw [normSq_horizontal]; rfl

theorem rotation_inversion (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) :
    rotation R * (inversion : IsometryGroup m) = inversion * rotation R := by
  apply eq_of_embed
  intro x
  by_cases hx : x = 0
  · subst x
    simp only [mul_smul, inversion_embed_zero, rotation_infty, rotation_embed, map_zero]
  · have hrx : R x ≠ 0 := fun h => hx (R.injective (h.trans (map_zero R).symm))
    simp only [mul_smul, inversion_embed hx, rotation_embed, inversion_embed hrx,
      map_smul, R.norm_map]

theorem rotation_conjugate_inversion (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) :
    rotation R * (inversion : IsometryGroup m) * (rotation R)⁻¹ = inversion := by
  rw [rotation_inversion, mul_inv_cancel_right]

theorem rotation_oppositeTranslation (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m)
    (b : Horizontal m) :
    rotation R * oppositeTranslation (fun i => b i) * (rotation R)⁻¹ =
      oppositeTranslation (fun i => R b i) := by
  calc
    _ = (rotation R * inversion * (rotation R)⁻¹) *
        (rotation R * translation (fun i => b i) * (rotation R)⁻¹) *
        (rotation R * inversion * (rotation R)⁻¹) := by
      simp only [oppositeTranslation]
      group
    _ = _ := by rw [rotation_conjugate_inversion, rotation_translation]; rfl

def mirror (v : Horizontal m) : Horizontal m ≃ₗᵢ[ℝ] Horizontal m :=
  (ℝ ∙ v)ᗮ.reflection

omit [Nonempty (Fin m)] in
theorem mirror_apply (v x : Horizontal m) :
    mirror v x = x - (2 * (inner ℝ v x / ‖v‖ ^ 2)) • v := by
  simp only [mirror, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    neg_sub, RCLike.ofReal_real_eq_id, id_eq, two_smul, two_mul, add_smul]

omit [Nonempty (Fin m)] in
theorem mirror_map (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) (v : Horizontal m) :
    mirror (R v) = R * mirror v * R⁻¹ := by
  have h := Submodule.reflection_map R (ℝ ∙ v)ᗮ
  simp only [Submodule.map_orthogonal_equiv, Submodule.map_span, image_singleton] at h
  exact h

omit [Nonempty (Fin m)] in
theorem mirror_smul {c : ℝ} (hc : c ≠ 0) (v : Horizontal m) :
    mirror (c • v) = mirror v := by
  simp only [mirror, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

abbrev basisVector (i : Fin m) : Horizontal m := EuclideanSpace.basisFun (Fin m) ℝ i

omit [Nonempty (Fin m)] in
theorem mirror_basis_apply (i : Fin m) (x : Horizontal m) (j : Fin m) :
    mirror (basisVector i) x j = if j = i then -x j else x j := by
  have hn : ‖basisVector i‖ = 1 := (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.1 i
  have hi : inner ℝ (basisVector i) x = x i := by
    simp only [basisVector, EuclideanSpace.basisFun_inner]
  rw [mirror_apply, hi, hn]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, basisVector,
    EuclideanSpace.basisFun_apply, one_pow, div_one, PiLp.single_apply]
  split_ifs with h
  · subst j
    ring
  · ring

theorem rotation_mirror_basis (i : Fin m) :
    rotation (mirror (basisVector i)) = reflection i := by
  have hd (x : Horizontal m) : denominator (reflectionLor i) x = 1 := by
    change vHeight (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat i.castSucc *ᵥ horoVec (fun j => x j)) = 1
    simpa only [vHeight, tc, signMat_mulVec_apply, Sum.elim_inr, Sum.elim_inl,
      ite_eq_right (Fin.castSucc_ne_last i).symm, one_mul] using vHeight_horoVec (fun j => x j)
  have hf (x : Horizontal m) : x ∈ chartDomain (reflection i) :=
    (denominator_ne_zero_iff (reflectionLor i) x).mp (by rw [hd]; exact one_ne_zero)
  have hc (x : Horizontal m) : chartAction (reflection i) x = mirror (basisVector i) x := by
    ext j
    rw [show reflection i = QuotientGroup.mk' _ (reflectionLor i) from rfl,
      chartAction_mk_apply, hd, div_one, mirror_basis_apply]
    change (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat i.castSucc *ᵥ horoVec (fun k => x k)) (Sum.inl j.castSucc) = _
    simp only [signMat_mulVec_apply, Sum.elim_inl, Fin.castSucc_inj, horoVec_castSucc]
    split_ifs <;> simp
  apply eq_of_embed
  intro x
  rw [rotation_embed, ← embed_chartAction (reflection i) (hf x), hc]

theorem rotation_conjugate_weyl (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m) (v : Horizontal m) :
    rotation R * (rotation (mirror v) * inversion) * (rotation R)⁻¹ =
      rotation (mirror (R v)) * inversion := by
  calc
    _ = (rotation R * rotation (mirror v) * (rotation R)⁻¹) *
        (rotation R * inversion * (rotation R)⁻¹) := by group
    _ = _ := by
      rw [rotation_conjugate_inversion, ← rotation_inv, ← rotation_mul, ← rotation_mul,
        ← mirror_map]

omit [Nonempty (Fin m)] in
theorem norm_basisVector (i : Fin m) : ‖basisVector i‖ = 1 :=
  (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.1 i

theorem weyl_mirror_mem (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hO : ∀ b : Fin m → ℝ, oppositeTranslation b ∈ H)
    {v : Horizontal m} (hv : v ≠ 0) :
    rotation (mirror v) * inversion ∈ H := by
  classical
  let i : Fin m := Classical.choice inferInstance
  let u : Horizontal m := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  let R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m := mirror (basisVector i - u)
  have hR : R (basisVector i) = u :=
    Submodule.reflection_sub (by rw [norm_basisVector, hu])
  let H' : Subgroup (IsometryGroup m) := H.comap (MulAut.conj (rotation R)).toMonoidHom
  have hT' (b : Fin m → ℝ) : translation b ∈ H' := by
    change rotation R * translation b * (rotation R)⁻¹ ∈ H
    have he := rotation_translation R ((EuclideanSpace.equiv (Fin m) ℝ).symm b)
    change rotation R * translation b * (rotation R)⁻¹ = _ at he
    rw [he]
    exact hT _
  have hO' (b : Fin m → ℝ) : oppositeTranslation b ∈ H' := by
    change rotation R * oppositeTranslation b * (rotation R)⁻¹ ∈ H
    have he := rotation_oppositeTranslation R ((EuclideanSpace.equiv (Fin m) ℝ).symm b)
    change rotation R * oppositeTranslation b * (rotation R)⁻¹ = _ at he
    rw [he]
    exact hO _
  have hw := H'.mul_mem (H'.mul_mem (hT' (Pi.single i 1)) (hO' (Pi.single i (-1))))
    (hT' (Pi.single i 1))
  rw [three_unipotents] at hw
  change rotation R * (reflection i * inversion) * (rotation R)⁻¹ ∈ H at hw
  rw [← rotation_mirror_basis, rotation_conjugate_weyl, hR] at hw
  have hm : mirror u = mirror v := mirror_smul (inv_ne_zero (norm_ne_zero_iff.mpr hv)) v
  rwa [hm] at hw

theorem rotation_mirror_pair_mem (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hO : ∀ b : Fin m → ℝ, oppositeTranslation b ∈ H)
    {v w : Horizontal m} (hv : v ≠ 0) (hw : w ≠ 0) :
    rotation (mirror v * mirror w) ∈ H := by
  have h := H.mul_mem (weyl_mirror_mem H hT hO hv) (weyl_mirror_mem H hT hO hw)
  have he : (rotation (mirror v) * inversion) * (rotation (mirror w) * inversion) =
      rotation (mirror v * mirror w) := by
    calc
      _ = rotation (mirror v) * (inversion * rotation (mirror w)) * inversion := by group
      _ = rotation (mirror v) * (rotation (mirror w) * inversion) * inversion := by
        rw [← rotation_inversion]
      _ = (rotation (mirror v) * rotation (mirror w)) * (inversion * inversion) := by group
      _ = _ := by rw [inversion_sq, mul_one, ← rotation_mul]
  rwa [he] at h

def quarterTurn (i j : Fin m) : Horizontal m ≃ₗᵢ[ℝ] Horizontal m :=
  mirror (basisVector i - basisVector j) * mirror (basisVector i)

omit [Nonempty (Fin m)] in
theorem basisVector_sub_ne_zero {i j : Fin m} (hij : i ≠ j) :
    basisVector i - basisVector j ≠ 0 := by
  intro h
  have he := congrArg (fun x : Horizontal m => x i) h
  simp [basisVector, PiLp.sub_apply, EuclideanSpace.basisFun_apply,
    hij, PiLp.zero_apply] at he

theorem quarterTurn_mem (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hO : ∀ b : Fin m → ℝ, oppositeTranslation b ∈ H)
    {i j : Fin m} (hij : i ≠ j) : rotation (quarterTurn i j) ∈ H :=
  rotation_mirror_pair_mem H hT hO (basisVector_sub_ne_zero hij)
    (norm_ne_zero_iff.mp (by rw [norm_basisVector]; exact one_ne_zero))

omit [Nonempty (Fin m)] in
theorem quarterTurn_first (i j : Fin m) :
    quarterTurn i j (basisVector i) = -basisVector j := by
  change mirror (basisVector i - basisVector j) (mirror (basisVector i) (basisVector i)) = _
  rw [show mirror (basisVector i) (basisVector i) = -basisVector i from
    Submodule.reflection_orthogonalComplement_singleton_eq_neg _, map_neg]
  exact congrArg Neg.neg (Submodule.reflection_sub
    (by rw [norm_basisVector, norm_basisVector] : ‖basisVector i‖ = ‖basisVector j‖))

omit [Nonempty (Fin m)] in
theorem quarterTurn_second {i j : Fin m} (hij : i ≠ j) :
    quarterTurn i j (basisVector j) = basisVector i := by
  have hi : mirror (basisVector i) (basisVector j) = basisVector j := by
    ext k
    rw [mirror_basis_apply]
    by_cases hki : k = i
    · subst k
      simp [basisVector, EuclideanSpace.basisFun_apply, hij]
    · rw [ite_eq_right hki]
  have hs : mirror (basisVector i - basisVector j) (basisVector i) = basisVector j :=
    Submodule.reflection_sub (by rw [norm_basisVector, norm_basisVector])
  change mirror (basisVector i - basisVector j) (mirror (basisVector i) (basisVector j)) = _
  rw [hi]
  calc
    _ = mirror (basisVector i - basisVector j)
        (mirror (basisVector i - basisVector j) (basisVector i)) :=
      congrArg (mirror (basisVector i - basisVector j)) hs.symm
    _ = _ := Submodule.reflection_reflection (𝕜 := ℝ)
      (ℝ ∙ (basisVector i - basisVector j))ᗮ (basisVector i)

end DifferentialGeometry.FrameRotations
