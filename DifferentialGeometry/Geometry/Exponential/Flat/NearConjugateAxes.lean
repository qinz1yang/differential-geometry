import DifferentialGeometry.Geometry.Exponential.Flat.SmallRotations
import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis

/-!
Commuting affine conjugates with rotational conjugator norm less than one have the same fixed
linear subspace and the same axis points. Orthogonality and the actual operator norm establish
this directly, including infinite-dimensional real inner-product spaces.
-/

set_option autoImplicit false

noncomputable section

open Set Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V]

private theorem nearConjugate_linear_apply (g k : V ≃ᵃⁱ[ℝ] V) (x : V) :
    (k * g * k⁻¹).linearIsometryEquiv (k.linearIsometryEquiv x) =
      k.linearIsometryEquiv (g.linearIsometryEquiv x) := by
  have hi := congrArg (fun L : V ≃ₗᵢ[ℝ] V => L x) (affineLinearHom.map_mul k⁻¹ k)
  simp only [inv_mul_cancel, map_one] at hi
  change x = (k⁻¹).linearIsometryEquiv (k.linearIsometryEquiv x) at hi
  change k.linearIsometryEquiv
    (g.linearIsometryEquiv ((k⁻¹).linearIsometryEquiv (k.linearIsometryEquiv x))) =
      k.linearIsometryEquiv (g.linearIsometryEquiv x)
  rw [← hi]

private theorem nearConjugate_fixed_le (g k : V ≃ᵃⁱ[ℝ] V)
    (hk : affineRotationNorm k < 1) (hcomm : Commute g (k * g * k⁻¹))
    (w : V) (hw : g.linearIsometryEquiv w = w) :
    (k * g * k⁻¹).linearIsometryEquiv w = w := by
  let A := g.linearIsometryEquiv
  let B := k.linearIsometryEquiv
  let C := (k * g * k⁻¹).linearIsometryEquiv
  let u := C w - w
  have hAC : A (C w) = C (A w) := by
    have hlin := congrArg (fun L : V ≃ₗᵢ[ℝ] V => L w) (hcomm.map affineLinearHom).eq
    exact hlin
  have hAu : A u = u := by
    dsimp [u]
    rw [map_sub, hAC, hw]
  have hCBu : C (B u) = B u := by
    dsimp [C, B]
    rw [nearConjugate_linear_apply, hAu]
  have horth : inner ℝ (B u) u = 0 := by
    dsimp [u]
    rw [inner_sub_right, ← hCBu, C.inner_map_map, hCBu, sub_self]
  have hsquare := norm_sub_sq_real (B u) u
  rw [horth, B.norm_map, mul_zero, sub_zero] at hsquare
  have hbound : ‖B u - u‖ ≤ affineRotationNorm k * ‖u‖ := by
    exact ContinuousLinearMap.le_opNorm
      (affineLinearOperator k - ContinuousLinearMap.id ℝ V) u
  have hu : u = 0 := by
    by_contra hne
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hne
    have hlt : ‖B u - u‖ < ‖u‖ :=
      hbound.trans_lt (by nlinarith)
    nlinarith [norm_nonneg (B u - u), sq_nonneg ‖u‖]
  exact sub_eq_zero.mp hu

private theorem nearConjugate_inverse_norm (k : V ≃ᵃⁱ[ℝ] V) :
    affineRotationNorm k⁻¹ = affineRotationNorm k := by
  have h := affineRotationNorm_mul_inv (1 : V ≃ᵃⁱ[ℝ] V) k
  simp only [one_mul] at h
  rw [h, norm_sub_rev]
  rfl

theorem nearConjugate_fixedSpace_eq (g k : V ≃ᵃⁱ[ℝ] V)
    (hk : affineRotationNorm k < 1) (hcomm : Commute g (k * g * k⁻¹)) :
    ((g.linearIsometryEquiv : V →ₗ[ℝ] V) - LinearMap.id).ker =
      (((k * g * k⁻¹).linearIsometryEquiv : V →ₗ[ℝ] V) - LinearMap.id).ker := by
  have hc : k⁻¹ * (k * g * k⁻¹) * (k⁻¹)⁻¹ = g := by group
  have hki : affineRotationNorm k⁻¹ < 1 := by rw [nearConjugate_inverse_norm]; exact hk
  apply le_antisymm
  · intro w hw
    exact sub_eq_zero.mpr (nearConjugate_fixed_le g k hk hcomm w (sub_eq_zero.mp hw))
  · intro w hw
    have hrev : Commute (k * g * k⁻¹) (k⁻¹ * (k * g * k⁻¹) * (k⁻¹)⁻¹) := by
      rw [hc]
      exact hcomm.symm
    have hv := nearConjugate_fixed_le (k * g * k⁻¹) k⁻¹ hki hrev w
      (sub_eq_zero.mp hw)
    rw [hc] at hv
    exact sub_eq_zero.mpr hv

theorem nearConjugate_axis_points (g k : V ≃ᵃⁱ[ℝ] V)
    (hk : affineRotationNorm k < 1) (hcomm : Commute g (k * g * k⁻¹))
    {p q p' q' : V} (hp : g p = p + q) (hq : g.linearIsometryEquiv q = q)
    (hp' : (k * g * k⁻¹) p' = p' + q')
    (hq' : (k * g * k⁻¹).linearIsometryEquiv q' = q') :
    g.linearIsometryEquiv (p - p') = p - p' := by
  let h := k * g * k⁻¹
  let A := g.linearIsometryEquiv
  let C := h.linearIsometryEquiv
  have hfix := nearConjugate_fixedSpace_eq g k hk hcomm
  have hCq : C q = q := by
    have hm : q ∈ ((A : V →ₗ[ℝ] V) - LinearMap.id).ker := sub_eq_zero.mpr hq
    rw [hfix] at hm
    exact sub_eq_zero.mp hm
  have hcommPoint : g (h p) = h (g p) := by
    exact congrArg (fun f : V ≃ᵃⁱ[ℝ] V => f p) hcomm.eq
  have hgHp : g (h p) = h p + q := by
    rw [hcommPoint, hp]
    change h.linearIsometryEquiv q = q at hCq
    simpa only [vadd_eq_add, hCq, add_comm] using h.map_vadd p q
  have hdelta : A (h p - p) = h p - p := by
    have hm := g.map_vsub (h p) p
    simp only [hgHp, hp, vsub_eq_sub] at hm
    simpa only [add_sub_add_right_eq_sub] using hm
  have hAq' : A q' = q' := by
    have hm : q' ∈ ((C : V →ₗ[ℝ] V) - LinearMap.id).ker := sub_eq_zero.mpr hq'
    rw [← hfix] at hm
    exact sub_eq_zero.mp hm
  let u := C (p - p') - (p - p')
  have hformula : h p - p = q' + u := by
    have h1 := affineIsometry_apply h p
    have h2 := affineIsometry_apply h p'
    rw [hp'] at h2
    dsimp [u, C]
    rw [map_sub]
    linear_combination (norm := abel) h1 - h2
  have hAu : A u = u := by
    have heq : u = (h p - p) - q' := by rw [hformula]; abel
    rw [heq, map_sub, hdelta, hAq']
  have hCu : C u = u := by
    have hm : u ∈ ((A : V →ₗ[ℝ] V) - LinearMap.id).ker := sub_eq_zero.mpr hAu
    rw [hfix] at hm
    exact sub_eq_zero.mp hm
  have hzero : inner ℝ u u = 0 := by
    change inner ℝ u (C (p - p') - (p - p')) = 0
    rw [inner_sub_right, ← hCu, C.inner_map_map, hCu, sub_self]
  have hCd : C (p - p') = p - p' := sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  have hm : p - p' ∈ ((C : V →ₗ[ℝ] V) - LinearMap.id).ker := sub_eq_zero.mpr hCd
  rw [← hfix] at hm
  exact sub_eq_zero.mp hm

end DifferentialGeometry.Geometry.FlatSurface
