import DifferentialGeometry.Geometry.Exponential.Flat.LineReverseInvolution
import DifferentialGeometry.Geometry.Exponential.Flat.AffineScrewPeriods

/-!
An actual free affine group cannot have a half-turn reversing the axis and conjugating
an order-three rotation to its inverse. The half-turn square translation is in the actual
translation module; its rotated translation corrects that lift to actual order two.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem orderThree_orthogonal_sum_zero (L : E3 ≃ₗᵢ[ℝ] E3) (hp : L ^ 3 = 1)
    (hne : L ≠ 1) (hpos : 0 < LinearMap.det L.toLinearMap) (q r : E3)
    (hq : q ≠ 0) (hfix : L q = q) (horth : inner ℝ q r = 0) :
    r + L r + (L ^ 2) r = 0 := by
  let s := r + L r + (L ^ 2) r
  have hL3 : L (L (L r)) = r := congrArg (fun K : E3 ≃ₗᵢ[ℝ] E3 => K r) hp
  have hs : L s = s := by
    change L (r + L r + L (L r)) = r + L r + L (L r)
    rw [map_add, map_add, hL3]
    abel
  obtain ⟨a, ha⟩ := orderThree_fixedVector_uniqueLine L hp hne hpos q s hq hfix hs
  have hi : inner ℝ q (L r) = 0 := by
    have he := L.inner_map_map q r
    rw [hfix, horth] at he
    exact he
  have hi2 : inner ℝ q ((L ^ 2) r) = 0 := by
    have he := L.inner_map_map q (L r)
    rw [hfix, hi] at he
    exact he
  have his : inner ℝ q s = 0 := by
    change inner ℝ q (r + L r + (L ^ 2) r) = 0
    rw [inner_add_right, inner_add_right, horth, hi, hi2]
    norm_num
  rw [ha, real_inner_smul_right] at his
  have hqq : inner ℝ q q ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)
  have hz : a = 0 := (mul_eq_zero.mp his).resolve_right hqq
  simpa only [hz, zero_smul] using ha

theorem affineFree_dihedralThree_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (g k : G) (hg3 : g.val.linearIsometryEquiv ^ 3 = 1)
    (hgn : g.val.linearIsometryEquiv ≠ 1)
    (hgpos : 0 < LinearMap.det g.val.linearIsometryEquiv.toLinearMap)
    (hk2 : k.val.linearIsometryEquiv ^ 2 = 1)
    (hc : k.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      k.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹)
    (q : E3) (hq : q ≠ 0) (hfix : g.val.linearIsometryEquiv q = q)
    (hflip : k.val.linearIsometryEquiv q = -q) : False := by
  let L := g.val.linearIsometryEquiv
  let K := k.val.linearIsometryEquiv
  have hqneg : q ≠ -q := by
    intro he
    have hh := smul_left_injective ℝ hq
      (show (1 : ℝ) • q = (-1 : ℝ) • q by simpa only [one_smul, neg_one_smul] using he)
    norm_num at hh
  have hk : k ≠ 1 := by
    intro he
    rw [he] at hflip
    exact hqneg hflip
  obtain ⟨p, r, hr0, hp, hr, hu0, hu, hpow⟩ :=
    exists_affineScrew_period G hfree k hk 2 (by decide) hk2
  let u := (2 : ℝ) • r
  have hKu : K u = u := by rw [map_smul, hr]
  have hqu : inner ℝ q u = 0 := by
    have hi := K.inner_map_map q u
    rw [hflip, hKu, inner_neg_left] at hi
    linarith
  have hsum : u + L u + (L ^ 2) u = 0 :=
    orderThree_orthogonal_sum_zero L hg3 hgn hgpos q u hq hfix hqu
  have hKLu : K (L u) = (L ^ 2) u := by
    have he := congrArg (fun T : E3 ≃ₗᵢ[ℝ] E3 => T (K u)) hc
    change K (L (K.symm (K u))) = L.symm (K u) at he
    rw [K.symm_apply_apply, hKu] at he
    rw [he]
    apply L.injective
    rw [L.apply_symm_apply]
    symm
    exact congrArg (fun T : E3 ≃ₗᵢ[ℝ] E3 => T u) hg3
  let v := L u
  have hv : v ∈ affineTranslationModule G := affineTranslationModule_linear_mem G g hu
  let a : G := ⟨AffineIsometryEquiv.constVAdd ℝ E3 v * k.val, G.mul_mem hv k.property⟩
  have hlin : a.val.linearIsometryEquiv = K := by
    change affineLinearHom (AffineIsometryEquiv.constVAdd ℝ E3 v * k.val) = _
    rw [map_mul]
    rfl
  have han : a ≠ 1 := by
    intro he
    have hK : K = 1 := by rw [← hlin, he]; rfl
    change K q = -q at hflip
    rw [hK] at hflip
    exact hqneg hflip
  have hkadd (x y : E3) : k.val (x + y) = K x + k.val y := k.val.map_vadd y x
  have hpoint : (a.val ^ 2) p = p := by
    change v + k.val (v + k.val p) = p
    rw [hkadd]
    change v + (K v + (k.val ^ 2) p) = p
    rw [hpow]
    change L u + (K (L u) + (u + p)) = p
    rw [hKLu]
    have he : L u + (L ^ 2) u = -u := by
      apply add_eq_zero_iff_eq_neg.mp
      simpa only [add_assoc, add_comm, add_left_comm] using hsum
    rw [← add_assoc, he]
    abel
  have ha2 : a ^ 2 = 1 := by
    by_contra hn
    exact hfree (a ^ 2) hn p hpoint
  exact affineFree_no_finiteOrder G hfree han
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ha2⟩)

end DifferentialGeometry.Geometry.FlatSurface
