import DifferentialGeometry.Geometry.Exponential.Flat.ParallelLatticePeriods
import DifferentialGeometry.Geometry.Exponential.Flat.DihedralFourPeriodCorrection
import DifferentialGeometry.Geometry.Exponential.Flat.AffineScrewPeriods

/-!
An actual fourfold rotation and a reversing half-turn in a free oriented lattice affine
group force torsion. Their actual square periods provide a lattice correction internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem affineFree_halfTurn_norm_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x) (g : G)
    (hgn : g.val.linearIsometryEquiv ≠ 1) (p u x : E3)
    (hperiod : (g.val ^ 2) p = u + p) (hx : x ∈ affineTranslationModule G)
    (hcorrection : u + x + g.val.linearIsometryEquiv x = 0) : False := by
  let a : G := ⟨AffineIsometryEquiv.constVAdd ℝ E3 x * g.val, G.mul_mem hx g.property⟩
  have hlin : a.val.linearIsometryEquiv = g.val.linearIsometryEquiv := by
    change affineLinearHom (AffineIsometryEquiv.constVAdd ℝ E3 x * g.val) = _
    rw [map_mul]
    rfl
  have han : a ≠ 1 := by
    intro he
    apply hgn
    rw [← hlin, he]
    rfl
  have hgadd (y z : E3) : g.val (y + z) = g.val.linearIsometryEquiv y + g.val z :=
    g.val.map_vadd z y
  have hpoint : (a.val ^ 2) p = p := by
    change x + g.val (x + g.val p) = p
    rw [hgadd]
    change x + (g.val.linearIsometryEquiv x + (g.val ^ 2) p) = p
    rw [hperiod]
    calc
      x + (g.val.linearIsometryEquiv x + (u + p)) =
          (u + x + g.val.linearIsometryEquiv x) + p := by abel
      _ = p := by rw [hcorrection, zero_add]
  have ha2 : a ^ 2 = 1 := by
    by_contra hn
    exact hfree (a ^ 2) hn p hpoint
  exact affineFree_no_finiteOrder G hfree han
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ha2⟩)

theorem affineFree_dihedralFour_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x) (g k : G)
    (horder : orderOf g.val.linearIsometryEquiv = 4)
    (hgpos : 0 < LinearMap.det g.val.linearIsometryEquiv.toLinearMap)
    (hkpos : 0 < LinearMap.det k.val.linearIsometryEquiv.toLinearMap)
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
  have hkn : K ≠ 1 := by
    intro he
    change K q = -q at hflip
    rw [he] at hflip
    exact hqneg hflip
  have hk : k ≠ 1 := by
    intro he
    apply hkn
    change k.val.linearIsometryEquiv = 1
    rw [he]
    rfl
  have hKK (x : E3) : K (K x) = x :=
    congrArg (fun A : E3 ≃ₗᵢ[ℝ] E3 => A x) hk2
  have hKKmul : K * K = 1 := by simpa only [pow_two] using hk2
  have hKinv : K⁻¹ = K := by
    calc
      K⁻¹ = K⁻¹ * (K * K) := by rw [hKKmul, mul_one]
      _ = K := by group
  have hR2 : (K * L) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (K * L) * (K * L) = (K * L * K⁻¹) * L := by rw [hKinv]; group
      _ = 1 := by
        rw [hc]
        change L⁻¹ * L = 1
        group
  let a : G := k * g
  have haL : a.val.linearIsometryEquiv = K * L := rfl
  have ha2 : a.val.linearIsometryEquiv ^ 2 = 1 := by rw [haL]; exact hR2
  have haq : a.val.linearIsometryEquiv q = -q := by
    change K (L q) = -q
    rw [hfix]
    exact hflip
  have hanL : a.val.linearIsometryEquiv ≠ 1 := by
    intro he
    rw [he] at haq
    exact hqneg haq
  have han : a ≠ 1 := by
    intro he
    apply hanL
    rw [he]
    rfl
  obtain ⟨p, r, _hr0, _hp, hr, hu0, hu, hpow⟩ :=
    exists_affineScrew_period G hfree k hk 2 (by decide) hk2
  obtain ⟨z, s, _hs0, _hz, hs, _hw0, hw, hwpow⟩ :=
    exists_affineScrew_period G hfree a han 2 (by decide) ha2
  let u := (2 : ℝ) • r
  let w := (2 : ℝ) • s
  have hKu : K u = u := by rw [map_smul, hr]
  have hRw : K (L w) = w := by
    change a.val.linearIsometryEquiv w = w
    rw [map_smul, hs]
  have hqw : inner ℝ q w = 0 := by
    have he := a.val.linearIsometryEquiv.inner_map_map q w
    change inner ℝ (a.val.linearIsometryEquiv q) (K (L w)) = inner ℝ q w at he
    rw [haq, hRw, inner_neg_left] at he
    linarith
  have hKw : K w = L w := by
    have he := congrArg K hRw
    rw [hKK] at he
    exact he.symm
  let v := w + K w
  have hv : v ∈ affineTranslationModule G :=
    (affineTranslationModule G).add_mem hw (affineTranslationModule_linear_mem G k hw)
  have hKv : K v = v := by
    change K (w + K w) = w + K w
    rw [map_add, hKK]
    abel
  have hparallel : ∃ c : ℝ, v = c • u :=
    involution_fixedVector_uniqueLine K hk2 hkn hkpos u v hu0 hKu hKv
  obtain ⟨t, m, n, ht, hum, hvn, _hcop⟩ := parallel_lattice_periods_coprime b u v
    (hb.symm ▸ hu) (hb.symm ▸ hv) hu0 hparallel
  have htG : t ∈ affineTranslationModule G := hb ▸ ht
  have hm0 : m ≠ 0 := by
    intro he
    rw [he, zero_smul] at hum
    exact hu0 hum
  have hKt : K t = t := by
    have he := congrArg K hum
    rw [map_zsmul, hKu, hum] at he
    have he' : (m : ℝ) • K t = (m : ℝ) • t := by
      simpa only [Int.cast_smul_eq_zsmul ℝ] using he.symm
    have hz : (m : ℝ) • (K t - t) = 0 := by rw [smul_sub, he', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hm0))
  have hqt : inner ℝ q t = 0 := by
    have he := K.inner_map_map q t
    rw [hflip, hKt, inner_neg_left] at he
    linarith
  have hL2w : (L ^ 2) w = -w :=
    orderFour_orthogonal_square_neg L horder hgpos q w hq hfix hqw
  have hL2t : (L ^ 2) t = -t :=
    orderFour_orthogonal_square_neg L horder hgpos q t hq hfix hqt
  have hKLt : K (L t) = -L t := by
    have he := congrArg (fun A : E3 ≃ₗᵢ[ℝ] E3 => A (K t)) hc
    change K (L (K.symm (K t))) = L.symm (K t) at he
    rw [K.symm_apply_apply, hKt] at he
    rw [he]
    apply L.injective
    rw [L.apply_symm_apply, map_neg]
    change t = -L (L t)
    change L (L t) = -t at hL2t
    rw [hL2t, neg_neg]
  obtain ⟨x, hx, he | he⟩ := dihedral_four_period_norm_correction
    (affineTranslationModule G) K L u w t m n hu hw htG hKu hKw hL2w hKLt hum hvn
  · exact affineFree_halfTurn_norm_obstruction G hfree k hkn p u x
      (by rw [hpow]; rfl) hx he
  · exact affineFree_halfTurn_norm_obstruction G hfree a hanL z w x
      (by rw [hwpow]; rfl) hx he

end DifferentialGeometry.Geometry.FlatSurface
