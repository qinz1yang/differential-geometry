import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugPlanarSides

/-!
Actual strict fibre-circle and paired product signs in the bounded fibre plug.
The original filling, product identifications and strip coordinates are retained.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology

namespace GC.Seifert.SplitTube

theorem fibrePlug_circleHalf_connected (t : Bool) :
    IsConnected {ν : Circle | 0 < sgnR t * (-((ν : ℂ).re))} := by
  let A : Set ℂ := {z | 0 < sgnR t * (-z.re)}
  have hA : Convex ℝ A := by
    cases t
    · have h := convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear (0 : ℝ)
      convert h using 1
      ext z
      simp [A, sgnR]
    · have h := convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear (0 : ℝ)
      convert h using 1
      ext z
      simp [A, sgnR]
  have hne : A.Nonempty := by
    refine ⟨((-sgnR t : ℝ) : ℂ), ?_⟩
    change 0 < sgnR t * (-(-sgnR t))
    rw [neg_neg, sgnR_mul_self]
    norm_num
  have hzero : ∀ z ∈ A, z ≠ 0 := by
    intro z hz he
    rw [he] at hz
    change 0 < sgnR t * (-0) at hz
    simp at hz
  have hcont : ContinuousOn unitOf A := contMDiffOn_unitOf.continuousOn.mono hzero
  have he : unitOf '' A = {ν : Circle | 0 < sgnR t * (-((ν : ℂ).re))} := by
    ext ν
    constructor
    · rintro ⟨z, hz, rfl⟩
      change 0 < sgnR t * (-((unitOf z : ℂ).re))
      rw [coe_unitOf (hzero z hz)]
      have hr : (((‖z‖⁻¹ : ℝ) • z) : ℂ).re = ‖z‖⁻¹ * z.re := by
        simp [Complex.real_smul]
      rw [hr]
      have hm : sgnR t * (-(‖z‖⁻¹ * z.re)) = ‖z‖⁻¹ * (sgnR t * (-z.re)) := by ring
      rw [hm]
      exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hzero z hz))) hz
    · intro hν
      refine ⟨(ν : ℂ), hν, ?_⟩
      apply Subtype.ext
      have hn : (ν : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [Circle.norm_coe]; norm_num)
      rw [coe_unitOf hn, Circle.norm_coe, inv_one, one_smul]
  rw [← he]
  exact ⟨hne.image unitOf, hA.isPreconnected.image _ hcont⟩

theorem fibrePlug_circlePower_re (e : ℤ) (he : e = 1 ∨ e = -1) (ν : Circle) :
    ((ν ^ e : Circle) : ℂ).re = (ν : ℂ).re := by
  rcases he with rfl | rfl <;> simp

theorem fibrePlug_strip_boundary_sign (l : Fin 3) (t : Bool) {R : ℝ}
    (hR : 2 ≤ R) (θ : Circle) :
    (0 < sgnR t * stripLevel l (R • (θ : ℂ))) ↔
      0 < sgnR t * (-((θ : ℂ).re)) := by
  let w : ℂ := R • (θ : ℂ)
  have hRp : 0 < R := by linarith
  have hre : w.re = R * (θ : ℂ).re := by simp [w, Complex.real_smul]
  have hn : ‖w‖ = R := by rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hRp.le]
  have hd : 0 < tubeSlope * stripWidth w.im :=
    mul_pos (by norm_num [tubeSlope]) (stripWidth_pos w.im)
  change (0 < sgnR t * stripLevel l w) ↔ _
  rw [stripLevel_eq, ← mul_div_assoc, div_pos_iff_of_pos_right hd]
  by_cases hY : 1 ≤ |w.im|
  · rw [stripBump_of_one_le hY, mul_zero, zero_sub]
    have he : sgnR t * (-w.re) = R * (sgnR t * (-((θ : ℂ).re))) := by rw [hre]; ring
    rw [he]
    exact mul_pos_iff_of_pos_left hRp
  · have hY' : |w.im| < 1 := lt_of_not_ge hY
    have hs := Complex.sq_norm w
    rw [hn, Complex.normSq_apply] at hs
    have hy2 : w.im ^ 2 < 1 := by nlinarith [sq_abs w.im, abs_nonneg w.im]
    have hx2 : 3 < w.re ^ 2 := by nlinarith
    have hx : 1 < |w.re| := by nlinarith [sq_abs w.re, abs_nonneg w.re]
    have hc : |stripCenter l * stripBump w.im| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_nonneg (stripBump_nonneg w.im)]
      nlinarith [abs_stripCenter_le l, stripBump_le_one w.im, stripBump_nonneg w.im,
        abs_nonneg (stripCenter l)]
    have hc' := abs_le.mp hc
    rcases lt_abs.mp hx with hpos | hneg
    all_goals cases t <;> simp only [sgnR, Bool.false_eq_true, ↓reduceIte]
    all_goals constructor <;> intro h <;> nlinarith

theorem fibrePlug_hostInv_boundary (l : Fin 3) (θ : Circle) :
    hostInv l (planarCircleMap 3 l θ) = hostRadius l.val 0 • (θ : ℂ) := by
  fin_cases l
  · simp [hostInv, hostRadius, planarCircleMap, planarCenter, planarRadius,
      Complex.real_smul]
  · simp only [hostInv, ↓reduceIte, planarCircleMap, planarCenter,
      planarRadius, hostRadius]
    have he : (((1 / 2 : ℝ) : ℂ) * starRingEnd ℂ (θ : ℂ))⁻¹ = 2 * (θ : ℂ) := by
      rw [mul_inv_rev]
      have hc : (starRingEnd ℂ (θ : ℂ))⁻¹ = (θ : ℂ) := by
        rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_inv]
      rw [hc]
      norm_num [mul_comm]
    convert he using 1 <;> norm_num [Complex.real_smul]
  · simp only [hostInv, planarCircleMap, planarCenter, planarRadius, hostRadius]
    norm_num
    have he : (((1 / 2 : ℝ) : ℂ) * starRingEnd ℂ (θ : ℂ))⁻¹ = 2 * (θ : ℂ) := by
      rw [mul_inv_rev]
      have hc : (starRingEnd ℂ (θ : ℂ))⁻¹ = (θ : ℂ) := by
        rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_inv]
      rw [hc]
      norm_num [mul_comm]
    convert he using 1; norm_num [Complex.real_smul]

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

universe u

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
variable {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
variable (hlin : E.IsLinearSeam j)

theorem fibrePlugSolidSide_connected (t : Bool) :
    IsConnected (E.fibrePlugSolidSide h hlin t) := by
  let A : Set Circle := {ν | 0 < SplitTube.sgnR t * (-((ν : ℂ).re))}
  let : ConnectedSpace A := isConnected_iff_connectedSpace.mp
    (SplitTube.fibrePlug_circleHalf_connected t)
  let g : (discPlanarBase.{u} 1).surface.Carrier × A →
      (discPlanarBase.{u} 1).surface.Carrier × Circle := fun q => (q.1, q.2.val)
  have hg : Continuous g := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  let f : (discPlanarBase.{u} 1).surface.Carrier × A → W.Carrier := fun q =>
    E.toTorus.cutMap ((E.splitData h).ΘV (g q)).val
  have hf : Continuous f := E.toTorus.quotient_smooth.continuous.comp
    (continuous_subtype_val.comp ((E.splitData h).ΘV.continuous.comp hg))
  have he : range f = E.fibrePlugSolidSide h hlin t := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨g q, ?_, rfl⟩
      change 0 < SplitTube.sgnR t *
        (-(((q.2.val ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))
      rw [SplitTube.fibrePlug_circlePower_re _ (E.boundedSplitCharts h hlin).he₀]
      exact q.2.property
    · rintro ⟨q, hq, rfl⟩
      change 0 < SplitTube.sgnR t *
        (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hq
      rw [SplitTube.fibrePlug_circlePower_re _ (E.boundedSplitCharts h hlin).he₀] at hq
      refine ⟨(q.1, (⟨q.2, hq⟩ : A)), ?_⟩
      rfl
  rw [← he]
  exact isConnected_range hf

theorem fibrePlug_product_boundary_pair (τ : Torus) :
    E.toTorus.cutMap ((E.splitData h).ΘV
      ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val =
      E.toTorus.cutMap ((E.splitData h).ΘH
        (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
          ((E.crossMap j b τ).1, halfZero), (E.crossMap j b τ).2)).val := by
  have hpV : E.standardPort (E.seamPiece j b) h.1 0 =
      ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ := by
    let : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
      Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
    exact Subsingleton.elim _ _
  have hpH : E.standardPort (E.hostPiece j b) h.2.1 (E.fibrePlugFilledHostPort h) =
      ⟨E.seamSide j (!b), E.sidePiece_seamSide j (!b)⟩ := Equiv.apply_symm_apply _ _
  have hV := (E.splitData h).hV 0 (τ, halfZero)
    (zero_mem_halfCollarSource τ) (E.splitData h).hδ
  have hH := (E.splitData h).hH (E.fibrePlugFilledHostPort h)
    (E.crossMap j b τ, halfZero) (zero_mem_halfCollarSource _) (E.splitData h).hδ
  rw [← hV, ← hH, hpV, hpH,
    E.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource τ),
    E.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource (E.crossMap j b τ))]
  exact E.cutMap_sideCollar_cross j b τ

theorem fibrePlugSide_connected (t : Bool) :
    IsConnected (E.fibrePlugSide h hlin t) := by
  obtain ⟨ν, hν⟩ := (SplitTube.fibrePlug_circleHalf_connected t).nonempty
  let qV := ((discPlanarBase.{u} 1).collar 0 ((1 : Circle), halfZero), ν)
  let qH := (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
    ((E.crossMap j b (1, ν)).1, halfZero), (E.crossMap j b (1, ν)).2)
  have hV : E.toTorus.cutMap ((E.splitData h).ΘV qV).val ∈
      E.fibrePlugSolidSide h hlin t := by
    refine ⟨qV, ?_, rfl⟩
    change 0 < SplitTube.sgnR t *
      (-(((ν ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))
    rw [SplitTube.fibrePlug_circlePower_re _ (E.boundedSplitCharts h hlin).he₀]
    exact hν
  have hfirst : (E.crossMap j b (1, ν)).1 = ν ^ (E.boundedSplitCharts h hlin).e₀ := by
    rw [hlin.crossMap_apply]
    simp [linearTorusMap]
    rfl
  have hH : E.toTorus.cutMap ((E.splitData h).ΘH qH).val ∈
      E.fibrePlugHostSide h t := by
    refine ⟨qH, ?_, rfl⟩
    change 0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
        (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
          ((E.crossMap j b (1, ν)).1, halfZero)).val.down)
    have hz : (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
        ((E.crossMap j b (1, ν)).1, halfZero)).val.down =
          planarCircleMap 3 (E.fibrePlugFilledHostPort h) (E.crossMap j b (1, ν)).1 :=
      planarCollar_zero_val (Or.inr rfl) _ _
    rw [hz, SplitTube.fibrePlug_hostInv_boundary]
    apply (SplitTube.fibrePlug_strip_boundary_sign _ t
      (SplitTube.two_le_hostRadius _) _).mpr
    rw [hfirst, SplitTube.fibrePlug_circlePower_re _ (E.boundedSplitCharts h hlin).he₀]
    exact hν
  have he := E.fibrePlug_product_boundary_pair h (1, ν)
  change E.toTorus.cutMap ((E.splitData h).ΘV qV).val =
    E.toTorus.cutMap ((E.splitData h).ΘH qH).val at he
  exact IsConnected.union ⟨E.toTorus.cutMap ((E.splitData h).ΘV qV).val,
    he ▸ hH, hV⟩ (E.fibrePlugHostSide_connected h t) (E.fibrePlugSolidSide_connected h hlin t)

theorem fibrePlug_product_cross_of_cutMap_eq (hn : E.toTorus.pairing.count = 1)
    (q : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (r : pantsPlanarBase.{u}.surface.Carrier × Circle)
    (he : E.toTorus.cutMap ((E.splitData h).ΘV q).val =
      E.toTorus.cutMap ((E.splitData h).ΘH r).val) :
    ∃ τ : Torus, q = ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2) ∧
      r = (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
        ((E.crossMap j b τ).1, halfZero), (E.crossMap j b τ).2) := by
  have hx := ((E.splitData h).ΘV q).property
  have hy := ((E.splitData h).ΘH r).property
  have hi : ∀ a : Fin E.toTorus.pairing.count, a = j := by
    intro a
    apply Fin.ext
    have ha1 := a.isLt
    have hj1 := j.isLt
    omega
  have hb : ∃ τ : Torus, E.toTorus.sideCollar (E.seamSide j b) (τ, halfZero) =
      ((E.splitData h).ΘV q).val := by
    rcases E.toTorus.cutMap_eq_cases he with hxy | ⟨a, hleft | hright⟩
    · have hvh := E.toTorus.eq_of_mem_piece' (hxy ▸ hx) hy
      exact (E.seamPiece_ne_hostPiece h hvh).elim
    · rw [hi a] at hleft
      cases b
      · exact (E.seamPiece_ne_hostPiece h
          (E.toTorus.eq_of_mem_piece' hx (E.toTorus.left_owned j hleft.1))).elim
      · refine ⟨(E.toTorus.pairing.leftParam j).symm
          ⟨((E.splitData h).ΘV q).val, hleft.1⟩, ?_⟩
        change E.toTorus.pairing.leftCollar j
          ((E.toTorus.pairing.leftParam j).symm ⟨_, hleft.1⟩, halfZero) = _
        rw [E.toTorus.pairing.left_zero, Homeomorph.apply_symm_apply]
    · rw [hi a] at hright
      cases b
      · refine ⟨(E.toTorus.pairing.rightParam j).symm
          ⟨((E.splitData h).ΘV q).val, hright.1⟩, ?_⟩
        change E.toTorus.pairing.rightCollar j
          ((E.toTorus.pairing.rightParam j).symm ⟨_, hright.1⟩, halfZero) = _
        rw [E.toTorus.pairing.right_zero, Homeomorph.apply_symm_apply]
      · exact (E.seamPiece_ne_hostPiece h
          (E.toTorus.eq_of_mem_piece' hx (E.toTorus.right_owned j hright.1))).elim
  obtain ⟨τ, hτ⟩ := hb
  have hpV : E.standardPort (E.seamPiece j b) h.1 0 =
      ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ := by
    let : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
      Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
    exact Subsingleton.elim _ _
  have hV := (E.splitData h).hV 0 (τ, halfZero)
    (zero_mem_halfCollarSource τ) (E.splitData h).hδ
  have hv : ((E.splitData h).ΘV
      ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val =
        ((E.splitData h).ΘV q).val := by
    rw [← hV, hpV, E.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource τ)]
    exact hτ
  have hq := (E.splitData h).ΘV.injective (Subtype.ext hv)
  have hp := E.fibrePlug_product_boundary_pair h τ
  rw [hq] at hp
  have hh := E.fibrePlug_host_cutMap_injective h hn
    ((E.splitData h).ΘH r).property
    ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
      ((E.crossMap j b τ).1, halfZero), (E.crossMap j b τ).2)).property (he.symm.trans hp)
  exact ⟨τ, hq.symm, (E.splitData h).ΘH.injective (Subtype.ext hh)⟩

theorem fibrePlug_product_sign_compatible (hn : E.toTorus.pairing.count = 1)
    (q : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (r : pantsPlanarBase.{u}.surface.Carrier × Circle)
    (he : E.toTorus.cutMap ((E.splitData h).ΘV q).val =
      E.toTorus.cutMap ((E.splitData h).ΘH r).val) (t : Bool) :
    (0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h) r.1.val.down)) ↔
      0 < SplitTube.sgnR t * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) := by
  obtain ⟨τ, hq, hr⟩ := E.fibrePlug_product_cross_of_cutMap_eq h hn q r he
  rw [hq, hr]
  have hz : (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
      ((E.crossMap j b τ).1, halfZero)).val.down =
        planarCircleMap 3 (E.fibrePlugFilledHostPort h) (E.crossMap j b τ).1 :=
    planarCollar_zero_val (Or.inr rfl) _ _
  have h0 := h.2.2
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  have hf : (E.crossMap j b τ).1 = τ.2 ^ (E.boundedSplitCharts h hlin).e₀ := by
    rw [hlin.crossMap_apply]
    simp [linearTorusMap, h0]
    rfl
  change (0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
    (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
      (pantsPlanarBase.{u}.collar (E.fibrePlugFilledHostPort h)
        ((E.crossMap j b τ).1, halfZero)).val.down)) ↔ _
  rw [hz, SplitTube.fibrePlug_hostInv_boundary,
    SplitTube.fibrePlug_strip_boundary_sign _ _ (SplitTube.two_le_hostRadius _), hf]

include h in
theorem fibrePlug_solid_cutMap_injective (hn : E.toTorus.pairing.count = 1) :
    InjOn E.toTorus.cutMap (E.toTorus.components.piece (E.seamPiece j b)) := by
  intro x hx y hy he
  have hq := E.toTorus.reconstruction.injective he
  rcases (Quotient.exact hq : E.toTorus.pairing.gluing.rel x y) with he | ⟨a, ha, hay⟩
  · exact he
  · have haj : a = j := by
      apply Fin.ext
      have ha1 := a.isLt
      have hj1 := j.isLt
      omega
    subst a
    have hnVH := E.seamPiece_ne_hostPiece h
    rcases ha with hl | hr
    · have hxL := E.toTorus.left_owned j hl
      have hyR : y ∈ E.toTorus.pairing.gluing.right j := by
        rw [hay, E.toTorus.pairing.gluing.flip_of_mem_left hl]
        exact (E.toTorus.pairing.gluing.attaching j ⟨x, hl⟩).property
      have hyR' := E.toTorus.right_owned j hyR
      cases b
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hx hxL)).elim
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hy hyR')).elim
    · have hxR := E.toTorus.right_owned j hr
      have hyL : y ∈ E.toTorus.pairing.gluing.left j := by
        rw [hay, E.toTorus.pairing.gluing.flip_of_mem_right hr]
        exact ((E.toTorus.pairing.gluing.attaching j).symm ⟨x, hr⟩).property
      have hyL' := E.toTorus.left_owned j hyL
      cases b
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hy hyL')).elim
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hx hxR)).elim

theorem fibrePlugSolidSide_disjoint (hn : E.toTorus.pairing.count = 1) :
    Disjoint (E.fibrePlugSolidSide h hlin false) (E.fibrePlugSolidSide h hlin true) := by
  rw [disjoint_left]
  rintro x ⟨q, hq, rfl⟩ ⟨r, hr, he⟩
  have hp := E.fibrePlug_solid_cutMap_injective h hn
    ((E.splitData h).ΘV r).property ((E.splitData h).ΘV q).property he
  have hqr := (E.splitData h).ΘV.injective (Subtype.ext hp)
  rw [hqr] at hr
  change 0 < -1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hq
  change 0 < 1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hr
  linarith

theorem fibrePlugSide_disjoint (hn : E.toTorus.pairing.count = 1) :
    Disjoint (E.fibrePlugSide h hlin false) (E.fibrePlugSide h hlin true) := by
  rw [disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact disjoint_left.mp (E.fibrePlugHostSide_disjoint h hn) hx hy
  · rcases hx with ⟨r, hr, rfl⟩
    rcases hy with ⟨q, hq, he⟩
    have hp := (E.fibrePlug_product_sign_compatible h hlin hn q r he false).mp hr
    change 0 < -1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hp
    change 0 < 1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hq
    linarith
  · rcases hx with ⟨q, hq, rfl⟩
    rcases hy with ⟨r, hr, he⟩
    have hp := (E.fibrePlug_product_sign_compatible h hlin hn q r he.symm true).mp hr
    change 0 < 1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hp
    change 0 < -1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) at hq
    linarith
  · exact disjoint_left.mp (E.fibrePlugSolidSide_disjoint h hlin hn) hx hy

end GC.Seifert.ElementaryPresentation
