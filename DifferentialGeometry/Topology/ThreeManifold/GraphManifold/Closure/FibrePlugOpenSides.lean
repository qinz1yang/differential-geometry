import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugZeroImage
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugTwoComponentsTopology

/-!
The actual strict sides of the fixed fibre plug are open and exhaust the
complement of its original middle sphere.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.SplitTube

theorem fibrePlug_tube_phase_sign {e : ℤ} (he : e = 1 ∨ e = -1)
    (side t : Bool) (s : ℝ) (hs : 0 < sgnR t * s) :
    0 < sgnR t * (-(((tubeFibre e side s ^ e : Circle) : ℂ).re)) := by
  rw [tubeFibre_zpow he]
  cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true, neg_one_mul, one_mul,
    Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  all_goals rw [cos_hostTheta, neg_div, neg_neg, ← mul_div_assoc]
  all_goals have hm : sgnR t * (tubeSlope * s) = tubeSlope * (sgnR t * s) := by ring
  all_goals rw [hm]
  all_goals exact div_pos (mul_pos (by norm_num [tubeSlope]) hs) (angleScale_pos s)

theorem fibrePlug_tube_junction_general {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (C : SplitCharts M)
    (p : SphereTwo) (s : ℝ) (hp : seamHeight (heightOf p) = 0) :
    C.tubeMap (p, s) = C.seam
      ((unitOf (planeOf p), tubeFibre C.e₀ (SplitCharts.side (p, s)) s), 0) := by
  simp only [SplitCharts.tubeMap, seamModel, hp, lt_self_iff_false, ite_false]

theorem fibrePlug_tube_cap {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (C : SplitCharts M)
    (p : SphereTwo) (s : ℝ) (hp : seamHeight (heightOf p) < 0) :
    C.tubeMap (p, s) = C.solid (capModel C.e₀ (SplitCharts.side (p, s)) (p, s)) := by
  simp only [SplitCharts.tubeMap, hp, ite_true]

theorem fibrePlug_tube_band {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (C : SplitCharts M)
    (p : SphereTwo) (s : ℝ) (hp : 0 < seamHeight (heightOf p)) :
    C.tubeMap (p, s) = C.hostMap (bandModel C.e₀ C.e₁ C.d C.host (p, s)) := by
  simp only [SplitCharts.tubeMap, not_lt_of_ge hp.le, hp, ite_false, ite_true]

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
variable {j : Fin E.toTorus.pairing.count} {b : Bool}
variable (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
variable (hn : E.toTorus.pairing.count = 1)

include hn in
theorem fibrePlug_host_side_iff (q : pantsPlanarBase.{u}.surface.Carrier × Circle) (t : Bool) :
    E.toTorus.cutMap ((E.splitData h).ΘH q).val ∈ E.fibrePlugSide h hlin t ↔
      0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
        (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) := by
  constructor
  · rintro (hx | hx)
    · obtain ⟨r, hr, he⟩ := hx
      have hi := E.fibrePlug_host_cutMap_injective h hn
        ((E.splitData h).ΘH r).property ((E.splitData h).ΘH q).property he
      have hq := (E.splitData h).ΘH.injective (Subtype.ext hi)
      rwa [hq] at hr
    · obtain ⟨r, hr, he⟩ := hx
      exact (E.fibrePlug_product_sign_compatible h hlin hn r q he t).mpr hr
  · intro hq
    exact Or.inl ⟨q, hq, rfl⟩

include hn in
theorem fibrePlug_solid_side_iff (q : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (t : Bool) :
    E.toTorus.cutMap ((E.splitData h).ΘV q).val ∈ E.fibrePlugSide h hlin t ↔
      0 < SplitTube.sgnR t * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re)) := by
  constructor
  · rintro (hx | hx)
    · obtain ⟨r, hr, he⟩ := hx
      exact (E.fibrePlug_product_sign_compatible h hlin hn q r he.symm t).mp hr
    · obtain ⟨r, hr, he⟩ := hx
      have hi := E.fibrePlug_solid_cutMap_injective h hn
        ((E.splitData h).ΘV r).property ((E.splitData h).ΘV q).property he
      have hq := (E.splitData h).ΘV.injective (Subtype.ext hi)
      rwa [hq] at hr
  · intro hq
    exact Or.inr ⟨q, hq, rfl⟩

def fibrePlugCutSide (t : Bool) : Set E.toTorus.cutCarrier.Carrier :=
  (fun q : pantsPlanarBase.{u}.surface.Carrier × Circle => ((E.splitData h).ΘH q).val) ''
    {q | 0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down)} ∪
  (fun q : (discPlanarBase.{u} 1).surface.Carrier × Circle => ((E.splitData h).ΘV q).val) ''
    {q | 0 < SplitTube.sgnR t * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))}

theorem fibrePlugCutSide_isOpen (t : Bool) : IsOpen (E.fibrePlugCutSide h hlin t) := by
  apply IsOpen.union
  · have hc : Continuous (fun q : pantsPlanarBase.{u}.surface.Carrier × Circle =>
        q.1.val.down) := continuous_uliftDown.comp (continuous_subtype_val.comp continuous_fst)
    have hi : Continuous (fun q : pantsPlanarBase.{u}.surface.Carrier × Circle =>
        SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) := by
      by_cases hl : (E.fibrePlugFilledHostPort h).val = 0
      · simpa only [SplitTube.hostInv, hl, ite_true] using hc
      · simp only [SplitTube.hostInv, hl, ite_false]
        refine (hc.sub continuous_const).inv₀ ?_
        intro q
        have hr := ((mem_planarSet_iff (Or.inr rfl) _).mp q.1.property).2
          (E.fibrePlugFilledHostPort h) hl
        exact norm_ne_zero_iff.mp (by linarith :
          ‖q.1.val.down - (planarCenter 3 (E.fibrePlugFilledHostPort h) : ℂ)‖ ≠ 0)
    have hs : IsOpen {q : pantsPlanarBase.{u}.surface.Carrier × Circle |
        0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
          (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down)} :=
      isOpen_lt continuous_const (continuous_const.mul
        ((SplitTube.contDiff_stripLevel (E.fibrePlugFilledHostPort h)).continuous.comp hi))
    have hm := (E.toTorus.components.piece (E.hostPiece j b)).isOpen.isOpenMap_subtype_val _
      ((E.splitData h).ΘH.toHomeomorph.isOpenMap _ hs)
    simpa only [image_image, Function.comp_def, Diffeomorph.coe_toHomeomorph] using hm
  · have hc : Continuous (fun q : (discPlanarBase.{u} 1).surface.Carrier × Circle =>
        (q.2 : ℂ).re) := by fun_prop
    have hs : IsOpen {q : (discPlanarBase.{u} 1).surface.Carrier × Circle |
        0 < SplitTube.sgnR t * (-(q.2 : ℂ).re)} :=
      isOpen_lt continuous_const (continuous_const.mul hc.neg)
    have he : {q : (discPlanarBase.{u} 1).surface.Carrier × Circle |
        0 < SplitTube.sgnR t * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))} =
          {q | 0 < SplitTube.sgnR t * (-(q.2 : ℂ).re)} := by
      ext q
      change (0 < SplitTube.sgnR t *
        (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))) ↔ _
      rw [SplitTube.fibrePlug_circlePower_re _ (E.boundedSplitCharts h hlin).he₀]
      rfl
    rw [he]
    have hm := (E.toTorus.components.piece (E.seamPiece j b)).isOpen.isOpenMap_subtype_val _
      ((E.splitData h).ΘV.toHomeomorph.isOpenMap _ hs)
    simpa only [image_image, Function.comp_def, Diffeomorph.coe_toHomeomorph] using hm

include hn in
theorem fibrePlug_side_preimage (hc : E.toTorus.components.count = 2) (t : Bool) :
    E.toTorus.cutMap ⁻¹' E.fibrePlugSide h hlin t = E.fibrePlugCutSide h hlin t := by
  ext x
  constructor
  · intro hx
    rcases E.fibrePlug_cut_cover h hc x with hv | hh
    · let q := (E.splitData h).ΘV.symm ⟨x, hv⟩
      have he : ((E.splitData h).ΘV q).val = x :=
        congrArg Subtype.val ((E.splitData h).ΘV.apply_symm_apply ⟨x, hv⟩)
      right
      refine ⟨q, ?_, he⟩
      apply (E.fibrePlug_solid_side_iff h hlin hn q t).mp
      rwa [he]
    · let q := (E.splitData h).ΘH.symm ⟨x, hh⟩
      have he : ((E.splitData h).ΘH q).val = x :=
        congrArg Subtype.val ((E.splitData h).ΘH.apply_symm_apply ⟨x, hh⟩)
      left
      refine ⟨q, ?_, he⟩
      apply (E.fibrePlug_host_side_iff h hlin hn q t).mp
      rwa [he]
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact (E.fibrePlug_host_side_iff h hlin hn q t).mpr hq
    · exact (E.fibrePlug_solid_side_iff h hlin hn q t).mpr hq

include hn in
theorem fibrePlugSide_isOpen (hc : E.toTorus.components.count = 2) (t : Bool) :
    IsOpen (E.fibrePlugSide h hlin t) := by
  have hq : IsQuotientMap E.toTorus.cutMap :=
    E.toTorus.reconstruction.isQuotientMap.comp isQuotientMap_quotient_mk'
  apply hq.isCoinducing.isOpen_preimage.mp
  rw [E.fibrePlug_side_preimage h hlin hn hc t]
  exact E.fibrePlugCutSide_isOpen h hlin t

include hn in
theorem fibrePlug_zero_side_disjoint (t : Bool) :
    Disjoint (E.fibrePlugHostZero h ∪ E.fibrePlugSolidZero h hlin)
      (E.fibrePlugSide h hlin t) := by
  rw [disjoint_left]
  intro x hx hy
  rcases hx with hx | hx
  · obtain ⟨q, hq, rfl⟩ := hx
    have hp := (E.fibrePlug_host_side_iff h hlin hn q t).mp hy
    change SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) = 0 at hq
    rw [hq, mul_zero] at hp
    exact lt_irrefl 0 hp
  · obtain ⟨q, hq, rfl⟩ := hx
    have hp := (E.fibrePlug_solid_side_iff h hlin hn q t).mp hy
    change (((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re) = 0 at hq
    rw [hq, neg_zero, mul_zero] at hp
    exact lt_irrefl 0 hp

include hn in
theorem fibrePlug_sphere_complement (hc : E.toTorus.components.count = 2) :
    (range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)))ᶜ =
      E.fibrePlugSide h hlin false ∪ E.fibrePlugSide h hlin true := by
  rw [E.fibrePlug_middle_zero_image h hlin]
  ext x
  constructor
  · intro hx
    rcases E.fibrePlug_product_cover h hc x with ⟨q, hq⟩ | ⟨q, hq⟩
    · rw [← hq]
      have hz : (((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re) ≠ 0 := by
        intro hz
        exact hx (Or.inr ⟨q, hz, hq⟩)
      rcases lt_or_gt_of_ne hz with hm | hp
      · right
        apply (E.fibrePlug_solid_side_iff h hlin hn q true).mpr
        change 0 < 1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))
        linarith
      · left
        apply (E.fibrePlug_solid_side_iff h hlin hn q false).mpr
        change 0 < -1 * (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))
        linarith
    · rw [← hq]
      have hz : SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
          (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) ≠ 0 := by
        intro hz
        exact hx (Or.inl ⟨q, hz, hq⟩)
      rcases lt_or_gt_of_ne hz with hm | hp
      · left
        apply (E.fibrePlug_host_side_iff h hlin hn q false).mpr
        change 0 < -1 * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
          (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down)
        linarith
      · right
        apply (E.fibrePlug_host_side_iff h hlin hn q true).mpr
        change 0 < 1 * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
          (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down)
        linarith
  · rintro (hx | hx) hy
    · exact disjoint_left.mp (E.fibrePlug_zero_side_disjoint h hlin hn false) hy hx
    · exact disjoint_left.mp (E.fibrePlug_zero_side_disjoint h hlin hn true) hy hx

theorem fibrePlug_cap_tube_closed (p : SphereTwo) (s : ℝ)
    (hp : SplitTube.seamHeight (SplitTube.heightOf p) ≤ 0) :
    E.boundedSplitTubeMap h hlin (p, s) =
      E.toTorus.pieceChart (E.seamPiece j b) (discPlanarBase 1)
        (E.splitData h).ΘV clampDisc
          (SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
            (SplitTube.SplitCharts.side (p, s)) (p, s)) := by
  rcases lt_or_eq_of_le hp with hneg | hz
  · have hn : ‖(SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (p, s)) (p, s)).1‖ < 3 := by
      change ‖(6 : ℝ) • SplitTube.planeOf p‖ < 3
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have hp' := (SplitTube.seamHeight_neg_iff p).mp hneg
      linarith
    have ht := SplitTube.fibrePlug_tube_cap (E.boundedSplitCharts h hlin) p s hneg
    exact (congrArg (boundedSplitInteriorVal W) ht).trans
      (E.boundedSplitCharts_solid_val h hlin _ hn)
  · let τ : Torus := (unitOf (SplitTube.planeOf p),
      SplitTube.tubeFibre (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (p, s)) s)
    have ht := SplitTube.fibrePlug_tube_junction_general
      (E.boundedSplitCharts h hlin) p s hz
    have hτ : |(τ, (0 : ℝ)).2| < 1 := by norm_num
    have hv := E.boundedSplitCharts_seam_val h hlin (τ, 0) hτ
    have he : E.boundedSplitTubeMap h hlin (p, s) =
        E.toTorus.cutMap ((E.splitData h).ΘV
          ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val :=
      (congrArg (boundedSplitInteriorVal W) ht).trans
        (hv.trans (E.fibrePlug_solid_zero_seam h τ))
    rw [he]
    change E.toTorus.cutMap ((E.splitData h).ΘV
      ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val =
        E.toTorus.cutMap ((E.splitData h).ΘV
          (clampDisc ((6 : ℝ) • SplitTube.planeOf p), τ.2)).val
    congr 3
    apply Prod.ext
    · have hd := discCollar_eq.{u} (θ := unitOf (SplitTube.planeOf p)) le_rfl zero_lt_one
      change (discPlanarBase.{u} 1).collar 0 (unitOf (SplitTube.planeOf p), halfZero) =
        clampDisc ((3 - 3 * (0 : ℝ) / 2 : ℝ) • (unitOf (SplitTube.planeOf p) : ℂ)) at hd
      apply hd.trans
      apply congrArg clampDisc
      have hn : ‖SplitTube.planeOf p‖ = 1 / 2 := by
        rw [SplitTube.seamHeight, SplitTube.latRadius_heightOf] at hz
        linarith
      rw [show (3 - 3 * (0 : ℝ) / 2 : ℝ) = 3 by norm_num]
      calc
        (3 : ℝ) • (unitOf (SplitTube.planeOf p) : ℂ) =
            (6 : ℝ) • (‖SplitTube.planeOf p‖ •
              (unitOf (SplitTube.planeOf p) : ℂ)) := by rw [hn, smul_smul]; norm_num
        _ = (6 : ℝ) • SplitTube.planeOf p :=
          congrArg (fun w : ℂ => (6 : ℝ) • w) (norm_smul_unitOf _)
    · rfl

theorem fibrePlug_tube_side (t : Bool) (p : SphereTwo) (s : ℝ)
    (hs : |s| < 3) (ht : 0 < SplitTube.sgnR t * s) :
    E.boundedSplitTubeMap h hlin (p, s) ∈ E.fibrePlugSide h hlin t := by
  by_cases hp : SplitTube.seamHeight (SplitTube.heightOf p) ≤ 0
  · right
    let q := SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
      (SplitTube.SplitCharts.side (p, s)) (p, s)
    refine ⟨(clampDisc q.1, q.2), ?_, (E.fibrePlug_cap_tube_closed h hlin p s hp).symm⟩
    exact SplitTube.fibrePlug_tube_phase_sign (E.boundedSplitCharts h hlin).he₀ _ t s ht
  · left
    have hp' : 0 < SplitTube.seamHeight (SplitTube.heightOf p) := lt_of_not_ge hp
    let q := SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
      (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
      (E.boundedSplitCharts h hlin).host (p, s)
    have hq : q.1 ∈ SplitTube.pantsInterior :=
      (SplitTube.hostChart_strip_mem (E.boundedSplitCharts h hlin).host
        (SplitTube.abs_heightOf_lt_of_seamHeight_pos hp') hp' hs).1
    have he : E.boundedSplitTubeMap h hlin (p, s) =
        E.toTorus.pieceChart (E.hostPiece j b) pantsPlanarBase
          (E.splitData h).ΘH clampPants q := by
      have ht := SplitTube.fibrePlug_tube_band (E.boundedSplitCharts h hlin) p s hp'
      exact (congrArg (boundedSplitInteriorVal W) ht).trans
        (E.boundedSplitCharts_host_val h hlin q hq)
    refine ⟨(clampPants q.1, q.2), ?_, he.symm⟩
    change 0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h) (clampPants q.1).val.down)
    rw [clampPants_val (SplitTube.pantsInterior_subset hq)]
    change 0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
        (SplitTube.bandBase (E.fibrePlugFilledHostPort h) (SplitTube.heightOf p, s)))
    rw [SplitTube.fibrePlug_band_level]
    exact ht

def fibrePlugSphereComponentsEquiv (hc : E.toTorus.components.count = 2) :
    ConnectedComponents ↥((range (fun z : SphereTwo =>
      E.boundedSplitTubeMap h hlin (z, 0)))ᶜ) ≃ Bool :=
  twoOpenSidesComponentsEquiv (E.fibrePlugSide h hlin)
    (range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)))
    (E.fibrePlugSide_connected h hlin) (E.fibrePlugSide_disjoint h hlin hn)
    (E.fibrePlugSide_isOpen h hlin hn hc) (E.fibrePlug_sphere_complement h hlin hn hc)

include hn in
theorem fibrePlugSphereComponentsEquiv_mk_eq_iff (hc : E.toTorus.components.count = 2)
    (x : ↥((range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)))ᶜ)) (t : Bool) :
    E.fibrePlugSphereComponentsEquiv h hlin hn hc (ConnectedComponents.mk x) = t ↔
      x.val ∈ E.fibrePlugSide h hlin t :=
  twoOpenSidesComponentsEquiv_mk_eq_iff (E.fibrePlugSide h hlin)
    (range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)))
    (E.fibrePlugSide_connected h hlin) (E.fibrePlugSide_disjoint h hlin hn)
    (E.fibrePlugSide_isOpen h hlin hn hc) (E.fibrePlug_sphere_complement h hlin hn hc) x t

include hn in
theorem fibrePlug_sphere_connectedComponentIn (hc : E.toTorus.components.count = 2)
    (t : Bool) (x : W.Carrier) (hx : x ∈ E.fibrePlugSide h hlin t) :
    connectedComponentIn (range (fun z : SphereTwo =>
      E.boundedSplitTubeMap h hlin (z, 0)))ᶜ x = E.fibrePlugSide h hlin t :=
  twoOpenSides_connectedComponentIn (E.fibrePlugSide h hlin)
    (range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)))
    (E.fibrePlugSide_connected h hlin) (E.fibrePlugSide_disjoint h hlin hn)
    (E.fibrePlugSide_isOpen h hlin hn hc) (E.fibrePlug_sphere_complement h hlin hn hc) t x hx

include hn in
theorem fibrePlug_sphere_components_card (hc : E.toTorus.components.count = 2) :
    Nat.card (ConnectedComponents ↥((range (fun z : SphereTwo =>
      E.boundedSplitTubeMap h hlin (z, 0)))ᶜ)) = 2 :=
  twoOpenSides_components_card (E.fibrePlugSide h hlin)
    (range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)))
    (E.fibrePlugSide_connected h hlin) (E.fibrePlugSide_disjoint h hlin hn)
    (E.fibrePlugSide_isOpen h hlin hn hc) (E.fibrePlug_sphere_complement h hlin hn hc)

include hn in
theorem fibrePlug_external_connectedComponent (hc : E.toTorus.components.count = 2)
    (t : Bool) (τ : Torus) :
    connectedComponentIn (range (fun z : SphereTwo =>
      E.boundedSplitTubeMap h hlin (z, 0)))ᶜ
        (E.toTorus.external.collar (E.fibrePlugSideExternalEquiv h hc hn t) (τ, halfZero)) =
          E.fibrePlugSide h hlin t :=
  E.fibrePlug_sphere_connectedComponentIn h hlin hn hc t _
    (E.fibrePlug_external_mem_side h hc hn hlin t τ)

end GC.Seifert.ElementaryPresentation

namespace GC.GraphManifold

theorem exists_separating_fibrePlug :
    ∃ (W : CompactCarrier.{u}) (E : GC.Seifert.ElementaryPresentation W)
      (j : Fin E.toTorus.pairing.count), W.kind = .withBoundary ∧
      E.toTorus.externalCount = 2 ∧
      ∃ (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
        (h : E.IsSplitSeam j true) (hlin : E.IsLinearSeam j),
      ∃ d : PartialDiffeomorph sphereSignedCollarModel W.model
        (ClosureSphere.{u} × ℝ) W.Carrier ∞,
        d.source = sphereSignedCollarSource ∧ d.target ⊆ W.interior ∧
        (∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s)) ∧
        ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ 1 ∧
          (∀ r, Disjoint d.target
            (GC.Seifert.shrinkHalfCollar hρ (E.toTorus.external.collar r)).target) ∧
          Nat.card (ConnectedComponents ↥((range (fun z : ClosureSphere.{u} => d (z, 0)))ᶜ)) = 2 ∧
          ∀ t τ, connectedComponentIn (range (fun z : ClosureSphere.{u} => d (z, 0)))ᶜ
            (E.toTorus.external.collar (E.fibrePlugSideExternalEquiv h hc hn t) (τ, halfZero)) =
              E.fibrePlugSide h hlin t := by
  obtain ⟨W, E, j, hW, hc, hn, he, h, hlin⟩ := exists_fibrePlug.{u}
  obtain ⟨d, hd, hdi, hformula, ρ, hρ, hρ1, hav⟩ :=
    E.exists_boundedSplitSignedTube j true h hlin
  have hz : range (fun z : ClosureSphere.{u} => d (z, 0)) =
      range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.down, (hformula z 0).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨ULift.up z, hformula (ULift.up z) 0⟩
  refine ⟨W, E, j, hW, he, hc, hn, h, hlin, d, hd, hdi, hformula,
    ρ, hρ, hρ1, hav, ?_, ?_⟩
  · rw [hz]
    exact E.fibrePlug_sphere_components_card h hlin hn hc
  · intro t τ
    rw [hz]
    exact E.fibrePlug_external_connectedComponent h hlin hn hc t τ

end GC.GraphManifold
