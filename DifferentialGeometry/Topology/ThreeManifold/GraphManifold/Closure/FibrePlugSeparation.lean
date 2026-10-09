import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSphere
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelPorts

/-!
Actual two-piece product coverage and retained host markings for the bounded fibre plug.
Native strip levels identify the zero band and distinguish the two retained model ports.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
variable {j : Fin E.toTorus.pairing.count} {b : Bool}
variable (h : E.IsSplitSeam j b) (hc : E.toTorus.components.count = 2)

include h hc in
theorem fibrePlug_piece_exhaustion (k : Fin E.toTorus.components.count) :
    k = E.seamPiece j b ∨ k = E.hostPiece j b := by
  have hn := E.seamPiece_ne_hostPiece h
  have hvh : (E.seamPiece j b).val ≠ (E.hostPiece j b).val := fun he => hn (Fin.ext he)
  have hv := (E.seamPiece j b).isLt
  have hh := (E.hostPiece j b).isLt
  have hk := k.isLt
  by_cases hvk : k.val = (E.seamPiece j b).val
  · exact Or.inl (Fin.ext hvk)
  · right
    apply Fin.ext
    omega

include h hc in
theorem fibrePlug_cut_cover (x : E.toTorus.cutCarrier.Carrier) :
    x ∈ E.toTorus.components.piece (E.seamPiece j b) ∨
      x ∈ E.toTorus.components.piece (E.hostPiece j b) := by
  have hx : x ∈ ⋃ k, (E.toTorus.components.piece k : Set E.toTorus.cutCarrier.Carrier) := by
    rw [E.toTorus.components.covers]
    trivial
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  rcases E.fibrePlug_piece_exhaustion h hc k with rfl | rfl
  · exact Or.inl hk
  · exact Or.inr hk

include h hc in
theorem fibrePlug_external_owner (r : Fin E.toTorus.externalCount) :
    E.toTorus.externalPiece r = E.hostPiece j b := by
  rcases E.fibrePlug_piece_exhaustion h hc (E.toTorus.externalPiece r) with he | he
  · have hs : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
      Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
    have hp := congrArg Subtype.val (Subsingleton.elim
      (⟨.inr (.inr r), he⟩ : E.toTorus.OwnedSide (E.seamPiece j b))
      ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩)
    cases b <;> cases hp
  · exact he

include hc in
theorem fibrePlug_product_cover (x : W.Carrier) :
    (∃ q : (discPlanarBase.{u} 1).surface.Carrier × Circle,
      E.toTorus.cutMap ((E.splitData h).ΘV q).val = x) ∨
    (∃ q : pantsPlanarBase.{u}.surface.Carrier × Circle,
      E.toTorus.cutMap ((E.splitData h).ΘH q).val = x) := by
  obtain ⟨q, rfl⟩ := E.toTorus.reconstruction.surjective x
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  rcases E.fibrePlug_cut_cover h hc y with hv | hh
  · obtain ⟨q, hq⟩ := (E.splitData h).ΘV.surjective ⟨y, hv⟩
    exact Or.inl ⟨q, congrArg (fun z => E.toTorus.cutMap z.val) hq⟩
  · obtain ⟨q, hq⟩ := (E.splitData h).ΘH.surjective ⟨y, hh⟩
    exact Or.inr ⟨q, congrArg (fun z => E.toTorus.cutMap z.val) hq⟩

def fibrePlugFilledHostPort : Fin 3 :=
  (E.standardPort (E.hostPiece j b) h.2.1).symm
    ⟨E.seamSide j (!b), E.sidePiece_seamSide j (!b)⟩

def fibrePlugExternalHostPort (r : Fin E.toTorus.externalCount) : Fin 3 :=
  (E.standardPort (E.hostPiece j b) h.2.1).symm
    ⟨.inr (.inr r), E.fibrePlug_external_owner h hc r⟩

theorem fibrePlugExternalHostPort_injective : Injective (E.fibrePlugExternalHostPort h hc) := by
  intro r s he
  have hp := (E.standardPort (E.hostPiece j b) h.2.1).symm.injective he
  have hv := congrArg Subtype.val hp
  exact Sum.inr.inj (Sum.inr.inj hv)

theorem fibrePlugExternalHostPort_ne (r : Fin E.toTorus.externalCount) :
    E.fibrePlugExternalHostPort h hc r ≠ E.fibrePlugFilledHostPort h := by
  intro he
  have hp := (E.standardPort (E.hostPiece j b) h.2.1).symm.injective he
  have hv := congrArg Subtype.val hp
  cases b <;> cases hv

theorem fibrePlugExternalHostPort_surjective
    (hn : E.toTorus.pairing.count = 1)
    (l : Fin 3) (hl : l ≠ E.fibrePlugFilledHostPort h) :
    ∃ r, E.fibrePlugExternalHostPort h hc r = l := by
  let s := E.standardPort (E.hostPiece j b) h.2.1 l
  have hj (c : Fin E.toTorus.pairing.count) : c = j := by
    apply Fin.ext
    have hc1 := c.isLt
    have hj1 := j.isLt
    omega
  rcases hs : s.val with c | c | r
  · have hcj := hj c
    subst c
    have hp : E.toTorus.sidePiece (.inl j) = E.hostPiece j b := by
      rw [← hs]
      exact s.property
    cases b
    · exfalso
      apply hl
      apply (E.standardPort (E.hostPiece j false) h.2.1).injective
      rw [fibrePlugFilledHostPort, Equiv.apply_symm_apply]
      exact Subtype.ext hs
    · exact (E.seamPiece_ne_hostPiece h hp).elim
  · have hcj := hj c
    subst c
    have hp : E.toTorus.sidePiece (.inr (.inl j)) = E.hostPiece j b := by
      rw [← hs]
      exact s.property
    cases b
    · exact (E.seamPiece_ne_hostPiece h hp).elim
    · exfalso
      apply hl
      apply (E.standardPort (E.hostPiece j true) h.2.1).injective
      rw [fibrePlugFilledHostPort, Equiv.apply_symm_apply]
      exact Subtype.ext hs
  · refine ⟨r, ?_⟩
    apply (E.standardPort (E.hostPiece j b) h.2.1).injective
    rw [fibrePlugExternalHostPort, Equiv.apply_symm_apply]
    exact Subtype.ext hs.symm

def fibrePlugExternalHostPortEquiv (hn : E.toTorus.pairing.count = 1) :
    Fin E.toTorus.externalCount ≃ {l : Fin 3 // l ≠ E.fibrePlugFilledHostPort h} :=
  Equiv.ofBijective
    (fun r => ⟨E.fibrePlugExternalHostPort h hc r, E.fibrePlugExternalHostPort_ne h hc r⟩)
    ⟨fun r s he => E.fibrePlugExternalHostPort_injective h hc (congrArg Subtype.val he),
      fun l => by
        obtain ⟨r, hr⟩ := E.fibrePlugExternalHostPort_surjective h hc hn l.val l.property
        exact ⟨r, Subtype.ext hr⟩⟩

theorem fibrePlug_external_germ (r : Fin E.toTorus.externalCount)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource)
    (hs : p.2.val 0 < (E.splitData h).δ) :
    E.toTorus.external.collar r p = E.toTorus.cutMap
      ((E.splitData h).ΘH
        (pantsPlanarBase.collar (E.fibrePlugExternalHostPort h hc r) (p.1.1, p.2), p.1.2)).val := by
  have he := (E.splitData h).hH (E.fibrePlugExternalHostPort h hc r) p hp hs
  rw [fibrePlugExternalHostPort, Equiv.apply_symm_apply] at he
  have he' := congrArg (fun z => E.toTorus.cutMap z.val) he
  rw [E.toTorus.pieceCollar_apply _ _ hp] at he'
  exact (E.toTorus.marked_collar r p hp).symm.trans he'

theorem fibrePlug_external_zero (r : Fin E.toTorus.externalCount) (t : Torus) :
    E.toTorus.external.collar r (t, halfZero) = E.toTorus.cutMap
      ((E.splitData h).ΘH
        (pantsPlanarBase.collar (E.fibrePlugExternalHostPort h hc r)
          (t.1, halfZero), t.2)).val := by
  have he := (E.splitData h).hH (E.fibrePlugExternalHostPort h hc r)
    (t, halfZero) (zero_mem_halfCollarSource t) (E.splitData h).hδ
  rw [fibrePlugExternalHostPort, Equiv.apply_symm_apply] at he
  have he' := congrArg (fun z => E.toTorus.cutMap z.val) he
  rw [E.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource t)] at he'
  exact (E.toTorus.marked_collar r (t, halfZero) (zero_mem_halfCollarSource t)).symm.trans he'

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert.SplitTube

def fibrePlugSidePortEquiv (l : Fin 3) : Bool ≃ {p : Fin 3 // p ≠ l} where
  toFun t := ⟨sidePort l t, sidePort_ne l t⟩
  invFun p := decide (p.val = sidePort l true)
  left_inv t := by
    fin_cases l <;> cases t <;> simp [sidePort]
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨p, hp⟩
    fin_cases l <;> fin_cases p <;> first | exact (hp rfl).elim | decide +revert

theorem fibrePlug_band_level (l : Fin 3) (x s : ℝ) :
    stripLevel l (hostInv l (bandBase l (x, s))) = s := by
  rw [bandBase, hostInv_hostChart, stripLevel_strip]

theorem fibrePlug_retained_port_level (l : Fin 3) (t : Bool) (θ : Circle) :
    3 < sgnR t * stripLevel l
      (hostInv l (planarCollarFormula 3 (sidePort l t) ((θ : ℂ), 0))) := by
  exact (lt_sgnR_mul_stripLevel l t
    (planarCollarFormula_mem_outerCollarRegion (sidePort l t) θ le_rfl (by norm_num))).2

theorem fibrePlug_cap_fibre_zero (e : ℤ) (he : e = 1 ∨ e = -1) (t : Bool) :
    ((tubeFibre e t 0 : Circle) : ℂ).re = 0 := by
  rcases he with rfl | rfl <;> cases t <;>
    simp [tubeFibre, hostTheta, Circle.coe_exp]

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
variable {j : Fin E.toTorus.pairing.count} {b : Bool}
variable (h : E.IsSplitSeam j b) (hc : E.toTorus.components.count = 2)
variable (hn : E.toTorus.pairing.count = 1)

def fibrePlugSideExternalEquiv : Bool ≃ Fin E.toTorus.externalCount :=
  (SplitTube.fibrePlugSidePortEquiv (E.fibrePlugFilledHostPort h)).trans
    (E.fibrePlugExternalHostPortEquiv h hc hn).symm

theorem fibrePlugSideExternalEquiv_port (t : Bool) :
    E.fibrePlugExternalHostPort h hc (E.fibrePlugSideExternalEquiv h hc hn t) =
      SplitTube.sidePort (E.fibrePlugFilledHostPort h) t := by
  exact congrArg Subtype.val ((E.fibrePlugExternalHostPortEquiv h hc hn).apply_symm_apply
    (SplitTube.fibrePlugSidePortEquiv (E.fibrePlugFilledHostPort h) t))

theorem fibrePlug_side_external_zero (t : Bool) (τ : Torus) :
    E.toTorus.external.collar (E.fibrePlugSideExternalEquiv h hc hn t) (τ, halfZero) =
      E.toTorus.cutMap ((E.splitData h).ΘH
        (pantsPlanarBase.collar (SplitTube.sidePort (E.fibrePlugFilledHostPort h) t)
          (τ.1, halfZero), τ.2)).val := by
  rw [E.fibrePlug_external_zero h hc, E.fibrePlugSideExternalEquiv_port h hc hn]

include hc hn in
theorem fibrePlug_side_external_level (t : Bool) (θ : Circle) :
    3 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
        (pantsPlanarBase.{u}.collar
          (E.fibrePlugExternalHostPort h hc (E.fibrePlugSideExternalEquiv h hc hn t))
          (θ, halfZero)).val.down) := by
  rw [E.fibrePlugSideExternalEquiv_port h hc hn]
  change 3 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
    (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
      (planarCollarMap.{u} 3 (Or.inr rfl)
        (SplitTube.sidePort (E.fibrePlugFilledHostPort h) t) (θ, halfZero)).val.down)
  rw [planarCollarMap_val (Or.inr rfl) _ (by change (0 : ℝ) < 1; norm_num)]
  exact SplitTube.fibrePlug_retained_port_level (E.fibrePlugFilledHostPort h) t θ


theorem fibrePlug_middle_band (hlin : E.IsLinearSeam j) (z : SphereTwo)
    (hz : 0 < SplitTube.seamHeight (SplitTube.heightOf z)) :
    E.boundedSplitTubeMap h hlin (z, 0) = E.toTorus.pieceChart (E.hostPiece j b)
      pantsPlanarBase (E.splitData h).ΘH clampPants
        (SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
          (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
          (E.boundedSplitCharts h hlin).host (z, 0)) ∧
    SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
        (SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
          (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
          (E.boundedSplitCharts h hlin).host (z, 0)).1) = 0 := by
  constructor
  · have hm := (SplitTube.hostChart_strip_mem (E.boundedSplitCharts h hlin).host
      (SplitTube.abs_heightOf_lt_of_seamHeight_pos hz) hz
      (by norm_num : |(0 : ℝ)| < 3)).1
    unfold boundedSplitTubeMap SplitTube.SplitCharts.tubeMap
    simp only [Function.comp_apply, not_lt_of_ge hz.le, hz, ite_eq_left]
    exact E.boundedSplitCharts_host_val h hlin _ hm
  · change SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
      (SplitTube.hostInv (E.fibrePlugFilledHostPort h)
        (SplitTube.bandBase (E.fibrePlugFilledHostPort h) (SplitTube.heightOf z, 0))) = 0
    exact SplitTube.fibrePlug_band_level _ _ _

theorem fibrePlug_middle_cap (hlin : E.IsLinearSeam j) (z : SphereTwo)
    (hz : SplitTube.seamHeight (SplitTube.heightOf z) < 0) :
    E.boundedSplitTubeMap h hlin (z, 0) = E.toTorus.pieceChart (E.seamPiece j b)
      (discPlanarBase 1) (E.splitData h).ΘV clampDisc
        (SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
          (SplitTube.SplitCharts.side (z, 0)) (z, 0)) ∧
    (((SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
      (SplitTube.SplitCharts.side (z, 0)) (z, 0)).2 : Circle) : ℂ).re = 0 := by
  constructor
  · have hm : ‖(SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (z, 0)) (z, 0)).1‖ < 3 := by
      change ‖(6 : ℝ) • SplitTube.planeOf z‖ < 3
      have hn := (SplitTube.seamHeight_neg_iff z).mp hz
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      linarith
    unfold boundedSplitTubeMap SplitTube.SplitCharts.tubeMap
    simp only [Function.comp_apply, hz, ite_eq_left]
    exact E.boundedSplitCharts_solid_val h hlin _ hm
  · exact SplitTube.fibrePlug_cap_fibre_zero _ (E.boundedSplitCharts h hlin).he₀ _

def fibrePlugHostSide (t : Bool) : Set W.Carrier :=
  (fun q : pantsPlanarBase.{u}.surface.Carrier × Circle =>
    E.toTorus.cutMap ((E.splitData h).ΘH q).val) ''
      {q | 0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
        (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down)}

def fibrePlugSolidSide (hlin : E.IsLinearSeam j) (t : Bool) : Set W.Carrier :=
  (fun q : (discPlanarBase.{u} 1).surface.Carrier × Circle =>
    E.toTorus.cutMap ((E.splitData h).ΘV q).val) ''
      {q | 0 < SplitTube.sgnR t *
        (-(((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re))}

def fibrePlugSide (hlin : E.IsLinearSeam j) (t : Bool) : Set W.Carrier :=
  E.fibrePlugHostSide h t ∪ E.fibrePlugSolidSide h hlin t

include hc hn in
theorem fibrePlug_external_mem_side (hlin : E.IsLinearSeam j) (t : Bool) (τ : Torus) :
    E.toTorus.external.collar (E.fibrePlugSideExternalEquiv h hc hn t) (τ, halfZero) ∈
      E.fibrePlugSide h hlin t := by
  left
  let q : pantsPlanarBase.{u}.surface.Carrier × Circle :=
    (pantsPlanarBase.collar (SplitTube.sidePort (E.fibrePlugFilledHostPort h) t)
      (τ.1, halfZero), τ.2)
  refine ⟨q, ?_, (E.fibrePlug_side_external_zero h hc hn t τ).symm⟩
  have hp := E.fibrePlug_side_external_level h hc hn t τ.1
  rw [E.fibrePlugSideExternalEquiv_port h hc hn] at hp
  change 0 < SplitTube.sgnR t * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
    (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down)
  exact lt_trans (by norm_num : (0 : ℝ) < 3) hp

include hc hn in
theorem fibrePlug_external_range_side (hlin : E.IsLinearSeam j) (t : Bool) :
    range (fun τ : Torus =>
      E.toTorus.external.collar (E.fibrePlugSideExternalEquiv h hc hn t) (τ, halfZero)) ⊆
        E.fibrePlugSide h hlin t := by
  rintro x ⟨τ, rfl⟩
  exact E.fibrePlug_external_mem_side h hc hn hlin t τ

include h in
theorem fibrePlug_host_cutMap_injective (hn : E.toTorus.pairing.count = 1) :
    InjOn E.toTorus.cutMap (E.toTorus.components.piece (E.hostPiece j b)) := by
  intro x hx y hy he
  have hq := E.toTorus.reconstruction.injective he
  rcases (Quotient.exact hq : E.toTorus.pairing.gluing.rel x y) with he | ⟨c, hc, hcy⟩
  · exact he
  · have hcj : c = j := by
      apply Fin.ext
      have hc1 := c.isLt
      have hj1 := j.isLt
      omega
    subst c
    have hnVH := E.seamPiece_ne_hostPiece h
    rcases hc with hl | hr
    · have hxL := E.toTorus.left_owned j hl
      have hyR : y ∈ E.toTorus.pairing.gluing.right j := by
        rw [hcy, E.toTorus.pairing.gluing.flip_of_mem_left hl]
        exact (E.toTorus.pairing.gluing.attaching j ⟨x, hl⟩).property
      have hyR' := E.toTorus.right_owned j hyR
      cases b
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hyR' hy)).elim
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hxL hx)).elim
    · have hxR := E.toTorus.right_owned j hr
      have hyL : y ∈ E.toTorus.pairing.gluing.left j := by
        rw [hcy, E.toTorus.pairing.gluing.flip_of_mem_right hr]
        exact ((E.toTorus.pairing.gluing.attaching j).symm ⟨x, hr⟩).property
      have hyL' := E.toTorus.left_owned j hyL
      cases b
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hxR hx)).elim
      · exact (hnVH (E.toTorus.eq_of_mem_piece' hyL' hy)).elim

theorem fibrePlugHostSide_disjoint (hn : E.toTorus.pairing.count = 1) :
    Disjoint (E.fibrePlugHostSide h false) (E.fibrePlugHostSide h true) := by
  rw [disjoint_left]
  rintro x ⟨q, hq, rfl⟩ ⟨r, hr, he⟩
  have hp := E.fibrePlug_host_cutMap_injective h hn
    ((E.splitData h).ΘH r).property ((E.splitData h).ΘH q).property he
  have hqr := (E.splitData h).ΘH.injective (Subtype.ext hp)
  rw [hqr] at hr
  change 0 < -1 * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
    (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) at hq
  change 0 < 1 * SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
    (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) at hr
  linarith

end GC.Seifert.ElementaryPresentation
