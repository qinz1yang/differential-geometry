import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Cylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.QuotientInclusion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionClosure
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionQuotient
import DifferentialGeometry.Topology.Compactness.ProductChartThickening
import Mathlib.Topology.OpenPartialHomeomorph.Composition

noncomputable section

open Set

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere)
open HorosphereProjection (quotientBusemann quotientHorosphereHomeomorph)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer hn Γ (Set.singleton ξ.val)
local notation "QP" => @MulAction.orbitRel.Quotient P (HUpper n) _ (EquivariantMap.subAction hn P)
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)
local notation "πP" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))
local notation "πΓ" => Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "C" => (πP '' horosphere ξ.val (D.level ξ))
local notation "hhor" => CuspCrossSections.horospherical_endStabilizer hn Γ hΓ (D.region_nonempty ξ)
local notation "B" => quotientBusemann hn P ξ.val hhor
local notation "F" => EquivariantMap.quotientInclusion («P» := P) (Γ := Γ) hn inf_le_left
local notation "V" => (πP '' interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val)))

def horosphereHeightHomeomorph : QP ≃ₜ C × ℝ := by
  let e := quotientHorosphereHomeomorph hn P ξ.val hhor (D.level ξ)
  refine
    { toFun := fun q => ((e q).1, B q)
      invFun := fun z => e.symm (z.1, D.level ξ - z.2)
      left_inv := fun q => e.symm_apply_apply q
      right_inv := ?_
      continuous_toFun := e.continuous.fst.prodMk (HorosphereProjection.continuous_quotientBusemann hn P ξ.val hhor)
      continuous_invFun := e.symm.continuous.comp
        (continuous_fst.prodMk (continuous_const.sub continuous_snd)) }
  intro z
  apply Prod.ext
  · change (e (e.symm (z.1, D.level ξ - z.2))).1 = z.1
    have he := congrArg Prod.fst (e.apply_symm_apply (z.1, D.level ξ - z.2))
    exact he
  · have he := congrArg Prod.snd (e.apply_symm_apply (z.1, D.level ξ - z.2))
    change D.level ξ - B (e.symm (z.1, D.level ξ - z.2)) = D.level ξ - z.2 at he
    change B (e.symm (z.1, D.level ξ - z.2)) = z.2
    linarith

local notation "E" => D.horosphereHeightHomeomorph hΓ ξ

@[simp] theorem horosphereHeightHomeomorph_snd (q : QP) : (E q).2 = B q := rfl

@[simp] theorem horosphereHeightHomeomorph_symm (z : C × ℝ) :
    (E).symm z = (quotientHorosphereHomeomorph hn P ξ.val hhor (D.level ξ)).symm
      (z.1, D.level ξ - z.2) := rfl

@[simp] theorem horosphereHeightHomeomorph_apply_mk (p : HUpper n) :
    E (πP p) =
      (⟨πP (HorosphereProjection.retract ξ.val (D.level ξ) p),
        ⟨HorosphereProjection.retract ξ.val (D.level ξ) p,
          HorosphereProjection.retract_mem_horosphere ξ.val (D.level ξ) p, rfl⟩⟩,
        busemann ξ.val p) := rfl

private theorem isOpenMap_quotientInclusion : IsOpenMap F := by
  let := EquivariantMap.subAction hn Γ
  let := EquivariantMap.subAction hn P
  let : ContinuousConstSMul Γ (HUpper n) :=
    ⟨fun γ => (Isometry.of_dist_eq (HyperbolicAction.po_dist_smul hn (γ : PO n 1))).continuous⟩
  exact IsOpenMap.of_comp (continuous_quotient_mk' : Continuous (πP : HUpper n → QP))
    Quotient.mk_surjective (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := HUpper n)).isOpenMap

private theorem isOpen_thinRegion_image : IsOpen V := by
  let := EquivariantMap.subAction hn P
  let : ContinuousConstSMul P (HUpper n) :=
    ⟨fun γ => (Isometry.of_dist_eq (HyperbolicAction.po_dist_smul hn (γ : PO n 1))).continuous⟩
  exact (MulAction.isOpenQuotientMap_quotientMk (Γ := P) (T := HUpper n)).isOpenMap _ isOpen_interior

include hΓ in
private theorem quotientInclusion_injOn_thinRegion : InjOn F V := by
  intro q hq q' hq' he
  have h := (OrbifoldThinRegions.isOpenEmbedding_thinRegionQuotientInclusion
    hn Γ r (Set.singleton ξ.val) hΓ).injective
    (a₁ := ⟨q, hq⟩) (a₂ := ⟨q', hq'⟩) he
  exact congrArg Subtype.val h

def horosphereGraphChart : OpenPartialHomeomorph (C × ℝ) QΓ := by
  let e := E
  let f : C × ℝ → QΓ := F ∘ e.symm
  let S : Set (C × ℝ) := e.symm ⁻¹' V
  have hS : IsOpen S := (isOpen_thinRegion_image D ξ).preimage e.symm.continuous
  have hinj : InjOn f S := by
    intro p hp q hq he
    exact e.symm.injective (quotientInclusion_injOn_thinRegion D hΓ ξ hp hq he)
  let : Nonempty (C × ℝ) := ⟨e (πP (HyperbolicFaithful.basepointH : HUpper n))⟩
  exact OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv f S)
    ((F).continuous.comp e.symm.continuous).continuousOn
    ((isOpenMap_quotientInclusion D ξ).comp e.symm.isOpenMap) hS

@[simp] theorem horosphereGraphChart_apply (z : C × ℝ) :
    D.horosphereGraphChart hΓ ξ z = F ((E).symm z) := rfl

theorem horosphereGraphChart_apply_mk (p : HUpper n)
    (hp : p ∈ horosphere ξ.val (D.level ξ)) (b : ℝ) :
    D.horosphereGraphChart hΓ ξ (⟨πP p, ⟨p, hp, rfl⟩⟩, b) =
      πΓ (AsymptoticRays.rayTo p ξ.val (D.level ξ - b)) := rfl

@[simp] theorem horosphereGraphChart_source :
    (D.horosphereGraphChart hΓ ξ).source = (E).symm ⁻¹' V := rfl

@[simp] theorem horosphereGraphChart_target :
    (D.horosphereGraphChart hΓ ξ).target =
      πΓ '' interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val)) := by
  change (F ∘ (E).symm) '' ((E).symm ⁻¹' V) = _
  rw [image_comp, (E).symm.surjective.image_preimage]
  exact EquivariantMap.quotientInclusion_image hn inf_le_left _

def openGraphRegion (f : C → ℝ) : Set QΓ :=
  F '' {q : QP | (E q).2 < f (E q).1}

def closedGraphRegion (f : C → ℝ) : Set QΓ :=
  F '' {q : QP | (E q).2 ≤ f (E q).1}

theorem openGraphRegion_eq_image (f : C → ℝ) :
    D.openGraphRegion hΓ ξ f =
      πΓ '' {p : HUpper n | busemann ξ.val p < f (E (πP p)).1} := by
  have he : {q : QP | (E q).2 < f (E q).1} =
      πP '' {p : HUpper n | busemann ξ.val p < f (E (πP p)).1} := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
      exact ⟨p, hq, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  change F '' _ = _
  rw [he]
  exact EquivariantMap.quotientInclusion_image hn inf_le_left _

theorem closedGraphRegion_eq_image (f : C → ℝ) :
    D.closedGraphRegion hΓ ξ f =
      πΓ '' {p : HUpper n | busemann ξ.val p ≤ f (E (πP p)).1} := by
  have he : {q : QP | (E q).2 ≤ f (E q).1} =
      πP '' {p : HUpper n | busemann ξ.val p ≤ f (E (πP p)).1} := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
      exact ⟨p, hq, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  change F '' _ = _
  rw [he]
  exact EquivariantMap.quotientInclusion_image hn inf_le_left _

theorem isOpen_openGraphRegion (f : C → ℝ) (hf : Continuous f) :
    IsOpen (D.openGraphRegion hΓ ξ f) :=
  isOpenMap_quotientInclusion D ξ _ (isOpen_lt (E).continuous.snd (hf.comp (E).continuous.fst))

private def graphHeightHomeomorph (f : C → ℝ) (hf : Continuous f) : QP ≃ₜ C × ℝ :=
  (E).trans
    { toFun := fun z => (z.1, z.2 - f z.1)
      invFun := fun z => (z.1, z.2 + f z.1)
      left_inv := by intro z; exact Prod.ext rfl (sub_add_cancel _ _)
      right_inv := by intro z; exact Prod.ext rfl (add_sub_cancel_right _ _)
      continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst))
      continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst)) }

private theorem closure_graph_strict_sublevel (f : C → ℝ) (hf : Continuous f) :
    closure {q : QP | (E q).2 < f (E q).1} = {q : QP | (E q).2 ≤ f (E q).1} := by
  let e := graphHeightHomeomorph D hΓ ξ f hf
  have ho : IsOpenMap (fun q : QP => (e q).2) := isOpenMap_snd.comp e.isOpenMap
  have hc : Continuous (fun q : QP => (e q).2) := e.continuous.snd
  have he := ho.preimage_closure_eq_closure_preimage hc (Iio (0 : ℝ))
  rw [closure_Iio] at he
  have hs : (fun q : QP => (e q).2) ⁻¹' Iio (0 : ℝ) =
      {q : QP | (E q).2 < f (E q).1} := by
    ext q
    change (E q).2 - f (E q).1 < 0 ↔ (E q).2 < f (E q).1
    exact sub_neg
  have hw : (fun q : QP => (e q).2) ⁻¹' Iic (0 : ℝ) =
      {q : QP | (E q).2 ≤ f (E q).1} := by
    ext q
    change (E q).2 - f (E q).1 ≤ 0 ↔ (E q).2 ≤ f (E q).1
    exact sub_nonpos
  rw [hs, hw] at he
  exact he.symm

private theorem heightHomeomorph_quotientRay (t : ℝ) (q : QP) :
    E (HorosphereProjection.quotientRay hn P ξ.val (fun γ => (hhor γ).1) t q) =
      ((E q).1, (E q).2 - t) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (πP : HUpper n → QP)
        (HorosphereProjection.retract_rayTo ξ.val (D.level ξ) p t)
    · exact HorosphereProjection.busemann_rayTo p ξ.val t

private theorem quotientRay_heightHomeomorph_symm (s : C) (a b : ℝ) :
    HorosphereProjection.quotientRay hn P ξ.val (fun γ => (hhor γ).1)
      (b - a) ((E).symm (s, b)) = (E).symm (s, a) := by
  apply (E).injective
  rw [heightHomeomorph_quotientRay, (E).apply_symm_apply, (E).apply_symm_apply]
  exact Prod.ext rfl (by ring)

include hΓ in
private theorem mem_quotient_interior_thinRegion_iff (p : HUpper n) :
    πP p ∈ V ↔ p ∈ interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val)) := by
  constructor
  · rintro ⟨p', hp', he⟩
    obtain ⟨γ, hγ⟩ := Quotient.exact he.symm
    let δ : Γ := ⟨γ, γ.property.1⟩
    have hi := (OrbifoldThinRegions.precisely_invariant_interior_thinRegion
      hn Γ hΓ r (Set.singleton ξ.val) δ).1 γ.property
    rw [← hi]
    exact ⟨p', hp', hγ⟩
  · exact fun hp => ⟨p, hp, rfl⟩

variable (hr : 0 < r)
  (hgeom : ∀ p : HUpper n,
    BoundaryStabilizer.ElementaryGeometry hn (OrbifoldStrata.closedSmallSubgroup hn Γ r p))

include hr hgeom

private theorem quotientRay_mem_interior_thinRegion (q : QP) (hq : q ∈ V)
    (t : ℝ) (ht : 0 ≤ t) :
    HorosphereProjection.quotientRay hn P ξ.val (fun γ => (hhor γ).1) t q ∈ V := by
  rcases ht.eq_or_lt with he | ht
  · subst t
    have hzero := heightHomeomorph_quotientRay D hΓ ξ 0 q
    simp only [sub_zero, Prod.eta] at hzero
    rw [(E).injective hzero]
    exact hq
  · obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨AsymptoticRays.rayTo p ξ.val t,
      CuspHoroballs.rayTo_mem_interior_thinRegion hn Γ hΓ hr hgeom (interior_subset hp) ht, rfl⟩

theorem graph_sublevel_subset_interior_thinRegion (f : C → ℝ)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V) :
    {q : QP | (E q).2 ≤ f (E q).1} ⊆ V := by
  intro q hq
  have h := quotientRay_mem_interior_thinRegion D hΓ ξ hr hgeom
    ((E).symm ((E q).1, f (E q).1)) (hgraph (E q).1)
    (f (E q).1 - (E q).2) (sub_nonneg.mpr hq)
  rw [quotientRay_heightHomeomorph_symm, (E).symm_apply_apply] at h
  exact h

theorem isClosed_closedGraphRegion (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V) :
    IsClosed (D.closedGraphRegion hΓ ξ f) := by
  let W : Set QP := {q | (E q).2 ≤ f (E q).1}
  let A : Set (HUpper n) := πP ⁻¹' W
  have hW : IsClosed W := isClosed_le (E).continuous.snd (hf.comp (E).continuous.fst)
  have hA : IsClosed A := hW.preimage continuous_quotient_mk'
  have hAsub : A ⊆ OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val) := by
    intro p hp
    exact interior_subset ((mem_quotient_interior_thinRegion_iff D hΓ ξ p).mp
      (D.graph_sublevel_subset_interior_thinRegion hΓ ξ hr hgeom f hgraph hp))
  have hinv (γ : P) (p : HUpper n) (hp : p ∈ A) :
      (HyperbolicAction.poMulAction hn).smul (γ : PO n 1) p ∈ A := by
    change πP ((HyperbolicAction.poMulAction hn).smul (γ : PO n 1) p) ∈ W
    have he : πP ((HyperbolicAction.poMulAction hn).smul (γ : PO n 1) p) = πP p :=
      Quotient.sound ⟨γ, rfl⟩
    rw [he]
    exact hp
  have he : D.closedGraphRegion hΓ ξ f = πΓ '' A := by
    change F '' W = _
    rw [← EquivariantMap.quotientInclusion_image hn (show P ≤ Γ from inf_le_left) A]
    rw [show πP '' A = W from Quotient.mk_surjective.image_preimage W]
  rw [he]
  exact OrbifoldThinRegions.isClosed_quotient_of_subset_thinRegion hn Γ hΓ hA hAsub hinv

theorem closure_openGraphRegion (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V) :
    closure (D.openGraphRegion hΓ ξ f) = D.closedGraphRegion hΓ ξ f := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact image_mono (fun q h => (show (E q).2 < f (E q).1 from h).le)
    · exact D.isClosed_closedGraphRegion hΓ ξ hr hgeom f hf hgraph
  · have h := image_closure_subset_closure_image (F).continuous
      (s := {q : QP | (E q).2 < f (E q).1})
    rwa [closure_graph_strict_sublevel D hΓ ξ f hf] at h

theorem mem_openGraphRegion_iff (f : C → ℝ)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V)
    (z : C × ℝ) (hz : z ∈ (D.horosphereGraphChart hΓ ξ).source) :
    D.horosphereGraphChart hΓ ξ z ∈ D.openGraphRegion hΓ ξ f ↔ z.2 < f z.1 := by
  constructor
  · rintro ⟨q, hq, he⟩
    have hqV := D.graph_sublevel_subset_interior_thinRegion hΓ ξ hr hgeom f hgraph (show (E q).2 ≤ f (E q).1 from hq.le)
    have hqq : q = (E).symm z := quotientInclusion_injOn_thinRegion D hΓ ξ hqV hz he
    change (E q).2 < f (E q).1 at hq
    rw [hqq, (E).apply_symm_apply] at hq
    exact hq
  · intro hz'
    refine ⟨(E).symm z, ?_, rfl⟩
    change (E ((E).symm z)).2 < f (E ((E).symm z)).1
    simpa only [(E).apply_symm_apply] using hz'

theorem frontier_openGraphRegion (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V) :
    frontier (D.openGraphRegion hΓ ξ f) =
      range (fun s : C => D.horosphereGraphChart hΓ ξ (s, f s)) := by
  rw [frontier, D.closure_openGraphRegion hΓ ξ hr hgeom f hf hgraph,
    (D.isOpen_openGraphRegion hΓ ξ f hf).interior_eq]
  ext y
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hn⟩
    have he : (E q).2 = f (E q).1 := by
      by_contra hne
      exact hn ⟨q, lt_of_le_of_ne hq hne, rfl⟩
    refine ⟨(E q).1, ?_⟩
    change F ((E).symm ((E q).1, f (E q).1)) = F q
    rw [← he, (E).symm_apply_apply]
  · rintro ⟨s, rfl⟩
    refine ⟨⟨(E).symm (s, f s), ?_, rfl⟩, ?_⟩
    · change (E ((E).symm (s, f s))).2 ≤ f (E ((E).symm (s, f s))).1
      simpa only [(E).apply_symm_apply] using (le_refl (f s))
    · rw [D.mem_openGraphRegion_iff hΓ ξ hr hgeom f hgraph (s, f s) (hgraph s)]
      exact lt_irrefl _

omit hr hgeom in
theorem exists_graph_band_subset_horosphereGraphChart [CompactSpace C]
    (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V) :
    ∃ a : ℝ, 0 < a ∧ ∀ z : C × ℝ, |z.2 - f z.1| < a →
      z ∈ (D.horosphereGraphChart hΓ ξ).source := by
  let H : C × ℝ ≃ₜ C × ℝ :=
    { toFun := fun z => (z.1, f z.1 + z.2)
      invFun := fun z => (z.1, z.2 - f z.1)
      left_inv := by intro z; exact Prod.ext rfl (add_sub_cancel_left _ _)
      right_inv := by intro z; exact Prod.ext rfl (add_sub_cancel _ _)
      continuous_toFun := continuous_fst.prodMk ((hf.comp continuous_fst).add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst)) }
  let T := H.transOpenPartialHomeomorph (D.horosphereGraphChart hΓ ξ)
  have hzero : (univ : Set C) ×ˢ Icc (0 : ℝ) 0 ⊆ T.source := by
    rintro ⟨s, t⟩ ⟨_, ht⟩
    have he : t = 0 := le_antisymm ht.2 ht.1
    subst t
    change (s, f s + 0) ∈ (D.horosphereGraphChart hΓ ξ).source
    rw [add_zero]
    exact hgraph s
  obtain ⟨a, b, ha, hb, hsource, _⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band T
      (le_refl (0 : ℝ)) hzero isOpen_univ (subset_univ _)
  refine ⟨min (-a) b, lt_min (neg_pos.mpr ha) hb, ?_⟩
  intro z hz
  have habs := abs_lt.mp hz
  have ht : (z.1, z.2 - f z.1) ∈ T.source :=
    hsource ⟨mem_univ _, by
      have h := min_le_left (-a) b
      linarith [habs.1], habs.2.trans_le (min_le_right _ _)⟩
  change (z.1, f z.1 + (z.2 - f z.1)) ∈ (D.horosphereGraphChart hΓ ξ).source at ht
  simpa only [add_sub_cancel] using ht

theorem frontier_image_openGraphRegion
    {Y : Type*} [TopologicalSpace Y] (e : QΓ ≃ₜ Y)
    (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V) :
    frontier (e '' D.openGraphRegion hΓ ξ f) =
      range (fun s : C => e (D.horosphereGraphChart hΓ ξ (s, f s))) := by
  rw [← e.image_frontier, D.frontier_openGraphRegion hΓ ξ hr hgeom f hf hgraph]
  exact (range_comp e (fun s : C => D.horosphereGraphChart hΓ ξ (s, f s))).symm

theorem mem_image_openGraphRegion_iff
    {Y : Type*} [TopologicalSpace Y] (e : QΓ ≃ₜ Y)
    (f : C → ℝ) (hgraph : ∀ s : C, (E).symm (s, f s) ∈ V)
    (z : C × ℝ) (hz : z ∈ (D.horosphereGraphChart hΓ ξ).source) :
    e (D.horosphereGraphChart hΓ ξ z) ∈ e '' D.openGraphRegion hΓ ξ f ↔ z.2 < f z.1 := by
  rw [e.injective.mem_set_image]
  exact D.mem_openGraphRegion_iff hΓ ξ hr hgeom f hgraph z hz

theorem horosphereGraphChart_frontier_of_projection
    {Y : Type*} [TopologicalSpace Y] (e : QΓ ≃ₜ Y) (pH : HUpper n → Y)
    (hrep : ∀ p : HUpper n, e (πΓ p) = pH p) :
    let A := (D.horosphereGraphChart hΓ ξ).transHomeomorph e
    A.source = (E).symm ⁻¹' V ∧
    A.target = pH '' interior (OrbifoldThinRegions.thinRegion hn Γ r (Set.singleton ξ.val)) ∧
    (∀ (p : HUpper n) (hp : p ∈ horosphere ξ.val (D.level ξ)) (b : ℝ),
      A (⟨πP p, ⟨p, hp, rfl⟩⟩, b) = pH (AsymptoticRays.rayTo p ξ.val (D.level ξ - b))) ∧
    ∀ (f : C → ℝ), Continuous f → (∀ s : C, (E).symm (s, f s) ∈ V) →
      let U := pH '' {p : HUpper n | busemann ξ.val p < f (E (πP p)).1}
      let K := pH '' {p : HUpper n | busemann ξ.val p ≤ f (E (πP p)).1}
      IsOpen U ∧ IsClosed K ∧ closure U = K ∧
      frontier U = range (fun s : C => A (s, f s)) ∧
      (∀ z : C × ℝ, z ∈ A.source → (A z ∈ U ↔ z.2 < f z.1)) ∧
      (∀ [CompactSpace C], ∃ a : ℝ, 0 < a ∧ ∀ z : C × ℝ,
        |z.2 - f z.1| < a → z ∈ A.source) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change e.symm ⁻¹' (D.horosphereGraphChart hΓ ξ).target = _
    rw [D.horosphereGraphChart_target hΓ ξ, ← e.image_eq_preimage_symm, image_image]
    apply image_congr
    intro p hp
    exact hrep p
  · intro p hp b
    change e (D.horosphereGraphChart hΓ ξ (⟨πP p, ⟨p, hp, rfl⟩⟩, b)) = _
    rw [D.horosphereGraphChart_apply_mk hΓ ξ p hp b]
    exact hrep _
  · intro f hf hgraph
    have ho : e '' D.openGraphRegion hΓ ξ f =
        pH '' {p : HUpper n | busemann ξ.val p < f (E (πP p)).1} := by
      rw [D.openGraphRegion_eq_image hΓ ξ f, image_image]
      apply image_congr
      intro p hp
      exact hrep p
    have hc : e '' D.closedGraphRegion hΓ ξ f =
        pH '' {p : HUpper n | busemann ξ.val p ≤ f (E (πP p)).1} := by
      rw [D.closedGraphRegion_eq_image hΓ ξ f, image_image]
      apply image_congr
      intro p hp
      exact hrep p
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← ho]
      exact e.isOpenMap _ (D.isOpen_openGraphRegion hΓ ξ f hf)
    · rw [← hc]
      exact e.isClosedMap _ (D.isClosed_closedGraphRegion hΓ ξ hr hgeom f hf hgraph)
    · rw [← ho, ← hc, ← e.image_closure, D.closure_openGraphRegion hΓ ξ hr hgeom f hf hgraph]
    · rw [← ho]
      exact D.frontier_image_openGraphRegion hΓ ξ hr hgeom e f hf hgraph
    · intro z hz
      rw [← ho]
      exact D.mem_image_openGraphRegion_iff hΓ ξ hr hgeom e f hgraph z hz
    · intro hcompact
      exact D.exists_graph_band_subset_horosphereGraphChart hΓ ξ f hf hgraph

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
