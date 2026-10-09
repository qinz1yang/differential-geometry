import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianRegion

/-!
# CP1-A3 (G2, stage level): the exterior region retracts onto the deeper exterior region
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1
open GC.LongTime

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

theorem intImg_deepen_CPA3 {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)
    {b : ℝ} (hb : 2 ≤ b) :
    intImg_CPA3 (deepenTruncationOf_CPA2 T hb) = {p | deepHeight_CPA2 T b p < 0} :=
  deep_interior_image_CPA2 T (isClosed_range_cuspMap_CPA2 T) hb

theorem deepSet_subset_domain_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) (i : Fin cores.count) :
    deepSet_CPA2 (E.truncation i) b ⊆ (cores.domain i t : Set (cores.model i).Carrier) :=
  fun p hp => range_inclusion_subset_domain_CPA3 (deepExteriorOf_CPA2 E hb) ht i ⟨⟨p, hp⟩, rfl⟩

theorem start_le_of_deep_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) : E.start ≤ t :=
  (deepExterior_start_CPA2 E (fun i q => isClosed_range_cuspMap_CPA2 (E.truncation i) q) hb).trans ht

theorem hc_of_deep_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) : cores.start ≤ t :=
  E.after_cores.trans (start_le_of_deep_CPA3 E hb ht)

theorem region_deep_subset_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) :
    (deepExteriorOf_CPA2 E hb).region t ⊆ E.region t := by
  intro p hp
  rw [region_eq_CPA3 _ ht] at hp
  rw [region_eq_CPA3 E (start_le_of_deep_CPA3 E hb ht)]
  intro hmem
  obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hmem
  apply hp
  refine mem_iUnion.mpr ⟨i, y, ?_, rfl⟩
  change y ∈ intImg_CPA3 (deepenTruncationOf_CPA2 (E.truncation i) hb)
  rw [intImg_deepen_CPA3]
  exact interior_image_subset_neg_CPA3 (E.truncation i) (by linarith) hy

section Retr

/-- The retraction of the stage carrier: on the `i`-th model patch it is the model retraction
`rho_CPA3`, elsewhere the identity. -/
def retr_CPA3 (E : PersistentCuspExterior cores) (b : ℝ) (t : ℝ) (hc : cores.start ≤ t)
    (p : (postStage F.observation t).Carrier) : (postStage F.observation t).Carrier :=
  open Classical in
  if h : ∃ (i : Fin cores.count) (x : (cores.model i).Carrier),
      x ∈ (cores.domain i t : Set (cores.model i).Carrier) ∧ cores.map i t hc x = p then
    cores.map h.choose t hc (rho_CPA3 (E.truncation h.choose) b h.choose_spec.choose)
  else p

theorem retr_apply_CPA3 (E : PersistentCuspExterior cores) (b : ℝ) {t : ℝ}
    (hc : cores.start ≤ t) (i : Fin cores.count) {x : (cores.model i).Carrier}
    (hx : x ∈ (cores.domain i t : Set (cores.model i).Carrier)) :
    retr_CPA3 E b t hc (cores.map i t hc x) =
      cores.map i t hc (rho_CPA3 (E.truncation i) b x) := by
  classical
  have h : ∃ (i' : Fin cores.count) (x' : (cores.model i').Carrier),
      x' ∈ (cores.domain i' t : Set (cores.model i').Carrier) ∧
        cores.map i' t hc x' = cores.map i t hc x := ⟨i, x, hx, rfl⟩
  rw [retr_CPA3, dif_pos h]
  have key : ∀ (j : Fin cores.count) (y : (cores.model j).Carrier),
      y ∈ (cores.domain j t : Set (cores.model j).Carrier) →
      cores.map j t hc y = cores.map i t hc x →
      cores.map j t hc (rho_CPA3 (E.truncation j) b y) =
        cores.map i t hc (rho_CPA3 (E.truncation i) b x) := by
    intro j y hy hyx
    by_cases hji : j = i
    · subst hji
      have hinj := (cores.embedding j t hc).isEmbedding.injective
      have := @hinj ⟨y, hy⟩ ⟨x, hx⟩ hyx
      have h2 : y = x := congrArg Subtype.val this
      rw [h2]
    · exfalso
      exact Set.disjoint_left.mp (cores.disjoint t hc hji) ⟨y, hy, hyx⟩ ⟨x, hx, rfl⟩
  exact key _ _ h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2

theorem retr_apply_out_CPA3 (E : PersistentCuspExterior cores) (b : ℝ) {t : ℝ}
    (hc : cores.start ≤ t) {p : (postStage F.observation t).Carrier}
    (hout : ∀ (i : Fin cores.count) (x : (cores.model i).Carrier),
      x ∈ (cores.domain i t : Set (cores.model i).Carrier) → cores.map i t hc x ≠ p) :
    retr_CPA3 E b t hc p = p := by
  classical
  rw [retr_CPA3, dif_neg]
  rintro ⟨i, x, hx, hxp⟩
  exact hout i x hx hxp

theorem rho_mem_domain_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) (i : Fin cores.count)
    {x : (cores.model i).Carrier} (hx : x ∈ (cores.domain i t : Set (cores.model i).Carrier))
    (hxe : x ∈ extSet_CPA3 (E.truncation i)) :
    rho_CPA3 (E.truncation i) b x ∈ (cores.domain i t : Set (cores.model i).Carrier) := by
  obtain ⟨q, c, rfl⟩ := mem_iUnion.mp hxe
  rcases rho_eq_or_mem_deepSet_CPA3 (E.truncation i) hb q c with h | h
  · rw [h]; exact hx
  · exact deepSet_subset_domain_CPA3 E hb ht i h

/-- The set of stage points moved by the retraction lies in this compact set. -/
def collarSet_CPA3 (E : PersistentCuspExterior cores) (b : ℝ) (t : ℝ) (hc : cores.start ≤ t) :
    Set (postStage F.observation t).Carrier :=
  ⋃ i, cores.map i t hc '' (⋃ q, cuspCollar_CPA2 (E.truncation i) q b)

theorem collar_subset_domain_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) (i : Fin cores.count) :
    (⋃ q, cuspCollar_CPA2 (E.truncation i) q b) ⊆ (cores.domain i t : Set (cores.model i).Carrier) := by
  intro p hp
  apply deepSet_subset_domain_CPA3 E hb ht i
  rw [show deepSet_CPA2 (E.truncation i) b = _ from deepSet_eq_CPA2 (E.truncation i) (by linarith)]
  exact Or.inr hp

theorem isCompact_collarSet_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) :
    IsCompact (collarSet_CPA3 E b t (hc_of_deep_CPA3 E hb ht)) := by
  refine isCompact_iUnion fun i => ?_
  refine IsCompact.image_of_continuousOn ?_
    ((continuousOn_map_CPA3 i t (hc_of_deep_CPA3 E hb ht)).mono (collar_subset_domain_CPA3 E hb ht i))
  exact isCompact_iUnion fun q => isCompact_cuspCollar_CPA2 (E.truncation i) q (by linarith)

theorem rho_of_not_mem_ext_CPA3 {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)
    (b : ℝ) {x : H.Carrier} (hx : x ∉ extSet_CPA3 T) : rho_CPA3 T b x = x := by
  classical
  rw [rho_CPA3, dif_neg]
  rintro ⟨q, c, h⟩
  exact hx (mem_iUnion.mpr ⟨q, c, h⟩)

theorem retr_ne_mem_collarSet_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) {p : (postStage F.observation t).Carrier}
    (hne : retr_CPA3 E b t (hc_of_deep_CPA3 E hb ht) p ≠ p) :
    p ∈ collarSet_CPA3 E b t (hc_of_deep_CPA3 E hb ht) := by
  classical
  by_contra hp
  by_cases hout : ∀ (i : Fin cores.count) (x : (cores.model i).Carrier),
      x ∈ (cores.domain i t : Set (cores.model i).Carrier) →
        cores.map i t (hc_of_deep_CPA3 E hb ht) x ≠ p
  · exact hne (retr_apply_out_CPA3 E b _ hout)
  · push Not at hout
    obtain ⟨i, x, hx, rfl⟩ := hout
    rw [retr_apply_CPA3 E b _ i hx] at hne
    have hρ : rho_CPA3 (E.truncation i) b x ≠ x := fun h => hne (by rw [h])
    by_cases hxe : x ∈ extSet_CPA3 (E.truncation i)
    · obtain ⟨q, c, rfl⟩ := mem_iUnion.mp hxe
      have hc := exists_collar_of_rho_ne_CPA3 (E.truncation i) q c hρ
      exact hp (mem_iUnion.mpr ⟨i, _, mem_iUnion.mpr ⟨q, c, ⟨trivial, hc.le⟩, rfl⟩, rfl⟩)
    · exact hρ (rho_of_not_mem_ext_CPA3 _ b hxe)

theorem region_inter_image_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) (i : Fin cores.count) :
    E.region t ∩ cores.map i t (hc_of_deep_CPA3 E hb ht) '' (cores.domain i t : Set (cores.model i).Carrier) =
      (fun y : ↥(cores.domain i t) => cores.map i t (hc_of_deep_CPA3 E hb ht) y.1) ''
        {y | y.1 ∈ extSet_CPA3 (E.truncation i)} := by
  have hEt := start_le_of_deep_CPA3 E hb ht
  ext p
  constructor
  · rintro ⟨hp, y, hy, rfl⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have := (mem_region_image_iff_CPA3 E hEt i hy).mp hp
    exact (not_mem_interior_image_iff_CPA3 (E.truncation i) y).mp this
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.1, y.2, rfl⟩
    exact (mem_region_image_iff_CPA3 E hEt i y.2).mpr
      ((not_mem_interior_image_iff_CPA3 (E.truncation i) y.1).mpr hy)

theorem continuousOn_retr_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) :
    ContinuousOn (retr_CPA3 E b t (hc_of_deep_CPA3 E hb ht)) (E.region t) := by
  have hc := hc_of_deep_CPA3 E hb ht
  intro p hp
  by_cases hpK : p ∈ collarSet_CPA3 E b t hc
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hpK
    obtain ⟨x, hxcol, rfl⟩ := hi
    have hxD := collar_subset_domain_CPA3 E hb ht i hxcol
    have hMopen := isOpen_image_domain_CPA3 (cores := cores) i t hc
    have hmem : cores.map i t hc x ∈ cores.map i t hc '' (cores.domain i t : Set _) :=
      ⟨x, hxD, rfl⟩
    rw [← continuousWithinAt_inter (hMopen.mem_nhds hmem), region_inter_image_CPA3 E hb ht i]
    have hind : _root_.Topology.IsInducing
        (fun y : ↥(cores.domain i t) => cores.map i t hc y.1) :=
      (isOpenEmbedding_map_CPA3 (cores := cores) i t hc).isEmbedding.isInducing
    have hco : ContinuousOn (retr_CPA3 E b t hc)
        ((fun y : ↥(cores.domain i t) => cores.map i t hc y.1) ''
          {y | y.1 ∈ extSet_CPA3 (E.truncation i)}) := by
      rw [hind.continuousOn_image_iff]
      have hfun : (retr_CPA3 E b t hc ∘ fun y : ↥(cores.domain i t) => cores.map i t hc y.1) =
          fun y : ↥(cores.domain i t) =>
            cores.map i t hc (rho_CPA3 (E.truncation i) b y.1) :=
        funext fun y => retr_apply_CPA3 E b hc i y.2
      rw [hfun]
      refine (continuousOn_map_CPA3 (cores := cores) i t hc).comp
        ((continuousOn_rho_ext_CPA3 (E.truncation i) b).comp continuous_subtype_val.continuousOn
          (fun y hy => hy)) ?_
      intro y hy
      exact rho_mem_domain_CPA3 E hb ht i y.2 hy
    have hxe : x ∈ extSet_CPA3 (E.truncation i) := by
      have := (mem_region_image_iff_CPA3 E (start_le_of_deep_CPA3 E hb ht) i hxD).mp hp
      exact (not_mem_interior_image_iff_CPA3 (E.truncation i) x).mp this
    exact hco _ ⟨⟨x, hxD⟩, hxe, rfl⟩
  · have hopen : IsOpen (collarSet_CPA3 E b t hc)ᶜ :=
      (isCompact_collarSet_CPA3 E hb ht).isClosed.isOpen_compl
    have hev : retr_CPA3 E b t hc =ᶠ[𝓝 p] id := by
      filter_upwards [hopen.mem_nhds hpK] with y hy
      by_contra hne
      exact hy (retr_ne_mem_collarSet_CPA3 E hb ht hne)
    have hpp : retr_CPA3 E b t hc p = p := by
      by_contra hne
      exact hpK (retr_ne_mem_collarSet_CPA3 E hb ht hne)
    exact (continuousWithinAt_id (s := E.region t) (x := p)).congr_of_eventuallyEq
      (hev.filter_mono nhdsWithin_le_nhds) hpp

theorem not_mem_intImg_deep_iff_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b)
    (i : Fin cores.count) (x : (cores.model i).Carrier) :
    x ∉ intImg_CPA3 ((deepExteriorOf_CPA2 E hb).truncation i) ↔
      0 ≤ deepHeight_CPA2 (E.truncation i) b x := by
  change x ∉ intImg_CPA3 (deepenTruncationOf_CPA2 (E.truncation i) hb) ↔ _
  rw [intImg_deepen_CPA3]
  simp

theorem retr_mem_region_deep_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) {p : (postStage F.observation t).Carrier}
    (hp : p ∈ E.region t) :
    retr_CPA3 E b t (hc_of_deep_CPA3 E hb ht) p ∈ (deepExteriorOf_CPA2 E hb).region t := by
  classical
  have hc := hc_of_deep_CPA3 E hb ht
  by_cases hout : ∀ (i : Fin cores.count) (x : (cores.model i).Carrier),
      x ∈ (cores.domain i t : Set (cores.model i).Carrier) → cores.map i t hc x ≠ p
  · rw [retr_apply_out_CPA3 E b hc hout, region_eq_CPA3 _ ht]
    intro hmem
    obtain ⟨i, y, hy, hyp⟩ := mem_iUnion.mp hmem
    exact hout i y (intImg_subset_domain_CPA3 _ ht i hy) hyp
  · push Not at hout
    obtain ⟨i, x, hx, rfl⟩ := hout
    rw [retr_apply_CPA3 E b hc i hx]
    have hxe : x ∈ extSet_CPA3 (E.truncation i) := by
      have := (mem_region_image_iff_CPA3 E (start_le_of_deep_CPA3 E hb ht) i hx).mp hp
      exact (not_mem_interior_image_iff_CPA3 (E.truncation i) x).mp this
    have hρD := rho_mem_domain_CPA3 E hb ht i hx hxe
    refine (mem_region_image_iff_CPA3 (deepExteriorOf_CPA2 E hb) ht i hρD).mpr ?_
    rw [not_mem_intImg_deep_iff_CPA3]
    obtain ⟨q, c, rfl⟩ := mem_iUnion.mp hxe
    exact deepHeight_rho_nonneg_CPA3 (E.truncation i) hb q c

theorem retr_eq_of_mem_region_deep_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b)
    {t : ℝ} (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) {p : (postStage F.observation t).Carrier}
    (hp : p ∈ (deepExteriorOf_CPA2 E hb).region t) :
    retr_CPA3 E b t (hc_of_deep_CPA3 E hb ht) p = p := by
  classical
  have hc := hc_of_deep_CPA3 E hb ht
  by_cases hout : ∀ (i : Fin cores.count) (x : (cores.model i).Carrier),
      x ∈ (cores.domain i t : Set (cores.model i).Carrier) → cores.map i t hc x ≠ p
  · exact retr_apply_out_CPA3 E b hc hout
  · push Not at hout
    obtain ⟨i, x, hx, rfl⟩ := hout
    rw [retr_apply_CPA3 E b hc i hx]
    have hxE : x ∈ extSet_CPA3 (E.truncation i) := by
      have := (mem_region_image_iff_CPA3 E (start_le_of_deep_CPA3 E hb ht) i hx).mp
        (region_deep_subset_CPA3 E hb ht hp)
      exact (not_mem_interior_image_iff_CPA3 (E.truncation i) x).mp this
    have h0 := (not_mem_intImg_deep_iff_CPA3 E hb i x).mp
      ((mem_region_image_iff_CPA3 (deepExteriorOf_CPA2 E hb) ht i hx).mp hp)
    obtain ⟨q, c, rfl⟩ := mem_iUnion.mp hxE
    rw [rho_eq_self_of_deepHeight_nonneg_CPA3 (E.truncation i) hb q c h0]

/-- **The retraction of the exterior region onto the deeper exterior region.** -/
def retrMap_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) :
    C(↥(E.region t), ↥((deepExteriorOf_CPA2 E hb).region t)) :=
  ⟨fun p => ⟨retr_CPA3 E b t (hc_of_deep_CPA3 E hb ht) p.1, retr_mem_region_deep_CPA3 E hb ht p.2⟩,
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_retr_CPA3 E hb ht)).subtype_mk _⟩

/-- The inclusion of the deeper exterior region into the exterior region. -/
def inclMap_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) :
    C(↥((deepExteriorOf_CPA2 E hb).region t), ↥(E.region t)) :=
  ⟨fun p => ⟨p.1, region_deep_subset_CPA3 E hb ht p.2⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem retrMap_comp_inclMap_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) :
    (retrMap_CPA3 E hb ht).comp (inclMap_CPA3 E hb ht) = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun p => Subtype.ext ?_
  exact retr_eq_of_mem_region_deep_CPA3 E hb ht p.2

end Retr

end GC.LongTime.CuspP1
