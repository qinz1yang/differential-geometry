import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertRestrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCircle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecPortsApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSphereFaces

/-!
# FC42 sphere recursion, packet S4 (group G2): a circle region restricted to one component

Lane ASM-SPH2 (review 40 §2.5: "circle fibres are connected, so the component label is constant on
fibres, and the local product charts give the clopen restriction of the base").

* `CircleRegion.surjective_proj`: every base point has a fibre (the trivialization).
* `CircleRegion.restrictClopen O hO`: the restriction to a CLOPEN set `O` of the base; the corner
  charts are those centred in `O` (`CornerIn`, renumbered by `cornerInEquiv`); every corner chart
  target is either inside `O` or disjoint from it (`rimBox 2` is connected). Base, domain,
  projection and trivializations are those of `restrictBase` (`restrictDomain`, `restrictProj`,
  `restrictTrivialization`), defining functions and rounding are restricted.
* `CircleRegion.compBase R DQ i`: the base part of the component `i` (clopen; a fibre lies in the
  component iff its base point does, `mem_compBase_iff`).
* `CircleRegion.toComponent R DQ i`: the circle region of the component carrier
  `componentCarrier Q DQ i` (the clopen restriction, with the domain moved into the component by
  `compDomainDiffeo`); its cornered region, rounded region and fibres are the preimages of those of
  `R` (`val_image_proj_preimage_toComponent`, `region_toComponent`, `rounded_toComponent`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

theorem isPreconnected_rimBox (r : ℝ) : IsPreconnected (rimBox r) := by
  have h : rimBox r = Ioo (-r) r ×ˢ Ioo (-r) r := by
    ext v
    simp only [rimBox, mem_ofPred_eq, mem_prod, mem_Ioo, abs_lt]
  rw [h]
  exact isPreconnected_Ioo.prod isPreconnected_Ioo

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- Every base point has a nonempty fibre. -/
theorem surjective_proj : Surjective R.proj := by
  intro b
  let x := (R.trivialization b).symm (⟨b, R.mem_neighborhood b⟩, 1)
  refine ⟨x.val, ?_⟩
  have h := R.projection_trivialization b x
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

theorem isPreconnected_cornerChart_target (k : Fin R.cornerCount) :
    IsPreconnected (R.cornerChart k).target := by
  rw [← (R.cornerChart k).toPartialEquiv.image_source_eq_target]
  rw [R.cornerChart_source]
  exact (isPreconnected_rimBox 2).image _
    ((R.cornerChart k).contMDiffOn.continuousOn.mono (R.cornerChart_source k).ge)

theorem cornerChart_center_mem_target (k : Fin R.cornerCount) :
    R.cornerChart k (0, 0) ∈ (R.cornerChart k).target :=
  (R.cornerChart k).map_source (by rw [R.cornerChart_source]; simp [rimBox])

theorem cornerChart_mem_target (k : Fin R.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    R.cornerChart k v ∈ (R.cornerChart k).target :=
  (R.cornerChart k).map_source (by rw [R.cornerChart_source]; exact hv)

/-! ## Restriction to a clopen set of the base -/

section Clopen

variable (O : TopologicalSpace.Opens R.Base)

/-- The corners centred in `O`. -/
abbrev CornerIn : Type :=
  {k : Fin R.cornerCount // R.cornerChart k (0, 0) ∈ O}

/-- The corners centred in `O` form a finite type. -/
instance cornerInFintype_ASMSPH2 : Fintype (R.CornerIn O) :=
  Fintype.ofFinite _

/-- The numbering of the corners centred in `O`. -/
def cornerInEquiv : Fin (Fintype.card (R.CornerIn O)) ≃ R.CornerIn O :=
  (Fintype.equivFin _).symm

variable {O} (hO : IsClosed (O : Set R.Base))

include hO in
/-- A corner chart target is inside `O` or disjoint from it. -/
theorem cornerChart_target_subset_of_mem {k : Fin R.cornerCount} {b : R.Base}
    (hb : b ∈ (R.cornerChart k).target) (hbO : b ∈ O) : (R.cornerChart k).target ⊆ O :=
  (R.isPreconnected_cornerChart_target k).subset_isClopen ⟨hO, O.isOpen⟩ ⟨b, hb, hbO⟩

include hO in
theorem cornerChart_target_subset (k : R.CornerIn O) : (R.cornerChart k.1).target ⊆ O :=
  R.cornerChart_target_subset_of_mem hO (R.cornerChart_center_mem_target k.1) k.2

include hO in
theorem center_mem_of_mem {k : Fin R.cornerCount} {b : R.Base}
    (hb : b ∈ (R.cornerChart k).target) (hbO : b ∈ O) : R.cornerChart k (0, 0) ∈ O :=
  R.cornerChart_target_subset_of_mem hO hb hbO (R.cornerChart_center_mem_target k)

theorem nonempty_of_cornerIn (k : R.CornerIn O) : Nonempty O :=
  ⟨⟨_, k.2⟩⟩

/-- The restricted corner chart of a corner centred in `O`. -/
def clopenCornerChart (k : R.CornerIn O) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) O ∞ :=
  codRestrictOpens (R.cornerChart k.1) O (R.nonempty_of_cornerIn k)

include hO in
theorem clopenCornerChart_val (k : R.CornerIn O) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    (R.clopenCornerChart k v : R.Base) = R.cornerChart k.1 v :=
  codRestrictOpens_apply _ _ _ (R.cornerChart_target_subset hO k (R.cornerChart_mem_target k.1 hv))

include hO in
theorem clopenCornerChart_source (k : R.CornerIn O) :
    (R.clopenCornerChart k).source = rimBox 2 :=
  (codRestrictOpens_source _ _ _ (R.cornerChart_target_subset hO k)).trans (R.cornerChart_source k.1)

variable {R} in
include hO in
theorem mem_iUnion_clopenCornerChart_iff {b : O} :
    b ∈ (⋃ k, R.clopenCornerChart (R.cornerInEquiv O k) '' rimBox 1) ↔
      b.val ∈ ⋃ k, R.cornerChart k '' rimBox 1 := by
  have h12 : ∀ {v : ℝ × ℝ}, v ∈ rimBox 1 → v ∈ rimBox 2 :=
    fun hv => ⟨hv.1.trans one_lt_two, hv.2.trans one_lt_two⟩
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨k, v, hv, rfl⟩
    exact ⟨_, v, hv, (R.clopenCornerChart_val hO _ (h12 hv)).symm⟩
  · rintro ⟨k, v, hv, hvb⟩
    have hk : R.cornerChart k (0, 0) ∈ O :=
      R.center_mem_of_mem hO (R.cornerChart_mem_target k (h12 hv)) (hvb ▸ b.2)
    refine ⟨(R.cornerInEquiv O).symm ⟨k, hk⟩, v, hv, Subtype.ext ?_⟩
    rw [R.clopenCornerChart_val hO _ (h12 hv), Equiv.apply_symm_apply]
    exact hvb

/-- **A circle region restricted to a clopen set of its base** (corners centred in the set). -/
def restrictClopen : CircleRegion W where
  Base := O
  domain := R.restrictDomain O
  domain_interior := fun _ hx => R.domain_interior hx.fst
  proj := R.restrictProj O
  proj_smooth := R.contMDiff_restrictProj O
  proj_submersion x := by
    rw [R.mfderiv_restrictProj O x]
    exact R.proj_submersion _
  neighborhood := R.restrictNeighborhood O
  mem_neighborhood b := R.mem_neighborhood b.val
  trivialization := R.restrictTrivialization O
  projection_trivialization b x := by
    apply Subtype.ext
    change ((R.trivialization b.val (R.restrictTrivIn O b x)).1).val = _
    rw [R.trivialization_fst_val]
    rfl
  definingCount := R.definingCount
  defining l b := R.defining l b.val
  defining_smooth l := (R.defining_smooth l).comp contMDiff_subtype_val
  defining_regular l b hb := by
    rw [DifferentialGeometry.mfderiv_restrict_open (R.defining l) O b]
    exact R.defining_regular l b.val hb
  depth_le_two b := R.depth_le_two b.val
  defining_independent b l l' hll' hl hl' := by
    rw [DifferentialGeometry.mfderiv_restrict_open (R.defining l) O b,
      DifferentialGeometry.mfderiv_restrict_open (R.defining l') O b]
    exact R.defining_independent b.val l l' hll' hl hl'
  cornerBase := Subtype.val ⁻¹' R.cornerBase
  cornerBase_eq := by
    ext b
    simp only [mem_preimage, mem_ofPred_eq]
    rw [R.cornerBase_eq]
    rfl
  cornerBase_compact := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have : Subtype.val '' (Subtype.val ⁻¹' R.cornerBase : Set O) =
        (O : Set R.Base) ∩ R.cornerBase := by
      ext b
      constructor
      · rintro ⟨b', hb', rfl⟩
        exact ⟨b'.2, hb'⟩
      · rintro ⟨hbO, hb⟩
        exact ⟨⟨b, hbO⟩, hb, rfl⟩
    convert R.cornerBase_compact.inter_left hO using 1
  cornerCount := Fintype.card (R.CornerIn O)
  cornerChart k := R.clopenCornerChart (R.cornerInEquiv O k)
  cornerChart_source k := R.clopenCornerChart_source hO _
  cornerChart_disjoint k k' hkk' := by
    change Disjoint (codRestrictOpens _ _ _).target (codRestrictOpens _ _ _).target
    rw [codRestrictOpens_target, codRestrictOpens_target]
    refine (R.cornerChart_disjoint fun h => hkk' ?_).preimage _
    exact (R.cornerInEquiv O).injective (Subtype.ext h)
  cornerFirst k := R.cornerFirst (R.cornerInEquiv O k).1
  cornerSecond k := R.cornerSecond (R.cornerInEquiv O k).1
  corner_ne k := R.corner_ne _
  cornerScale k := R.cornerScale (R.cornerInEquiv O k).1
  cornerScale_pos k := R.cornerScale_pos _
  chart_first k v hv := by
    rw [R.clopenCornerChart_val hO _ hv]
    exact R.chart_first _ v hv
  chart_second k v hv := by
    rw [R.clopenCornerChart_val hO _ hv]
    exact R.chart_second _ v hv
  chart_other k l v h1 h2 hv := by
    rw [R.clopenCornerChart_val hO _ hv]
    exact R.chart_other _ l v h1 h2 hv
  corner_center b l l' hll' hl hl' := by
    obtain ⟨k, hk⟩ := R.corner_center b.val l l' hll' hl hl'
    have hc : R.cornerChart k (0, 0) ∈ O := hk ▸ b.2
    refine ⟨(R.cornerInEquiv O).symm ⟨k, hc⟩, Subtype.ext ?_⟩
    rw [R.clopenCornerChart_val hO _ (by simp [rimBox]), Equiv.apply_symm_apply]
    exact hk
  rounding b := R.rounding b.val
  rounding_smooth := R.rounding_smooth.comp contMDiff_subtype_val
  rounding_regular b hb := by
    rw [DifferentialGeometry.mfderiv_restrict_open R.rounding O b]
    exact R.rounding_regular b.val hb
  rounding_chart k v hv := by
    rw [R.clopenCornerChart_val hO _ hv]
    exact R.rounding_chart _ v hv
  rounding_agree := by
    ext b
    have h := Set.ext_iff.mp R.rounding_agree b.val
    simp only [mem_sdiff, mem_ofPred_eq, mem_preimage] at h ⊢
    rw [CircleRegion.mem_iUnion_clopenCornerChart_iff hO]
    exact h
  rounded_compact := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have : Subtype.val '' {b : O | R.rounding b.val ≤ 0} =
        (O : Set R.Base) ∩ {b | R.rounding b ≤ 0} := by
      ext b
      constructor
      · rintro ⟨b', hb', rfl⟩
        exact ⟨b'.2, hb'⟩
      · rintro ⟨hbO, hb⟩
        exact ⟨⟨b, hbO⟩, hb, rfl⟩
    convert R.rounded_compact.inter_left hO using 1

theorem restrictClopen_domain : (R.restrictClopen hO).domain = R.restrictDomain O :=
  rfl

theorem restrictClopen_proj_val (x : (R.restrictClopen hO).domain) :
    (show O from (R.restrictClopen hO).proj x).val = R.proj ⟨x.val, R.restrictDomain_le O x.2⟩ :=
  rfl

theorem restrictClopen_cornerChart_val (k : Fin (R.restrictClopen hO).cornerCount) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    (show O from (R.restrictClopen hO).cornerChart k v).val =
      R.cornerChart (R.cornerInEquiv O k).1 v :=
  R.clopenCornerChart_val hO _ hv

/-- A base set has the same preimage after the restriction (inside `O`). -/
theorem val_image_proj_preimage_restrictClopen (A : Set R.Base) :
    Subtype.val '' ((R.restrictClopen hO).proj ⁻¹' (Subtype.val ⁻¹' A : Set O)) =
      Subtype.val '' (R.proj ⁻¹' (A ∩ O)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, R.restrictDomain_le O y.2⟩, ⟨hy, y.2.snd⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, y.2, hy.2⟩, hy.1, rfl⟩

end Clopen

end CircleRegion

/-! ## The base part of a component and the circle region of the component carrier -/

namespace CircleRegion

variable {Q : CompactCarrier.{u}} (R : CircleRegion Q) (DQ : Q.Components) (i : Fin DQ.count)

/-- The base part of the component `i`. -/
def compBase : TopologicalSpace.Opens R.Base :=
  ⟨R.proj '' {x | x.val ∈ DQ.piece i}, R.isOpenMap_proj _
    ((DQ.piece i).isOpen.preimage continuous_subtype_val)⟩

variable {R DQ i} in
theorem mem_compBase_iff {x : R.domain} : R.proj x ∈ R.compBase DQ i ↔ x.val ∈ DQ.piece i := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hfib := R.isPreconnected_fibre y
    have hsub := subset_piece_pointComp (DQ := DQ) hfib ⟨y, rfl, rfl⟩
    have hy' : pointComp DQ y.val = i := pointComp_eq_of_mem hy
    rw [hy'] at hsub
    exact hsub ⟨x, hyx.symm, rfl⟩
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isClosed_compBase : IsClosed (R.compBase DQ i : Set R.Base) := by
  have h : (R.compBase DQ i : Set R.Base)ᶜ = R.proj '' {x | x.val ∉ DQ.piece i} := by
    ext b
    obtain ⟨x, rfl⟩ := R.surjective_proj b
    constructor
    · intro hb
      exact ⟨x, fun hx => hb ((mem_compBase_iff (x := x)).mpr hx), rfl⟩
    · rintro ⟨y, hy, hyx⟩ hb
      rw [← hyx] at hb
      exact hy ((mem_compBase_iff (x := y)).mp hb)
  rw [← isOpen_compl_iff, h]
  exact R.isOpenMap_proj _ ((DQ.closed i).isOpen_compl.preimage continuous_subtype_val)

/-- The clopen restriction to the component base. -/
abbrev compRegion : CircleRegion Q :=
  R.restrictClopen (R.isClosed_compBase DQ i)

theorem compRegion_domain_subset : ((R.compRegion DQ i).domain : Set Q.Carrier) ⊆ DQ.piece i :=
  fun _ hx => (mem_compBase_iff (x := ⟨_, hx.fst⟩)).mp hx.snd

/-- The domain of the component circle region, inside the component carrier. -/
def compDomain : TopologicalSpace.Opens (GC.Topology.componentCarrier Q DQ i).Carrier :=
  TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (R.compRegion DQ i).domain

theorem compDomain_subset_interior :
    ((R.compDomain DQ i : TopologicalSpace.Opens (GC.Topology.componentCarrier Q DQ i).Carrier) :
      Set (GC.Topology.componentCarrier Q DQ i).Carrier) ⊆
      (GC.Topology.componentCarrier Q DQ i).interior :=
  fun _ hx => mem_componentInterior_iff.mpr ((R.compRegion DQ i).domain_interior hx)

/-- The domain of the component circle region moved into the component carrier. -/
def compDomainDiffeo :
    R.compDomain DQ i ≃ₘ⟮(GC.Topology.componentCarrier Q DQ i).model, Q.model⟯
      (R.compRegion DQ i).domain where
  toFun x := ⟨x.val.val, x.2⟩
  invFun y := ⟨⟨y.val, R.compRegion_domain_subset DQ i y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff (J := Q.model)
      ((R.compRegion DQ i).domain) _).mp
    have h : ContMDiff (GC.Topology.componentCarrier Q DQ i).model Q.model ∞
        (fun x : R.compDomain DQ i => (x.val.val : Q.Carrier)) :=
      (contMDiff_subtype_val (I := Q.model) (U := DQ.piece i)).comp
        (contMDiff_subtype_val (I := (GC.Topology.componentCarrier Q DQ i).model)
          (U := R.compDomain DQ i))
    exact h
  contMDiff_invFun := by
    apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
      (J := (GC.Topology.componentCarrier Q DQ i).model) (R.compDomain DQ i) _).mp
    apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff (J := Q.model)
      (DQ.piece i) _).mp
    have h : ContMDiff Q.model Q.model ∞
        (fun y : (R.compRegion DQ i).domain => (y.val : Q.Carrier)) :=
      contMDiff_subtype_val
    exact h

/-- **The circle region of the component carrier.** -/
def toComponent : CircleRegion (GC.Topology.componentCarrier Q DQ i) :=
  (R.compRegion DQ i).ofDomainDiffeomorph (R.compDomain DQ i) (R.compDomain_subset_interior DQ i)
    (R.compDomainDiffeo DQ i)

theorem toComponent_domain :
    (R.toComponent DQ i).domain = R.compDomain DQ i :=
  rfl

variable {R DQ i} in
theorem mem_toComponent_domain_iff {x : (GC.Topology.componentCarrier Q DQ i).Carrier} :
    x ∈ (R.toComponent DQ i).domain ↔ x.val ∈ R.domain := by
  constructor
  · intro hx
    exact R.restrictDomain_le _ hx
  · intro hx
    exact ⟨hx, (mem_compBase_iff (x := ⟨x.val, hx⟩)).mpr x.2⟩

theorem toComponent_proj_val (x : (R.toComponent DQ i).domain) :
    (show R.compBase DQ i from (R.toComponent DQ i).proj x).val =
      R.proj ⟨x.val.val, R.restrictDomain_le _ x.2⟩ :=
  rfl

theorem toComponent_defining (l : Fin (R.toComponent DQ i).definingCount)
    (b : (R.toComponent DQ i).Base) :
    (R.toComponent DQ i).defining l b = R.defining l b.val :=
  rfl

theorem toComponent_cornerChart_val (k : Fin (R.toComponent DQ i).cornerCount) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    (show R.compBase DQ i from (R.toComponent DQ i).cornerChart k v).val =
      R.cornerChart (R.cornerInEquiv (R.compBase DQ i) k).1 v :=
  R.clopenCornerChart_val (R.isClosed_compBase DQ i) _ hv

/-- **Base sets have preimage-of-preimage fibres in the component.** -/
theorem val_image_proj_preimage_toComponent (A : Set R.Base) :
    Subtype.val '' ((R.toComponent DQ i).proj ⁻¹' (Subtype.val ⁻¹' A : Set (R.compBase DQ i))) =
      Subtype.val ⁻¹' (Subtype.val '' (R.proj ⁻¹' A)) := by
  have h1 := (R.compRegion DQ i).val_image_proj_preimage_ofDomainDiffeomorph (R.compDomain DQ i)
    (R.compDomain_subset_interior DQ i) (R.compDomainDiffeo DQ i)
    (Subtype.val ⁻¹' A : Set (R.compBase DQ i))
  change Subtype.val '' ((R.toComponent DQ i).proj ⁻¹' _) = _ at h1
  rw [h1]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, R.restrictDomain_le _ y.2⟩, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyd : y.val ∈ (R.compRegion DQ i).domain :=
      ⟨y.2, (mem_compBase_iff (x := y)).mpr (hyx ▸ x.2)⟩
    refine ⟨⟨y.val, hyd⟩, hy, ?_⟩
    exact Subtype.ext hyx

theorem region_toComponent : (R.toComponent DQ i).region = Subtype.val ⁻¹' R.region :=
  R.val_image_proj_preimage_toComponent DQ i R.cornerBase

theorem rounded_toComponent : (R.toComponent DQ i).rounded = Subtype.val ⁻¹' R.rounded :=
  R.val_image_proj_preimage_toComponent DQ i {b | R.rounding b ≤ 0}

theorem fibre_toComponent (b : (R.toComponent DQ i).Base) :
    Subtype.val '' ((R.toComponent DQ i).proj ⁻¹' {b}) =
      Subtype.val ⁻¹' (Subtype.val '' (R.proj ⁻¹' {b.val})) := by
  rw [← R.val_image_proj_preimage_toComponent DQ i {b.val}]
  congr 2
  ext b'
  simp only [mem_singleton_iff]
  exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩

/-- A point of the component over the domain of `R` lies in the component domain, with the same
base point. -/
theorem exists_toComponent_proj {x : (GC.Topology.componentCarrier Q DQ i).Carrier}
    {y : R.domain} (hxy : x.val = y.val) :
    ∃ hx : x ∈ (R.toComponent DQ i).domain,
      (show R.compBase DQ i from (R.toComponent DQ i).proj ⟨x, hx⟩).val = R.proj y := by
  have hx : x ∈ (R.toComponent DQ i).domain := mem_toComponent_domain_iff.mpr (hxy ▸ y.2)
  refine ⟨hx, ?_⟩
  exact congrArg R.proj (Subtype.ext hxy)

end CircleRegion

end GC.GraphManifold.Assembly
