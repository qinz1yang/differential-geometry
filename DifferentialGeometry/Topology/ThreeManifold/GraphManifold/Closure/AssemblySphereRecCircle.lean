import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecSides
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# FC42 sphere recursion, packet S2 (circle region): saturated restriction and lift

Lane ASM-SPH (review 40 §2.4: "`circ.domain` must first be restricted to a saturated open
neighbourhood of `circ.region`; `sphereSeam_region_disjoint` alone does not transport the whole old
domain").

* `CircleRegion.ofDomainDiffeomorph`: a circle region carried along a diffeomorphism of its domain
  onto an open set of `Q.interior` (all base data unchanged).
* `CircleRegion.restrictBase`: a circle region restricted to an open set `O` of its base containing
  the cornered base, the rounded base and every corner-chart target (base `O`, domain the saturated
  open set `proj⁻¹ O`); the cornered and rounded regions do not change
  (`region_restrictBase`, `rounded_restrictBase`). This is also the tool for the later restriction
  to one capped component (S1's clopen label bases).
* `SphereCutCapped.liftCircleRegion`: a circle region whose domain avoids the seam sphere, carried
  into the capped carrier by the transport (`region_liftCircleRegion = transport '' region`).
* Certificate level: `DecompositionCertificate.seamAvoidingBase c`, the open set of base points
  whose whole fibre avoids the seam sphere (open by the closed-map property of the trivializations
  with compact circle fibre); it contains the cornered base, the rounded base and every corner
  chart target (the rounding supports are rim-chart targets, which avoid the seam collar);
  `circAway c` is the restricted circle region, with the SAME region and rounded region, and
  `liftCircleRegion c X` its lift into the capped carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-! ## Transport of the domain -/

/-- A circle region carried along a diffeomorphism of its domain onto an open set of another
carrier (base data unchanged). -/
def ofDomainDiffeomorph {Q : CompactCarrier.{u}} (U : TopologicalSpace.Opens Q.Carrier)
    (hU : (U : Set Q.Carrier) ⊆ Q.interior) (e : U ≃ₘ⟮Q.model, W.model⟯ R.domain) :
    CircleRegion Q where
  Base := R.Base
  domain := U
  domain_interior := hU
  proj := R.proj.comp ⟨e, e.continuous⟩
  proj_smooth := R.proj_smooth.comp e.contMDiff
  proj_submersion x := by
    have hcomp : mfderiv Q.model (𝓡 2) (R.proj ∘ e) x =
        (mfderiv W.model (𝓡 2) R.proj (e x)).comp (mfderiv Q.model W.model e x) :=
      mfderiv_comp x (R.proj_smooth.mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))
    intro w
    obtain ⟨v, hv⟩ := R.proj_submersion (e x) w
    obtain ⟨t, ht⟩ := (e.mfderivToContinuousLinearEquiv (by simp) x).surjective v
    have ht' : mfderiv Q.model W.model e x t = v := ht
    refine ⟨t, (DFunLike.congr_fun hcomp t).trans ?_⟩
    change mfderiv W.model (𝓡 2) R.proj (e x) (mfderiv Q.model W.model e x t) = w
    rw [ht']
    exact hv
  neighborhood := R.neighborhood
  mem_neighborhood := R.mem_neighborhood
  trivialization b :=
    (opensComapDiffeomorph e (TopologicalSpace.Opens.comap R.proj (R.neighborhood b))).trans
      (R.trivialization b)
  projection_trivialization b _ := R.projection_trivialization b _
  definingCount := R.definingCount
  defining := R.defining
  defining_smooth := R.defining_smooth
  defining_regular := R.defining_regular
  depth_le_two := R.depth_le_two
  defining_independent := R.defining_independent
  cornerBase := R.cornerBase
  cornerBase_eq := R.cornerBase_eq
  cornerBase_compact := R.cornerBase_compact
  cornerCount := R.cornerCount
  cornerChart := R.cornerChart
  cornerChart_source := R.cornerChart_source
  cornerChart_disjoint := R.cornerChart_disjoint
  cornerFirst := R.cornerFirst
  cornerSecond := R.cornerSecond
  corner_ne := R.corner_ne
  cornerScale := R.cornerScale
  cornerScale_pos := R.cornerScale_pos
  chart_first := R.chart_first
  chart_second := R.chart_second
  chart_other := R.chart_other
  corner_center := R.corner_center
  rounding := R.rounding
  rounding_smooth := R.rounding_smooth
  rounding_regular := R.rounding_regular
  rounding_chart := R.rounding_chart
  rounding_agree := R.rounding_agree
  rounded_compact := R.rounded_compact

theorem ofDomainDiffeomorph_proj {Q : CompactCarrier.{u}} (U : TopologicalSpace.Opens Q.Carrier)
    (hU : (U : Set Q.Carrier) ⊆ Q.interior) (e : U ≃ₘ⟮Q.model, W.model⟯ R.domain) (x : U) :
    (R.ofDomainDiffeomorph U hU e).proj x = R.proj (e x) :=
  rfl

/-- The preimage of a base set under the transported region: the image of the old one. -/
theorem val_image_proj_preimage_ofDomainDiffeomorph {Q : CompactCarrier.{u}}
    (U : TopologicalSpace.Opens Q.Carrier) (hU : (U : Set Q.Carrier) ⊆ Q.interior)
    (e : U ≃ₘ⟮Q.model, W.model⟯ R.domain) (A : Set R.Base) :
    Subtype.val '' ((R.ofDomainDiffeomorph U hU e).proj ⁻¹' A) =
      (fun y => (e.symm y).val) '' (R.proj ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e y, hy, congrArg Subtype.val (e.symm_apply_apply y)⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e.symm y, ?_, rfl⟩
    change R.proj (e (e.symm y)) ∈ A
    rw [e.apply_symm_apply]
    exact hy

/-! ## Restriction to an open set of the base -/

/-- The domain over an open set of the base (a saturated open set). -/
def restrictDomain (O : TopologicalSpace.Opens R.Base) : TopologicalSpace.Opens W.Carrier :=
  ⟨{x | ∃ h : x ∈ R.domain, R.proj ⟨x, h⟩ ∈ O}, by
    have hset : {x | ∃ h : x ∈ R.domain, R.proj ⟨x, h⟩ ∈ O} =
        Subtype.val '' (R.proj ⁻¹' (O : Set R.Base)) := by
      ext x
      constructor
      · rintro ⟨h, hx⟩
        exact ⟨⟨x, h⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
    rw [hset]
    exact R.domain.isOpen.isOpenMap_subtype_val _ (O.isOpen.preimage R.proj.continuous)⟩

variable {R} in
theorem mem_restrictDomain_iff {O : TopologicalSpace.Opens R.Base} {x : W.Carrier} :
    x ∈ R.restrictDomain O ↔ ∃ h : x ∈ R.domain, R.proj ⟨x, h⟩ ∈ O :=
  Iff.rfl

theorem restrictDomain_le (O : TopologicalSpace.Opens R.Base) : R.restrictDomain O ≤ R.domain :=
  fun _ hx => hx.fst

/-- The projection over the open set `O`. -/
def restrictProj (O : TopologicalSpace.Opens R.Base) : C(R.restrictDomain O, O) where
  toFun x := ⟨R.proj (TopologicalSpace.Opens.inclusion (R.restrictDomain_le O) x), x.2.snd⟩
  continuous_toFun :=
    (R.proj.continuous.comp (continuous_inclusion (R.restrictDomain_le O))).subtype_mk _

theorem restrictProj_val (O : TopologicalSpace.Opens R.Base) (x : R.restrictDomain O) :
    (R.restrictProj O x).val = R.proj (TopologicalSpace.Opens.inclusion (R.restrictDomain_le O) x) :=
  rfl

theorem contMDiff_restrictProj (O : TopologicalSpace.Opens R.Base) :
    ContMDiff W.model (𝓡 2) ∞ (R.restrictProj O) :=
  (ContMDiff.subtypeVal_comp_iff O _).mp
    (R.proj_smooth.comp (contMDiff_inclusion (R.restrictDomain_le O)))

theorem mfderiv_restrictProj (O : TopologicalSpace.Opens R.Base) (x : R.restrictDomain O) :
    mfderiv W.model (𝓡 2) (R.restrictProj O) x =
      mfderiv W.model (𝓡 2) R.proj (TopologicalSpace.Opens.inclusion (R.restrictDomain_le O) x) := by
  rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp O (R.restrictProj O) x]
  change mfderiv W.model (𝓡 2)
    (R.proj ∘ TopologicalSpace.Opens.inclusion (R.restrictDomain_le O)) x = _
  rw [mfderiv_comp x (R.proj_smooth.mdifferentiableAt (by simp))
    ((contMDiff_inclusion (R.restrictDomain_le O)).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)),
    DifferentialGeometry.mfderiv_opens_incl]
  rfl

/-- The base neighbourhoods over `O`. -/
def restrictNeighborhood (O : TopologicalSpace.Opens R.Base) (b : O) :
    TopologicalSpace.Opens O :=
  TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (R.neighborhood b.val)

section Triv

variable (O : TopologicalSpace.Opens R.Base) (b : O)

/-- The old trivialization domain point of a point of the restricted trivialization domain. -/
def restrictTrivIn
    (x : TopologicalSpace.Opens.comap (R.restrictProj O) (R.restrictNeighborhood O b)) :
    TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val) :=
  ⟨TopologicalSpace.Opens.inclusion (R.restrictDomain_le O) x.val, x.2⟩

theorem trivialization_fst_val (a : TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val)) :
    ((R.trivialization b.val a).1).val = R.proj a.val :=
  R.projection_trivialization b.val a

/-- The restricted trivialization, forward map. -/
def restrictTrivFun
    (x : TopologicalSpace.Opens.comap (R.restrictProj O) (R.restrictNeighborhood O b)) :
    R.restrictNeighborhood O b × Circle :=
  (⟨⟨((R.trivialization b.val (R.restrictTrivIn O b x)).1).val, by
      rw [R.trivialization_fst_val]
      exact x.val.2.snd⟩, ((R.trivialization b.val (R.restrictTrivIn O b x)).1).2⟩,
    (R.trivialization b.val (R.restrictTrivIn O b x)).2)

/-- The restricted trivialization, inverse map. -/
def restrictTrivInv (y : R.restrictNeighborhood O b × Circle) :
    TopologicalSpace.Opens.comap (R.restrictProj O) (R.restrictNeighborhood O b) :=
  let a := (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)
  have ha : R.proj a.val = y.1.val.val := by
    rw [← R.trivialization_fst_val, Diffeomorph.apply_symm_apply]
  ⟨⟨a.val.val, a.val.2, by
      change R.proj a.val ∈ O
      rw [ha]
      exact y.1.val.2⟩, by
    change R.proj a.val ∈ R.neighborhood b.val
    rw [ha]
    exact y.1.2⟩

theorem restrictTrivInv_in (y : R.restrictNeighborhood O b × Circle) :
    R.restrictTrivIn O b (R.restrictTrivInv O b y) =
      (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2) :=
  rfl

theorem restrictTrivFun_in
    (x : TopologicalSpace.Opens.comap (R.restrictProj O) (R.restrictNeighborhood O b)) :
    (R.trivialization b.val).symm
        (⟨(R.restrictTrivFun O b x).1.val.val, (R.restrictTrivFun O b x).1.2⟩,
          (R.restrictTrivFun O b x).2) = R.restrictTrivIn O b x := by
  rw [show (⟨(R.restrictTrivFun O b x).1.val.val, (R.restrictTrivFun O b x).1.2⟩,
      (R.restrictTrivFun O b x).2) = R.trivialization b.val (R.restrictTrivIn O b x) from rfl,
    Diffeomorph.symm_apply_apply]

theorem contMDiff_restrictTrivIn :
    ContMDiff W.model W.model ∞ (R.restrictTrivIn O b) := by
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff W.model W.model ∞
      (fun x : TopologicalSpace.Opens.comap (R.restrictProj O) (R.restrictNeighborhood O b) =>
        (x.val.val : W.Carrier)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  exact h

theorem contMDiff_restrictTrivFun :
    ContMDiff W.model ((𝓡 2).prod (𝓡 1)) ∞ (R.restrictTrivFun O b) := by
  have hT : ContMDiff W.model ((𝓡 2).prod (𝓡 1)) ∞
      (fun x => R.trivialization b.val (R.restrictTrivIn O b x)) :=
    (R.trivialization b.val).contMDiff.comp (R.contMDiff_restrictTrivIn O b)
  refine ContMDiff.prodMk ?_ (contMDiff_snd.comp hT)
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff W.model (𝓡 2) ∞
      (fun x => ((R.trivialization b.val (R.restrictTrivIn O b x)).1 : R.Base)) :=
    contMDiff_subtype_val.comp (contMDiff_fst.comp hT)
  exact h

theorem contMDiff_restrictTrivInv :
    ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞ (R.restrictTrivInv O b) := by
  have hin : ContMDiff ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (fun y : R.restrictNeighborhood O b × Circle =>
        ((⟨y.1.val.val, y.1.2⟩ : R.neighborhood b.val), y.2)) := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (contMDiff_subtype_val.comp contMDiff_subtype_val).comp contMDiff_fst
  have hT : ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞
      (fun y : R.restrictNeighborhood O b × Circle =>
        (R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)) :=
    (R.trivialization b.val).symm.contMDiff.comp hin
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  have h : ContMDiff ((𝓡 2).prod (𝓡 1)) W.model ∞
      (fun y : R.restrictNeighborhood O b × Circle =>
        (((R.trivialization b.val).symm (⟨y.1.val.val, y.1.2⟩, y.2)).val.val : W.Carrier)) :=
    (contMDiff_subtype_val.comp contMDiff_subtype_val).comp hT
  exact h

/-- The restricted trivialization. -/
def restrictTrivialization :
    TopologicalSpace.Opens.comap (R.restrictProj O) (R.restrictNeighborhood O b) ≃ₘ⟮W.model,
      (𝓡 2).prod (𝓡 1)⟯ (R.restrictNeighborhood O b × Circle) where
  toFun := R.restrictTrivFun O b
  invFun := R.restrictTrivInv O b
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun a : TopologicalSpace.Opens.comap R.proj (R.neighborhood b.val) =>
      a.val.val) (R.restrictTrivFun_in O b x)
    exact h
  right_inv y := by
    have h := Diffeomorph.apply_symm_apply (R.trivialization b.val) (⟨y.1.val.val, y.1.2⟩, y.2)
    rw [← R.restrictTrivInv_in O b y] at h
    rcases y with ⟨⟨⟨c, hcO⟩, hc⟩, θ⟩
    simp only [Prod.ext_iff] at h
    refine Prod.ext ?_ h.2
    apply Subtype.ext
    apply Subtype.ext
    have h3 := congrArg Subtype.val h.1
    exact h3
  contMDiff_toFun := R.contMDiff_restrictTrivFun O b
  contMDiff_invFun := R.contMDiff_restrictTrivInv O b

end Triv

variable {O : TopologicalSpace.Opens R.Base}

/-- **A circle region restricted to an open set of its base** containing the cornered base, the
rounded base and every corner-chart target. -/
abbrev restrictBase (O : TopologicalSpace.Opens R.Base) (hcorner : R.cornerBase ⊆ O)
    (hround : {b | R.rounding b ≤ 0} ⊆ O) (hchart : ∀ k, (R.cornerChart k).target ⊆ O) :
    CircleRegion W where
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
    convert R.cornerBase_compact using 1
    ext b
    constructor
    · rintro ⟨b', hb', rfl⟩
      exact hb'
    · intro hb
      exact ⟨⟨b, hcorner hb⟩, hb, rfl⟩
  cornerCount := R.cornerCount
  cornerChart k := codRestrictOpens (R.cornerChart k) O
    ⟨⟨R.cornerChart k (0, 0), hchart k ((R.cornerChart k).map_source
      (by rw [R.cornerChart_source]; simp [rimBox]))⟩⟩
  cornerChart_source k := (codRestrictOpens_source _ _ _ (hchart k)).trans (R.cornerChart_source k)
  cornerChart_disjoint k k' hkk' := by
    dsimp only
    rw [codRestrictOpens_target, codRestrictOpens_target]
    exact (R.cornerChart_disjoint hkk').preimage _
  cornerFirst := R.cornerFirst
  cornerSecond := R.cornerSecond
  corner_ne := R.corner_ne
  cornerScale := R.cornerScale
  cornerScale_pos := R.cornerScale_pos
  chart_first k v hv := by
    rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
      ((R.cornerChart_source k).symm ▸ hv)))]
    exact R.chart_first k v hv
  chart_second k v hv := by
    rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
      ((R.cornerChart_source k).symm ▸ hv)))]
    exact R.chart_second k v hv
  chart_other k l v h1 h2 hv := by
    rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
      ((R.cornerChart_source k).symm ▸ hv)))]
    exact R.chart_other k l v h1 h2 hv
  corner_center b l l' hll' hl hl' := by
    obtain ⟨k, hk⟩ := R.corner_center b.val l l' hll' hl hl'
    refine ⟨k, Subtype.ext ?_⟩
    rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
      (by rw [R.cornerChart_source]; simp [rimBox])))]
    exact hk
  rounding b := R.rounding b.val
  rounding_smooth := R.rounding_smooth.comp contMDiff_subtype_val
  rounding_regular b hb := by
    rw [DifferentialGeometry.mfderiv_restrict_open R.rounding O b]
    exact R.rounding_regular b.val hb
  rounding_chart k v hv := by
    rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
      ((R.cornerChart_source k).symm ▸ hv)))]
    exact R.rounding_chart k v hv
  rounding_agree := by
    have hmem : ∀ (b : O),
        b ∈ (⋃ k, codRestrictOpens (R.cornerChart k) O
          ⟨⟨R.cornerChart k (0, 0), hchart k ((R.cornerChart k).map_source
            (by rw [R.cornerChart_source]; simp [rimBox]))⟩⟩ '' rimBox 1) ↔
        b.val ∈ ⋃ k, R.cornerChart k '' rimBox 1 := by
      intro b
      simp only [mem_iUnion, mem_image]
      constructor
      · rintro ⟨k, v, hv, rfl⟩
        refine ⟨k, v, hv, ?_⟩
        rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
          (by rw [R.cornerChart_source]; exact ⟨hv.1.trans one_lt_two, hv.2.trans one_lt_two⟩)))]
      · rintro ⟨k, v, hv, hvb⟩
        refine ⟨k, v, hv, Subtype.ext ?_⟩
        rw [codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
          (by rw [R.cornerChart_source]; exact ⟨hv.1.trans one_lt_two, hv.2.trans one_lt_two⟩)))]
        exact hvb
    ext b
    have h := Set.ext_iff.mp R.rounding_agree b.val
    simp only [mem_sdiff, mem_ofPred_eq, mem_preimage] at h ⊢
    rw [hmem b]
    exact h
  rounded_compact := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert R.rounded_compact using 1
    ext b
    constructor
    · rintro ⟨b', hb', rfl⟩
      exact hb'
    · intro hb
      exact ⟨⟨b, hround hb⟩, hb, rfl⟩

section RestrictBase

variable (hcorner : R.cornerBase ⊆ O) (hround : {b | R.rounding b ≤ 0} ⊆ O)
  (hchart : ∀ k, (R.cornerChart k).target ⊆ O)

theorem restrictBase_domain :
    ((R.restrictBase O hcorner hround hchart).domain : Set W.Carrier) =
      Subtype.val '' (R.proj ⁻¹' (O : Set R.Base)) := by
  ext x
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩

theorem restrictBase_proj_val (x : (R.restrictBase O hcorner hround hchart).domain) :
    (((R.restrictBase O hcorner hround hchart).proj x : O) : R.Base) =
      R.proj ⟨x.val, R.restrictDomain_le O x.2⟩ :=
  rfl

theorem restrictBase_cornerChart_val (k : Fin R.cornerCount) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    (((R.restrictBase O hcorner hround hchart).cornerChart k v : O) : R.Base) = R.cornerChart k v :=
  codRestrictOpens_apply _ _ _ (hchart k ((R.cornerChart k).map_source
    ((R.cornerChart_source k).symm ▸ hv)))

/-- A base set inside `O` has the same preimage in `W`. -/
theorem val_image_proj_preimage_restrictBase {A : Set R.Base} (hA : A ⊆ O) :
    Subtype.val '' ((R.restrictBase O hcorner hround hchart).proj ⁻¹'
        (Subtype.val ⁻¹' A : Set O)) =
      Subtype.val '' (R.proj ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, R.restrictDomain_le O y.2⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, y.2, hA hy⟩, hy, rfl⟩

/-- **The cornered region does not change.** -/
theorem region_restrictBase :
    (R.restrictBase O hcorner hround hchart).region = R.region :=
  R.val_image_proj_preimage_restrictBase hcorner hround hchart hcorner

/-- **The rounded region does not change.** -/
theorem rounded_restrictBase :
    (R.restrictBase O hcorner hround hchart).rounded = R.rounded :=
  R.val_image_proj_preimage_restrictBase hcorner hround hchart hround

end RestrictBase

end CircleRegion

/-! ## The lift into the capped carrier -/

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The transported domain of a circle region avoiding the seam sphere. -/
def liftDomain (R : CircleRegion W) (h : (R.domain : Set W.Carrier) ⊆ S.zeroSphereᶜ) :
    TopologicalSpace.Opens X.Q.Carrier :=
  ⟨X.transport '' (R.domain : Set W.Carrier), DifferentialGeometry.image_opens_isOpen X.transport h⟩

/-- **S2. The circle region lifted into the capped carrier** (domain avoiding the seam sphere). -/
def liftCircleRegion (R : CircleRegion W) (h : (R.domain : Set W.Carrier) ⊆ S.zeroSphereᶜ) :
    CircleRegion X.Q :=
  R.ofDomainDiffeomorph (X.liftDomain R h)
    (X.transport_image_subset_interior R.domain_interior)
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo X.transport h).symm

theorem liftCircleRegion_proj (R : CircleRegion W)
    (h : (R.domain : Set W.Carrier) ⊆ S.zeroSphereᶜ) (y : X.liftDomain R h) :
    (X.liftCircleRegion R h).proj y = R.proj ((DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo X.transport h).symm y) :=
  rfl

theorem val_image_proj_preimage_liftCircleRegion (R : CircleRegion W)
    (h : (R.domain : Set W.Carrier) ⊆ S.zeroSphereᶜ) (A : Set R.Base) :
    Subtype.val '' ((X.liftCircleRegion R h).proj ⁻¹' A) =
      X.transport '' (Subtype.val '' (R.proj ⁻¹' A)) := by
  have h1 := R.val_image_proj_preimage_ofDomainDiffeomorph (X.liftDomain R h)
    (X.transport_image_subset_interior R.domain_interior)
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo X.transport h).symm A
  rw [image_image]
  exact h1

/-- **The lifted region is the transport of the region.** -/
theorem region_liftCircleRegion (R : CircleRegion W)
    (h : (R.domain : Set W.Carrier) ⊆ S.zeroSphereᶜ) :
    (X.liftCircleRegion R h).region = X.transport '' R.region :=
  X.val_image_proj_preimage_liftCircleRegion R h R.cornerBase

theorem rounded_liftCircleRegion (R : CircleRegion W)
    (h : (R.domain : Set W.Carrier) ⊆ S.zeroSphereᶜ) :
    (X.liftCircleRegion R h).rounded = X.transport '' R.rounded :=
  X.val_image_proj_preimage_liftCircleRegion R h _

end SphereCutCapped

/-! ## The certificate's circle region avoiding a sphere seam -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The base points whose whole fibre avoids the seam sphere of `c`. -/
def seamAvoidingSet (c : Fin D.sphereSeamCount) : Set D.circ.Base :=
  {b | ∀ x : D.circ.domain, D.circ.proj x = b → x.val ∉ (D.sphereSeam c).zeroSphere}

theorem isOpen_seamAvoidingSet (c : Fin D.sphereSeamCount) : IsOpen (D.seamAvoidingSet c) := by
  rw [isOpen_iff_forall_mem_open]
  intro b hb
  let N := D.circ.neighborhood b
  let A := TopologicalSpace.Opens.comap D.circ.proj N
  let T := D.circ.trivialization b
  let F : Set A := {a | a.val.val ∈ (D.sphereSeam c).zeroSphere}
  have hF : IsClosed F :=
    (D.sphereSeam c).isClosed_zeroSphere.preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  let g : A → N := fun a => (T a).1
  have hg : IsClosedMap g :=
    (isClosedMap_fst_of_compactSpace (X := N) (Y := Circle)).comp T.toHomeomorph.isClosedMap
  have hgval : ∀ a, (g a).val = D.circ.proj a.val := fun a => D.circ.projection_trivialization b a
  have hbN : b ∈ N := D.circ.mem_neighborhood b
  have hbG : (⟨b, hbN⟩ : N) ∉ g '' F := by
    rintro ⟨a, haF, hab⟩
    have hp : D.circ.proj a.val = b := by rw [← hgval, hab]
    exact hb a.val hp haF
  refine ⟨Subtype.val '' (g '' F)ᶜ, ?_, ?_, ⟨⟨b, hbN⟩, hbG, rfl⟩⟩
  · rintro _ ⟨c', hc', rfl⟩ x hx hxS
    have hxA : x ∈ A := by
      change D.circ.proj x ∈ N
      rw [hx]
      exact c'.2
    apply hc'
    refine ⟨⟨x, hxA⟩, hxS, Subtype.ext ?_⟩
    rw [hgval]
    exact hx
  · exact N.isOpen.isOpenMap_subtype_val _ (hg F hF).isOpen_compl

/-- The open set of `seamAvoidingSet`. -/
def seamAvoidingBase (c : Fin D.sphereSeamCount) : TopologicalSpace.Opens D.circ.Base :=
  ⟨D.seamAvoidingSet c, D.isOpen_seamAvoidingSet c⟩

theorem cornerBase_subset_seamAvoidingBase (c : Fin D.sphereSeamCount) :
    D.circ.cornerBase ⊆ D.seamAvoidingBase c := by
  intro b hb x hx hxS
  have hreg : x.val ∈ D.circ.region := ⟨x, by rw [mem_preimage, hx]; exact hb, rfl⟩
  exact Set.disjoint_left.mp (D.sphereSeam_region_disjoint c)
    ((D.sphereSeam c).zeroSphere_subset_target hxS) hreg

theorem cornerChart_target_subset_seamAvoidingBase (c : Fin D.sphereSeamCount)
    (k : Fin D.circ.cornerCount) : (D.circ.cornerChart k).target ⊆ D.seamAvoidingBase c := by
  intro b hb x hx hxS
  obtain ⟨h, b', -, hk⟩ := D.exists_roundingSupport_eq_rimChart_target k
  have hsupp : x.val ∈ D.circ.roundingSupport k := ⟨x, by rw [mem_preimage, hx]; exact hb, rfl⟩
  rw [hk] at hsupp
  exact Set.disjoint_left.mp (D.rim_sphereSeam_disjoint h b' c) hsupp
    ((D.sphereSeam c).zeroSphere_subset_target hxS)

theorem rounded_subset_seamAvoidingBase (c : Fin D.sphereSeamCount) :
    {b | D.circ.rounding b ≤ 0} ⊆ D.seamAvoidingBase c := by
  intro b hb
  by_cases hU : b ∈ ⋃ k, D.circ.cornerChart k '' rimBox 1
  · obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.mp hU
    exact D.cornerChart_target_subset_seamAvoidingBase c k ((D.circ.cornerChart k).map_source
      (by rw [D.circ.cornerChart_source]; exact ⟨hv.1.trans one_lt_two, hv.2.trans one_lt_two⟩))
  · exact D.cornerBase_subset_seamAvoidingBase c
      ((CircleRegion.rounding_le_zero_iff hU).mp hb)

/-- **The circle region restricted to the saturated open set avoiding the seam sphere of `c`.** -/
def circAway (c : Fin D.sphereSeamCount) : CircleRegion W :=
  D.circ.restrictBase (D.seamAvoidingBase c) (D.cornerBase_subset_seamAvoidingBase c)
    (D.rounded_subset_seamAvoidingBase c) (D.cornerChart_target_subset_seamAvoidingBase c)

theorem circAway_domain_subset (c : Fin D.sphereSeamCount) :
    ((D.circAway c).domain : Set W.Carrier) ⊆ (D.sphereSeam c).zeroSphereᶜ := by
  intro x hx
  exact hx.snd ⟨x, hx.fst⟩ rfl

theorem region_circAway (c : Fin D.sphereSeamCount) : (D.circAway c).region = D.circ.region :=
  D.circ.region_restrictBase (D.cornerBase_subset_seamAvoidingBase c)
    (D.rounded_subset_seamAvoidingBase c) (D.cornerChart_target_subset_seamAvoidingBase c)

theorem rounded_circAway (c : Fin D.sphereSeamCount) : (D.circAway c).rounded = D.circ.rounded :=
  D.circ.rounded_restrictBase (D.cornerBase_subset_seamAvoidingBase c)
    (D.rounded_subset_seamAvoidingBase c) (D.cornerChart_target_subset_seamAvoidingBase c)

/-- **S2. The retained circle region lifted into the capped carrier.** -/
def liftCircleRegion (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) :
    CircleRegion X.Q :=
  X.liftCircleRegion (D.circAway c) (D.circAway_domain_subset c)

theorem region_liftCircleRegion (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) :
    (D.liftCircleRegion c X).region = X.transport '' D.circ.region := by
  rw [liftCircleRegion, SphereCutCapped.region_liftCircleRegion, region_circAway]

theorem rounded_liftCircleRegion (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) :
    (D.liftCircleRegion c X).rounded = X.transport '' D.circ.rounded := by
  rw [liftCircleRegion, SphereCutCapped.rounded_liftCircleRegion, rounded_circAway]

end DecompositionCertificate

end GC.GraphManifold.Assembly
