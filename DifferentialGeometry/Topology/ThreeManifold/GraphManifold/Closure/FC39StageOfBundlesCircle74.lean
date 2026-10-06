import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesTriv74

/-!
# Draft 74, G5 step 3b: the cut-dependent circle facts over `⊤` from an existing circle bundle

Lane S-JUNCTIONS2 (suffix `_JN74`). `circleBundle_proper_JN74`: the whole-circle properness of the
projection of ANY `CircleBundle` (local trivializations over open neighbourhoods with compact
fibre `Circle`, locally compact base). `circleCutFacts_ofBundles74`: for the stage geometry and cut
choice of `FC39StageOfBundles74` the facts `CircleCutFacts74` are the trivializations restricted
over
`⊤` (`FC39StageOfBundlesTriv74`), the properness above, the compact `cbase` and the saturation
`M₃ = circleRegion`, the latter the only input.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace CircleBundle

variable (R : CircleBundle W)

/-- The preimage of a compact subset of a trivialization neighbourhood is compact. -/
theorem isCompact_preimage_nbhd_JN74 (c : R.Base) {K : Set R.Base} (hK : IsCompact K)
    (hKN : K ⊆ R.neighborhood c) :
    IsCompact (Subtype.val '' (R.proj ⁻¹' K) : Set W.Carrier) := by
  let N := R.neighborhood c
  have hKc : IsCompact (Subtype.val ⁻¹' K : Set N) :=
    Topology.IsEmbedding.subtypeVal.isCompact_iff.2
      (by rw [image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hKN hy⟩, rfl⟩)]; exact hK)
  have hprod : IsCompact ((Subtype.val ⁻¹' K : Set N) ×ˢ (univ : Set Circle)) :=
    hKc.prod isCompact_univ
  have himg : IsCompact ((R.trivialization c).symm '' ((Subtype.val ⁻¹' K : Set N) ×ˢ
      (univ : Set Circle))) :=
    hprod.image (R.trivialization c).symm.continuous
  have himg2 : IsCompact (Subtype.val '' (Subtype.val '' ((R.trivialization c).symm ''
      ((Subtype.val ⁻¹' K : Set N) ×ˢ (univ : Set Circle)))) : Set W.Carrier) :=
    (himg.image continuous_subtype_val).image continuous_subtype_val
  convert himg2 using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyN : y ∈ TopologicalSpace.Opens.comap R.proj N := hKN hy
    refine ⟨y, ⟨⟨y, hyN⟩, ⟨R.trivialization c ⟨y, hyN⟩, ⟨?_, mem_univ _⟩,
      Diffeomorph.symm_apply_apply _ _⟩, rfl⟩, rfl⟩
    change ((R.trivialization c ⟨y, hyN⟩).1 : R.Base) ∈ K
    rw [R.projection_trivialization c ⟨y, hyN⟩]
    exact hy
  · rintro ⟨y, ⟨a, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
    refine ⟨((R.trivialization c).symm p).1, ?_, rfl⟩
    have h := R.projection_trivialization c ((R.trivialization c).symm p)
    rw [Diffeomorph.apply_symm_apply] at h
    have hp1 : (p.1 : R.Base) ∈ K := hp.1
    change R.proj ((R.trivialization c).symm p).1 ∈ K
    rw [← h]
    exact hp1

/-- **Whole-circle properness** of the projection of a circle bundle: the preimage of a compact set
of the base is compact. -/
theorem proj_proper_JN74 {K : Set R.Base} (hK : IsCompact K) :
    IsCompact (Subtype.val '' (R.proj ⁻¹' K) : Set W.Carrier) := by
  have hloc : LocallyCompactSpace R.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) R.Base
  have hcov : ∀ c : R.Base, ∃ L : Set R.Base, L ∈ nhds c ∧ L ⊆ R.neighborhood c ∧ IsCompact L :=
    fun c => local_compact_nhds ((R.neighborhood c).isOpen.mem_nhds (R.mem_neighborhood c))
  choose L hLn hLN hLc using hcov
  obtain ⟨t, htK, htcov⟩ := hK.elim_nhds_subcover L fun c _ => hLn c
  have hunion : (Subtype.val '' (R.proj ⁻¹' K) : Set W.Carrier) =
      ⋃ c ∈ (t : Set R.Base), Subtype.val '' (R.proj ⁻¹' (K ∩ L c)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hct, hyc⟩ := mem_iUnion₂.1 (htcov hy)
      exact mem_iUnion₂.2 ⟨c, hct, y, ⟨hy, hyc⟩, rfl⟩
    · intro hx
      obtain ⟨c, -, y, hy, rfl⟩ := mem_iUnion₂.1 hx
      exact ⟨y, hy.1, rfl⟩
  rw [hunion]
  exact t.finite_toSet.isCompact_biUnion fun c hc =>
    R.isCompact_preimage_nbhd_JN74 c (hK.inter_right (hLc c).isClosed)
      (inter_subset_right.trans (hLN c))

end CircleBundle

section CircleFacts

variable (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
  (P : EdgeBundle W) (R : CircleBundle W) (hP : P.cbase.Nonempty) (K₃ D₃ : Set Sl.Base)
  (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
  (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
  (hfaces : Disjoint (frontier K₃) Sl.facePoints)

/-- **The cut-dependent circle facts of the whole-base cut of an existing circle bundle**: the
saturation `M₃ = circleRegion` is the only input (it is a statement about the cut, not about the
bundle). -/
def circleCutFacts_ofBundles74
    (hsat : (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).M₃ =
      (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).circleRegion) :
    CircleCutFacts74 (SmoothStageGeometry74.ofBundles74 Z C Sl P R)
      (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces) where
  neighborhood c := R.stageNeighborhood_JN74 ⊤ c
  mem_neighborhood c := R.mem_stageNeighborhood_JN74 ⊤ c
  trivialization c := R.stageTrivialization_JN74 ⊤ c
  projection_trivialization c x := R.stageProjection_trivialization_JN74 ⊤ c x
  proper K hK' := by
    have hc : IsCompact (Subtype.val '' K : Set R.Base) := hK'.image continuous_subtype_val
    have h := R.proj_proper_JN74 hc
    have heq := image_restrictTop_JN74 (StageProj74.ofCircleBundle74 R)
      (fun y => R.proj y ∈ Subtype.val '' K)
    have hset : Subtype.val '' {x : (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃
        hreq hfaces).circleSource |
          ((SmoothStageGeometry74.ofBundles74 Z C Sl P R).circle.restrictProj
          (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).circleBaseOpen)
            x ∈ K} = Subtype.val '' {x : R.domain | R.proj x ∈ Subtype.val '' K} := by
      refine Eq.trans ?_ heq
      congr 1
      ext x
      simp only [mem_ofPred_eq]
      exact (Subtype.val_injective.mem_set_image).symm
    exact Eq.mpr (congrArg IsCompact (by exact hset)) h
  cbase_compact := isCompact_preimage_top_JN74 R.cbase_compact
  saturation := hsat

end CircleFacts

end GC.GraphManifold.Assembly.FC39P0
