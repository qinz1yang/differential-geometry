import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundles74

/-!
# Draft 74, G5 step 2: the cut-dependent edge facts over `⊤` from an existing edge bundle

Lane S-JUNCTIONS2 (suffix `_JN74`). `edgeCutFacts_ofBundles74`: for the stage geometry and cut
choice of `FC39StageOfBundles74` the facts `EdgeCutFacts74` (rank two, properness, whole smooth
disks, compact base, regular boundary function of the base) are the fields of `P : EdgeBundle W`
carried over the identification of the restricted stage over `⊤` with the stage. Generic helper
lemmas: the differential of the restricted projection / of a function composed with the inclusion
of the restricted parent, and the image identity `image_restrictTop_JN74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsEdgeBundlesJN74 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- The differential of the restricted projection is the differential of the projection. -/
theorem mfderiv_restrictProj_apply_JN74 {k : ℕ} (Q : StageProj74 W k)
    (V : TopologicalSpace.Opens Q.Base) (x : Q.restrictParent V)
    (v : TangentSpace W.model (x : W.Carrier)) :
    mfderiv W.model (𝓡 k) (Q.restrictProj V) x v =
      mfderiv W.model (𝓡 k) Q.proj (Q.restrictIncl V x) v := by
  have h1 := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := W.model) (J := 𝓡 k) V
    (Q.restrictProj V) x
  have hid : mfderiv W.model W.model (Q.restrictIncl V) x = ContinuousLinearMap.id ℝ _ :=
    DifferentialGeometry.mfderiv_opens_incl (Q.restrictParent_le V) x
  have h2 : mfderiv W.model (𝓡 k) (Q.proj ∘ Q.restrictIncl V) x =
      (mfderiv W.model (𝓡 k) Q.proj (Q.restrictIncl V x)).comp
        (mfderiv W.model W.model (Q.restrictIncl V) x) :=
    mfderiv_comp x (Q.proj_smooth.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (n := ∞) (Q.restrictParent_le V)).mdifferentiableAt (by simp))
  rw [hid] at h2
  exact (congrArg (fun L => L v) h1).symm.trans (congrArg (fun L => L v) h2)

/-- The differential of a smooth function of the parent composed with the inclusion of the
restricted parent. -/
theorem mfderiv_comp_restrictIncl_apply_JN74 {k : ℕ} (Q : StageProj74 W k)
    (V : TopologicalSpace.Opens Q.Base) {f : Q.parent → ℝ}
    (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f) (x : Q.restrictParent V)
    (v : TangentSpace W.model (x : W.Carrier)) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y : Q.restrictParent V => f (Q.restrictIncl V y)) x v =
      mfderiv W.model 𝓘(ℝ, ℝ) f (Q.restrictIncl V x) v := by
  have hid : mfderiv W.model W.model (Q.restrictIncl V) x = ContinuousLinearMap.id ℝ _ :=
    DifferentialGeometry.mfderiv_opens_incl (Q.restrictParent_le V) x
  have h2 : mfderiv W.model 𝓘(ℝ, ℝ) (f ∘ Q.restrictIncl V) x =
      (mfderiv W.model 𝓘(ℝ, ℝ) f (Q.restrictIncl V x)).comp
        (mfderiv W.model W.model (Q.restrictIncl V) x) :=
    mfderiv_comp x (hf.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (n := ∞) (Q.restrictParent_le V)).mdifferentiableAt (by simp))
  rw [hid] at h2
  exact congrArg (fun L => L v) h2

/-- Over `⊤` the image of a predicate on the restricted parent is the image of the predicate on
the parent. -/
theorem image_restrictTop_JN74 {k : ℕ} (Q : StageProj74 W k) (Pr : Q.parent → Prop) :
    Subtype.val '' {x : Q.restrictParent ⊤ | Pr (Q.restrictIncl ⊤ x)} =
      Subtype.val '' {y : Q.parent | Pr y} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Q.restrictIncl ⊤ x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, Q.mem_restrictParent_of y.2 (TopologicalSpace.Opens.mem_top _)⟩, hy, rfl⟩

/-! ## Generic facts about the whole open base `⊤` -/

section Top

variable {B : Type u} [TopologicalSpace B]

/-- A compact set of `B` pulled back to the whole open base `⊤` is compact. -/
theorem isCompact_preimage_top_JN74 {C : Set B} (hC : IsCompact C) :
    IsCompact (Subtype.val ⁻¹' C : Set (⊤ : TopologicalSpace.Opens B)) := by
  refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset]
  · exact hC
  · exact fun c _ => ⟨⟨c, TopologicalSpace.Opens.mem_top c⟩, rfl⟩

variable [ChartedSpace (EuclideanSpace ℝ (Fin 1)) B]

/-- The regular boundary function of a compact base (`cbase_domain`) over the whole open base. -/
theorem cbaseDomain_top_JN74 (C : Set B)
    (h : ∀ c ∈ frontier C, ∃ U : TopologicalSpace.Opens B, c ∈ U ∧
      ∃ φ : B → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧ C ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'}) :
    ∀ c ∈ frontier (Subtype.val ⁻¹' C : Set (⊤ : TopologicalSpace.Opens B)),
      ∃ U : TopologicalSpace.Opens (⊤ : TopologicalSpace.Opens B), c ∈ U ∧
        ∃ φ : (⊤ : TopologicalSpace.Opens B) → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
          mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
          (Subtype.val ⁻¹' C : Set (⊤ : TopologicalSpace.Opens B)) ∩ U =
            {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  intro c hc
  have hopen : IsOpenMap (Subtype.val : (⊤ : TopologicalSpace.Opens B) → B) :=
    (⊤ : TopologicalSpace.Opens B).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hfr : c.1 ∈ frontier C := by
    have h' := hopen.preimage_frontier_eq_frontier_preimage continuous_subtype_val C
    exact (h' ▸ hc : c ∈ Subtype.val ⁻¹' frontier C)
  obtain ⟨U, hcU, φ, hφ, hφ0, hφd, hφeq⟩ := h c.1 hfr
  refine ⟨⟨Subtype.val ⁻¹' (U : Set B), U.isOpen.preimage continuous_subtype_val⟩, hcU,
    fun c' => φ c'.1, ?_, hφ0, ?_, ?_⟩
  · exact hφ.comp contMDiff_subtype_val.contMDiffOn (fun c' hc' => hc')
  · rw [DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) φ ⊤ c]
    exact hφd
  · ext c'
    exact Set.ext_iff.1 hφeq c'.1

end Top

section EdgeFacts

variable (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
  (P : EdgeBundle W) (R : CircleBundle W) (hP : P.cbase.Nonempty) (K₃ D₃ : Set Sl.Base)
  (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
  (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
  (hfaces : Disjoint (frontier K₃) Sl.facePoints)

/-- **The cut-dependent edge facts of the whole-base cut of an existing edge bundle.** -/
theorem edgeCutFacts_ofBundles74 :
    EdgeCutFacts74 (SmoothStageGeometry74.ofBundles74 Z C Sl P R)
      (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces) where
  rank_two x hx := by
    intro uc
    obtain ⟨v, hv⟩ := P.rank_two (EdgeStage74.ofBundle74 P |>.restrictIncl ⊤ x) hx uc
    refine ⟨v, ?_⟩
    rw [← hv]
    refine Prod.ext ?_ ?_
    · exact mfderiv_restrictProj_apply_JN74 (EdgeStage74.ofBundle74 P).toStageProj74 ⊤ x v
    · exact mfderiv_comp_restrictIncl_apply_JN74 (EdgeStage74.ofBundle74 P).toStageProj74 ⊤
        P.height_smooth x v
  proper K hK' := by
    have hc : IsCompact (Subtype.val '' K : Set P.Base) := hK'.image continuous_subtype_val
    have h := P.proper _ hc
    have heq := image_restrictTop_JN74 (EdgeStage74.ofBundle74 P).toStageProj74
      (fun y => P.proj y ∈ Subtype.val '' K ∧ P.height y ≤ P.level)
    have hset : Subtype.val '' {x : (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃
        hreq hfaces).edgeSource | ((SmoothStageGeometry74.ofBundles74 Z C Sl P R).edge.restrictProj
          (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).edgeBaseOpen)
            x ∈ K ∧ (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq
              hfaces).edgeHeight x ≤ P.level} =
        Subtype.val '' {x : P.source | P.proj x ∈ Subtype.val '' K ∧ P.height x ≤ P.level} := by
      refine Eq.trans ?_ heq
      congr 1
      ext x
      exact and_congr (Subtype.val_injective.mem_set_image).symm Iff.rfl
    exact Eq.mpr (congrArg IsCompact hset) h
  fibre_disk c := by
    obtain ⟨φ, hφ, hrange⟩ := P.fibre_disk c.1
    refine ⟨φ, hφ, ?_⟩
    rw [hrange]
    have heq := image_restrictTop_JN74 (EdgeStage74.ofBundle74 P).toStageProj74
      (fun y => P.proj y = c.1 ∧ P.height y ≤ P.level)
    refine heq.symm.trans ?_
    congr 1
    ext x
    exact and_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩ Iff.rfl
  cbase_compact := isCompact_preimage_top_JN74 P.cbase_compact
  cbase_domain := cbaseDomain_top_JN74 P.cbase P.cbase_domain

end EdgeFacts

end GC.GraphManifold.Assembly.FC39P0
