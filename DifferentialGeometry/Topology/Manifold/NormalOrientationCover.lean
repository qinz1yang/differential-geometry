/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Covering.BoolCocycle
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Manifold.CodimensionOneImmersion
import DifferentialGeometry.Topology.Manifold.NormalOrientation

set_option autoImplicit false

open Filter Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x

namespace DifferentialGeometry.Topology

structure EmbeddingRealNormalAtlas
    {B : Type u} {A : Type v} [TopologicalSpace B] [TopologicalSpace A] (f : B → A) where
  baseSet : B → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  mem_baseSet_self : ∀ i, i ∈ baseSet i
  chart : B → OpenPartialHomeomorph (B × ℝ) A
  zero_mem_source : ∀ i, ∀ {y}, y ∈ baseSet i → (y, 0) ∈ (chart i).source
  apply_zero : ∀ i, ∀ {y}, y ∈ baseSet i → chart i (y, 0) = f y
  range_iff_zero : ∀ i, ∀ q ∈ (chart i).source, chart i q ∈ Set.range f ↔ q.2 = 0

namespace EmbeddingRealNormalAtlas

variable {B : Type u} {A : Type v} [TopologicalSpace B] [TopologicalSpace A]
  {f : B → A} (C : EmbeddingRealNormalAtlas f)

def transition (i j : B) : OpenPartialHomeomorph (B × ℝ) (B × ℝ) :=
  (C.chart i).trans (C.chart j).symm

theorem zero_mem_transition_source
    {i j y : B} (hyi : y ∈ C.baseSet i) (hyj : y ∈ C.baseSet j) :
    (y, 0) ∈ (C.transition i j).source := by
  rw [transition, OpenPartialHomeomorph.trans_source]
  refine ⟨C.zero_mem_source i hyi, ?_⟩
  change C.chart i (y, 0) ∈ (C.chart j).target
  rw [C.apply_zero i hyi, ← C.apply_zero j hyj]
  exact (C.chart j).map_source (C.zero_mem_source j hyj)

theorem transition_apply_zero
    {i j y : B} (hyi : y ∈ C.baseSet i) (hyj : y ∈ C.baseSet j) :
    C.transition i j (y, 0) = (y, 0) := by
  change (C.chart j).symm (C.chart i (y, 0)) = (y, 0)
  rw [C.apply_zero i hyi, ← C.apply_zero j hyj]
  exact (C.chart j).left_inv (C.zero_mem_source j hyj)

theorem transition_zeroLocus_iff_zero (i j : B) :
    ∀ q ∈ (C.transition i j).source, (C.transition i j q).2 = 0 ↔ q.2 = 0 := by
  intro q hq
  rw [transition, OpenPartialHomeomorph.trans_source] at hq
  have hrSource : (C.chart j).symm (C.chart i q) ∈ (C.chart j).source :=
    (C.chart j).map_target hq.2
  have hright : C.chart j ((C.chart j).symm (C.chart i q)) = C.chart i q :=
    (C.chart j).right_inv hq.2
  calc
    (C.transition i j q).2 = 0 ↔
        C.chart j ((C.chart j).symm (C.chart i q)) ∈ Set.range f := by
          change ((C.chart j).symm (C.chart i q)).2 = 0 ↔ _
          exact (C.range_iff_zero j _ hrSource).symm
    _ ↔ C.chart i q ∈ Set.range f := by rw [hright]
    _ ↔ q.2 = 0 := C.range_iff_zero i q hq.1

def transitionZeroPoint (i j : B)
    (y : {y : B // y ∈ C.baseSet i ∩ C.baseSet j}) :
    OpenPartialHomeomorph.zeroSectionSource (C.transition i j) :=
  ⟨y.1, C.zero_mem_transition_source y.2.1 y.2.2⟩

noncomputable def transitionParity (i j y : B) : Bool := by
  classical
  exact if hy : y ∈ C.baseSet i ∩ C.baseSet j then
      OpenPartialHomeomorph.normalSideFlipAt (C.transition i j)
        (C.transition_zeroLocus_iff_zero i j) (C.transitionZeroPoint i j ⟨y, hy⟩)
    else false

theorem transitionParity_eq_normalSideFlipAt
    {i j y : B} (hy : y ∈ C.baseSet i ∩ C.baseSet j) :
    C.transitionParity i j y =
      OpenPartialHomeomorph.normalSideFlipAt (C.transition i j)
        (C.transition_zeroLocus_iff_zero i j) (C.transitionZeroPoint i j ⟨y, hy⟩) := by
  simp only [transitionParity, dif_pos hy]

theorem continuousOn_transitionParity (i j : B) :
    ContinuousOn (C.transitionParity i j) (C.baseSet i ∩ C.baseSet j) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let z : {y : B // y ∈ C.baseSet i ∩ C.baseSet j} →
      OpenPartialHomeomorph.zeroSectionSource (C.transition i j) :=
    fun y ↦ C.transitionZeroPoint i j y
  have hz : Continuous z := by
    exact Continuous.subtype_mk continuous_subtype_val _
  have hnormal : Continuous
      (OpenPartialHomeomorph.normalSideFlipAt (C.transition i j)
        (C.transition_zeroLocus_iff_zero i j)) :=
    (OpenPartialHomeomorph.isLocallyConstant_normalSideFlipAt (C.transition i j)
      (C.transition_zeroLocus_iff_zero i j)).continuous
  apply (hnormal.comp hz).congr
  intro y
  simp only [Function.comp_apply, Set.domRestrict_apply, z]
  rw [transitionParity, dif_pos y.2]

theorem hasNormalSideFlipAt_transition_self
    {i y : B} (hy : y ∈ C.baseSet i) :
    HasNormalSideFlipAt (C.transition i i) y false := by
  have hySource : (y, 0) ∈ (C.transition i i).source :=
    C.zero_mem_transition_source hy hy
  apply mem_of_superset ((C.transition i i).open_source.mem_nhds hySource)
  intro q hq _
  refine ⟨hq, ?_⟩
  have hq' := hq
  rw [transition, OpenPartialHomeomorph.trans_source] at hq'
  have hfix : C.transition i i q = q := by
    change (C.chart i).symm (C.chart i q) = q
    exact (C.chart i).left_inv hq'.1
  rw [hfix]
  simp

theorem transitionParity_self
    (i : B) {y : B} (hy : y ∈ C.baseSet i) :
    C.transitionParity i i y = false := by
  rw [C.transitionParity_eq_normalSideFlipAt ⟨hy, hy⟩]
  let p := C.transitionZeroPoint i i ⟨y, ⟨hy, hy⟩⟩
  have hcanonical :=
    OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt (C.transition i i)
      (C.transition_zeroLocus_iff_zero i i) p
  have hfalse := C.hasNormalSideFlipAt_transition_self hy
  exact (OpenPartialHomeomorph.existsUnique_hasNormalSideFlipAt (C.transition i i)
    p.2 (C.transition_zeroLocus_iff_zero i i)).unique hcanonical hfalse

theorem transition_trans_transition_apply
    {i j k : B} {q : B × ℝ}
    (hq : q ∈ ((C.transition i j).trans (C.transition j k)).source) :
    ((C.transition i j).trans (C.transition j k)) q = C.transition i k q := by
  have hqij : q ∈ (C.transition i j).source := by
    rw [OpenPartialHomeomorph.trans_source] at hq
    exact hq.1
  rw [transition, OpenPartialHomeomorph.trans_source] at hqij
  change (C.chart k).symm
      (C.chart j ((C.chart j).symm (C.chart i q))) =
    (C.chart k).symm (C.chart i q)
  rw [(C.chart j).right_inv hqij.2]

theorem transitionParity_comp
    (i j k : B) {y : B}
    (hy : y ∈ C.baseSet i ∩ C.baseSet j ∩ C.baseSet k) :
    Bool.xor (C.transitionParity i j y) (C.transitionParity j k y) =
      C.transitionParity i k y := by
  rcases hy with ⟨⟨hyi, hyj⟩, hyk⟩
  have hyij : y ∈ C.baseSet i ∩ C.baseSet j := ⟨hyi, hyj⟩
  have hyjk : y ∈ C.baseSet j ∩ C.baseSet k := ⟨hyj, hyk⟩
  have hyik : y ∈ C.baseSet i ∩ C.baseSet k := ⟨hyi, hyk⟩
  rw [C.transitionParity_eq_normalSideFlipAt hyij,
    C.transitionParity_eq_normalSideFlipAt hyjk,
    C.transitionParity_eq_normalSideFlipAt hyik]
  let pij := OpenPartialHomeomorph.normalSideFlipAt (C.transition i j)
    (C.transition_zeroLocus_iff_zero i j) (C.transitionZeroPoint i j ⟨y, hyij⟩)
  let pjk := OpenPartialHomeomorph.normalSideFlipAt (C.transition j k)
    (C.transition_zeroLocus_iff_zero j k) (C.transitionZeroPoint j k ⟨y, hyjk⟩)
  have hij := OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt
    (C.transition i j) (C.transition_zeroLocus_iff_zero i j)
    (C.transitionZeroPoint i j ⟨y, hyij⟩)
  have hjk := OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt
    (C.transition j k) (C.transition_zeroLocus_iff_zero j k)
    (C.transitionZeroPoint j k ⟨y, hyjk⟩)
  have hjk' : HasNormalSideFlipAt (C.transition j k)
      ((C.transition i j (y, 0)).1) pjk := by
    rw [C.transition_apply_zero hyi hyj]
    exact hjk
  have hcomp : HasNormalSideFlipAt
      ((C.transition i j).trans (C.transition j k)) y (Bool.xor pij pjk) :=
    OpenPartialHomeomorph.hasNormalSideFlipAt_trans (C.transition i j)
      (C.transition j k) (C.zero_mem_transition_source hyi hyj)
      (C.transition_zeroLocus_iff_zero i j) hij hjk'
  have hikCandidate : HasNormalSideFlipAt (C.transition i k) y (Bool.xor pij pjk) :=
    OpenPartialHomeomorph.hasNormalSideFlipAt_of_eqOn
      ((C.transition i j).trans (C.transition j k)) (C.transition i k)
      (C.zero_mem_transition_source hyi hyk)
      (fun q hq _ ↦ C.transition_trans_transition_apply hq) hcomp
  have hik := OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt
    (C.transition i k) (C.transition_zeroLocus_iff_zero i k)
    (C.transitionZeroPoint i k ⟨y, hyik⟩)
  exact (OpenPartialHomeomorph.existsUnique_hasNormalSideFlipAt (C.transition i k)
    (C.zero_mem_transition_source hyi hyk) (C.transition_zeroLocus_iff_zero i k)).unique
      hikCandidate hik

def toBoolCocycle : BoolCocycle B B where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := id
  mem_baseSet_at := C.mem_baseSet_self
  parity := C.transitionParity
  parity_self := C.transitionParity_self
  continuousOn_parity := C.continuousOn_transitionParity
  parity_comp := C.transitionParity_comp

end EmbeddingRealNormalAtlas

noncomputable def embeddingAdaptedRealNormalChart
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f)
    (i : M) : OpenPartialHomeomorph (M × ℝ) N :=
  Classical.choose (exists_embeddingAdapted_realNormalFormPartialHomeomorph hf (h i))

theorem embeddingAdaptedRealNormalChart_spec
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f)
    (i : M) :
    (∀ {y : M}, y ∈ (h i).domChart.source →
      (y, 0) ∈ (embeddingAdaptedRealNormalChart hf h i).source ∧
        embeddingAdaptedRealNormalChart hf h i (y, 0) = f y) ∧
    ∀ q ∈ (embeddingAdaptedRealNormalChart hf h i).source,
      embeddingAdaptedRealNormalChart hf h i q ∈ Set.range f ↔ q.2 = 0 :=
  (Classical.choose_spec (exists_embeddingAdapted_realNormalFormPartialHomeomorph hf (h i))).1

theorem contMDiffOn_embeddingAdaptedRealNormalChart
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f)
    (i : M) :
    ContMDiffOn
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ E') n
      (embeddingAdaptedRealNormalChart hf h i)
      (embeddingAdaptedRealNormalChart hf h i).source :=
  (Classical.choose_spec (exists_embeddingAdapted_realNormalFormPartialHomeomorph hf (h i))).2.1

theorem contMDiffOn_symm_embeddingAdaptedRealNormalChart
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f)
    (i : M) :
    ContMDiffOn
      (modelWithCornersSelf ℝ E')
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)) n
      (embeddingAdaptedRealNormalChart hf h i).symm
      (embeddingAdaptedRealNormalChart hf h i).target :=
  (Classical.choose_spec (exists_embeddingAdapted_realNormalFormPartialHomeomorph hf (h i))).2.2

noncomputable def embeddingRealNormalAtlasOfIsImmersionOfComplement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f) :
    EmbeddingRealNormalAtlas f where
  baseSet i := (h i).domChart.source
  isOpen_baseSet i := (h i).domChart.open_source
  mem_baseSet_self i := (h i).mem_domChart_source
  chart i := embeddingAdaptedRealNormalChart hf h i
  zero_mem_source i _y hy := (embeddingAdaptedRealNormalChart_spec hf h i).1 hy |>.1
  apply_zero i _y hy := (embeddingAdaptedRealNormalChart_spec hf h i).1 hy |>.2
  range_iff_zero i q hq := (embeddingAdaptedRealNormalChart_spec hf h i).2 q hq

noncomputable def normalOrientationBoolCocycle
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f) :
    BoolCocycle M M :=
  (embeddingRealNormalAtlasOfIsImmersionOfComplement hf h).toBoolCocycle

theorem isCoveringMap_normalOrientation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f) :
    IsCoveringMap (normalOrientationBoolCocycle hf h).toFiberBundleCore.proj :=
  (normalOrientationBoolCocycle hf h).isCoveringMap_proj

theorem exists_continuous_section_normalOrientation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsEmbedding f)
    (h : IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f)
    (x₀ : M) (side₀ : Bool) :
    ∃ s : C(M, (normalOrientationBoolCocycle hf h).toFiberBundleCore.TotalSpace),
      Function.RightInverse s (normalOrientationBoolCocycle hf h).toFiberBundleCore.proj :=
  (normalOrientationBoolCocycle hf h).exists_continuous_section x₀ side₀

noncomputable def smoothSphereNormalOrientationBoolCocycle
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {n : ℕ∞ω} {e : SphereTwo → N}
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e) :
    BoolCocycle SphereTwo SphereTwo :=
  normalOrientationBoolCocycle he.isEmbedding
    (isImmersionOfComplement_real_of_isSmoothEmbedding_sphereTwo he)

theorem isCoveringMap_smoothSphereNormalOrientation
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {n : ℕ∞ω} {e : SphereTwo → N}
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e) :
    IsCoveringMap (smoothSphereNormalOrientationBoolCocycle he).toFiberBundleCore.proj :=
  (smoothSphereNormalOrientationBoolCocycle he).isCoveringMap_proj

theorem exists_continuous_section_smoothSphereNormalOrientation
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {n : ℕ∞ω} {e : SphereTwo → N}
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e)
    (x₀ : SphereTwo) (side₀ : Bool) :
    ∃ s : C(SphereTwo,
        (smoothSphereNormalOrientationBoolCocycle he).toFiberBundleCore.TotalSpace),
      Function.RightInverse s
        (smoothSphereNormalOrientationBoolCocycle he).toFiberBundleCore.proj := by
  let _ : LocallyPathConnectedSpace SphereTwo :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) SphereTwo
  exact (smoothSphereNormalOrientationBoolCocycle he).exists_continuous_section x₀ side₀

end DifferentialGeometry.Topology
