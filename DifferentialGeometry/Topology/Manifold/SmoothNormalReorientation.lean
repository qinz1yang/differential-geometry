/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.SmoothNormalAtlas

set_option autoImplicit false

open Filter Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x y z

namespace DifferentialGeometry.Topology

theorem realNormalSide_neg {t : ℝ} (ht : t ≠ 0) :
    realNormalSide (-t) = Bool.xor (realNormalSide t) true := by
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · rw [realNormalSide_eq_true_of_neg htneg,
      realNormalSide_eq_false_of_pos (neg_pos.mpr htneg)]
    decide
  · rw [realNormalSide_eq_false_of_pos htpos,
      realNormalSide_eq_true_of_neg (neg_neg_of_pos htpos)]
    decide

namespace OpenPartialHomeomorph

def normalFlip (X : Type*) [TopologicalSpace X] :
    Bool → OpenPartialHomeomorph (X × ℝ) (X × ℝ)
  | false => OpenPartialHomeomorph.refl _
  | true => ((Homeomorph.refl X).prodCongr (Homeomorph.neg ℝ)).toOpenPartialHomeomorph

@[simp]
theorem normalFlip_apply
    {X : Type*} [TopologicalSpace X] (side : Bool) (q : X × ℝ) :
    normalFlip X side q = (q.1, if side then -q.2 else q.2) := by
  cases side <;> rfl

@[simp]
theorem normalFlip_symm_apply
    {X : Type*} [TopologicalSpace X] (side : Bool) (q : X × ℝ) :
    (normalFlip X side).symm q = normalFlip X side q := by
  cases side <;> rfl

@[simp]
theorem normalFlip_source
    {X : Type*} [TopologicalSpace X] (side : Bool) :
    (normalFlip X side).source = Set.univ := by
  cases side <;> rfl

@[simp]
theorem normalFlip_target
    {X : Type*} [TopologicalSpace X] (side : Bool) :
    (normalFlip X side).target = Set.univ := by
  cases side <;> rfl

theorem normalFlip_apply_zero
    {X : Type*} [TopologicalSpace X] (side : Bool) (x : X) :
    normalFlip X side (x, 0) = (x, 0) := by
  cases side <;> simp

theorem normalFlip_zeroLocus_iff_zero
    {X : Type*} [TopologicalSpace X] (side : Bool) :
    ∀ q ∈ (normalFlip X side).source,
      (normalFlip X side q).2 = 0 ↔ q.2 = 0 := by
  intro q _
  cases side <;> simp

theorem hasNormalSideFlipAt_normalFlip
    {X : Type*} [TopologicalSpace X] (side : Bool) (x : X) :
    HasNormalSideFlipAt (normalFlip X side) x side := by
  filter_upwards [] with q hqne
  refine ⟨by simp, ?_⟩
  cases side with
  | false => simp
  | true => simpa using realNormalSide_neg hqne

theorem hasNormalSideFlipAt_normalFlip_symm
    {X : Type*} [TopologicalSpace X] (side : Bool) (x : X) :
    HasNormalSideFlipAt (normalFlip X side).symm x side := by
  apply hasNormalSideFlipAt_of_eqOn (normalFlip X side) (normalFlip X side).symm
  · change (x, 0) ∈ (normalFlip X side).target
    rw [normalFlip_target]
    exact mem_univ _
  · intro q _ _
    exact (normalFlip_symm_apply side q).symm
  · exact hasNormalSideFlipAt_normalFlip side x

theorem contMDiff_normalFlip
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {B : Type w} [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω) (side : Bool) :
    ContMDiff (I.prod (modelWithCornersSelf ℝ ℝ))
      (I.prod (modelWithCornersSelf ℝ ℝ)) n
      (normalFlip B side) := by
  cases side with
  | false =>
      change ContMDiff (I.prod (modelWithCornersSelf ℝ ℝ))
        (I.prod (modelWithCornersSelf ℝ ℝ)) n (fun q : B × ℝ ↦ q)
      exact contMDiff_id
  | true =>
      change ContMDiff (I.prod (modelWithCornersSelf ℝ ℝ))
        (I.prod (modelWithCornersSelf ℝ ℝ)) n
        (fun q : B × ℝ ↦ (q.1, -q.2))
      exact (contMDiff_fst (I := I) (J := modelWithCornersSelf ℝ ℝ)).prodMk
        (contMDiff_snd (I := I) (J := modelWithCornersSelf ℝ ℝ)).neg

end OpenPartialHomeomorph

namespace EmbeddingRealNormalAtlas

variable {B : Type u} {A : Type v} [TopologicalSpace B] [TopologicalSpace A]
  {f : B → A}

abbrev Coorientation (C : EmbeddingRealNormalAtlas f) := C.toBoolCocycle.Coorientation

namespace Coorientation

variable {C : EmbeddingRealNormalAtlas f} (O : C.Coorientation)

def centerSide (i : B) : Bool :=
  O.coord i ⟨i, C.mem_baseSet_self i⟩

def baseSet (i : B) : Set B :=
  Subtype.val '' {y : C.baseSet i | O.coord i y = O.centerSide i}

theorem isOpen_baseSet (i : B) : IsOpen (O.baseSet i) := by
  apply (C.isOpen_baseSet i).isOpenMap_subtype_val
  exact ((IsLocallyConstant.iff_continuous _).2 (O.coord i).continuous).isOpen_fiber _

theorem mem_baseSet_self (i : B) : i ∈ O.baseSet i := by
  exact ⟨⟨i, C.mem_baseSet_self i⟩, rfl, rfl⟩

theorem mem_original_baseSet {i x : B} (hx : x ∈ O.baseSet i) :
    x ∈ C.baseSet i := by
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

theorem coord_eq_centerSide {i x : B} (hx : x ∈ O.baseSet i) :
    O.coord i ⟨x, O.mem_original_baseSet hx⟩ = O.centerSide i := by
  obtain ⟨y, hy, hxy⟩ := hx
  subst x
  exact hy

def reorientedAtlas : EmbeddingRealNormalAtlas f where
  baseSet := O.baseSet
  isOpen_baseSet := O.isOpen_baseSet
  mem_baseSet_self := O.mem_baseSet_self
  chart i := (OpenPartialHomeomorph.normalFlip B (O.centerSide i)).trans (C.chart i)
  zero_mem_source i _y hy := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by simp, ?_⟩
    simpa using C.zero_mem_source i (O.mem_original_baseSet hy)
  apply_zero i _y hy := by
    change C.chart i
      (OpenPartialHomeomorph.normalFlip B (O.centerSide i) (_y, 0)) = f _y
    rw [OpenPartialHomeomorph.normalFlip_apply_zero]
    exact C.apply_zero i (O.mem_original_baseSet hy)
  range_iff_zero i q hq := by
    rw [OpenPartialHomeomorph.trans_source] at hq
    change C.chart i (OpenPartialHomeomorph.normalFlip B (O.centerSide i) q) ∈
        Set.range f ↔ q.2 = 0
    rw [C.range_iff_zero i _ hq.2]
    cases O.centerSide i <;> simp

theorem reorientedAtlas_transitionParity_eq_false
    {i j x : B} (hxi : x ∈ O.baseSet i) (hxj : x ∈ O.baseSet j) :
    O.reorientedAtlas.transitionParity i j x = false := by
  let si := O.centerSide i
  let sj := O.centerSide j
  let Ri := OpenPartialHomeomorph.normalFlip B si
  let Rj := OpenPartialHomeomorph.normalFlip B sj
  let e := C.transition i j
  let composite := (Ri.trans e).trans Rj.symm
  have hxiOld : x ∈ C.baseSet i := O.mem_original_baseSet hxi
  have hxjOld : x ∈ C.baseSet j := O.mem_original_baseSet hxj
  have hoverlap : x ∈ C.baseSet i ∩ C.baseSet j := ⟨hxiOld, hxjOld⟩
  have heFlip : HasNormalSideFlipAt e x (C.transitionParity i j x) := by
    rw [C.transitionParity_eq_normalSideFlipAt hoverlap]
    exact OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt e
      (C.transition_zeroLocus_iff_zero i j) (C.transitionZeroPoint i j ⟨x, hoverlap⟩)
  have hRiFlip : HasNormalSideFlipAt Ri x si := by
    exact OpenPartialHomeomorph.hasNormalSideFlipAt_normalFlip si x
  have hfirstFlip : HasNormalSideFlipAt (Ri.trans e) x
      (Bool.xor si (C.transitionParity i j x)) := by
    apply OpenPartialHomeomorph.hasNormalSideFlipAt_trans Ri e
    · simp [Ri]
    · exact OpenPartialHomeomorph.normalFlip_zeroLocus_iff_zero si
    · exact hRiFlip
    · simpa [Ri, e] using heFlip
  have hxfirst : (x, 0) ∈ (Ri.trans e).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by simp [Ri], ?_⟩
    simpa [Ri, e] using C.zero_mem_transition_source hxiOld hxjOld
  have hfirstZero : ∀ q ∈ (Ri.trans e).source,
      ((Ri.trans e) q).2 = 0 ↔ q.2 = 0 :=
    OpenPartialHomeomorph.zeroLocus_iff_zero_trans Ri e
      (OpenPartialHomeomorph.normalFlip_zeroLocus_iff_zero si)
      (C.transition_zeroLocus_iff_zero i j)
  have hRjFlip : HasNormalSideFlipAt Rj.symm ((Ri.trans e (x, 0)).1) sj := by
    have h := OpenPartialHomeomorph.hasNormalSideFlipAt_normalFlip_symm sj x
    simpa [Ri, e, Rj, OpenPartialHomeomorph.trans_apply,
      C.transition_apply_zero hxiOld hxjOld] using h
  have hcompositeFlip : HasNormalSideFlipAt composite x
      (Bool.xor (Bool.xor si (C.transitionParity i j x)) sj) := by
    exact OpenPartialHomeomorph.hasNormalSideFlipAt_trans (Ri.trans e) Rj.symm
      hxfirst hfirstZero hfirstFlip hRjFlip
  have hbool : Bool.xor (Bool.xor si (C.transitionParity i j x)) sj = false := by
    dsimp [si, sj]
    rw [← O.coord_eq_centerSide hxi, ← O.coord_eq_centerSide hxj]
    rw [O.coord_change i j x hxiOld hxjOld]
    exact Bool.xor_self _
  have hcompositeFalse : HasNormalSideFlipAt composite x false := by
    rw [← hbool]
    exact hcompositeFlip
  have hnewSource : (x, 0) ∈ (O.reorientedAtlas.transition i j).source :=
    O.reorientedAtlas.zero_mem_transition_source hxi hxj
  have hnewFlip : HasNormalSideFlipAt (O.reorientedAtlas.transition i j) x false := by
    apply OpenPartialHomeomorph.hasNormalSideFlipAt_of_eqOn composite
      (O.reorientedAtlas.transition i j) hnewSource
    · intro q _ _
      change Rj.symm (C.chart j |>.symm (C.chart i (Ri q))) =
        Rj.symm (C.chart j |>.symm (C.chart i (Ri q)))
      rfl
    · exact hcompositeFalse
  rw [O.reorientedAtlas.transitionParity_eq_normalSideFlipAt ⟨hxi, hxj⟩]
  have hcanonical := OpenPartialHomeomorph.hasNormalSideFlipAt_normalSideFlipAt
    (O.reorientedAtlas.transition i j)
    (O.reorientedAtlas.transition_zeroLocus_iff_zero i j)
    (O.reorientedAtlas.transitionZeroPoint i j ⟨x, ⟨hxi, hxj⟩⟩)
  exact (OpenPartialHomeomorph.existsUnique_hasNormalSideFlipAt
    (O.reorientedAtlas.transition i j) hnewSource
    (O.reorientedAtlas.transition_zeroLocus_iff_zero i j)).unique hcanonical hnewFlip

end Coorientation
end EmbeddingRealNormalAtlas

structure CoorientedSmoothEmbeddingRealNormalAtlas
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    (n : ℕ∞ω) (f : B → A) extends SmoothEmbeddingRealNormalAtlas I J n f where
  transitionParity_eq_false : ∀ i j x,
    x ∈ toEmbeddingRealNormalAtlas.baseSet i →
    x ∈ toEmbeddingRealNormalAtlas.baseSet j →
    toEmbeddingRealNormalAtlas.transitionParity i j x = false

namespace SmoothEmbeddingRealNormalAtlas

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {f : B → A}
    (C : SmoothEmbeddingRealNormalAtlas I J n f)

def reorientedAtlas
    (O : C.toEmbeddingRealNormalAtlas.Coorientation) :
    SmoothEmbeddingRealNormalAtlas I J n f where
  toEmbeddingRealNormalAtlas := O.reorientedAtlas
  contMDiffOn_chart i := by
    rw [EmbeddingRealNormalAtlas.Coorientation.reorientedAtlas,
      OpenPartialHomeomorph.trans_source]
    exact (C.contMDiffOn_chart i).comp
      (OpenPartialHomeomorph.contMDiff_normalFlip I n (O.centerSide i)).contMDiffOn
      inter_subset_right
  contMDiffOn_chart_symm i := by
    have hflip : ContMDiffOn (I.prod (modelWithCornersSelf ℝ ℝ))
        (I.prod (modelWithCornersSelf ℝ ℝ)) n
        (OpenPartialHomeomorph.normalFlip B (O.centerSide i)).symm
        (OpenPartialHomeomorph.normalFlip B (O.centerSide i)).target := by
      rw [OpenPartialHomeomorph.normalFlip_target]
      intro q _
      exact ((OpenPartialHomeomorph.contMDiff_normalFlip (B := B) I n
        (O.centerSide i)).contMDiffAt.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y ↦
            OpenPartialHomeomorph.normalFlip_symm_apply (O.centerSide i) y)).contMDiffWithinAt
    change ContMDiffOn J (I.prod (modelWithCornersSelf ℝ ℝ)) n
      ((C.toEmbeddingRealNormalAtlas.chart i).symm.trans
        (OpenPartialHomeomorph.normalFlip B (O.centerSide i)).symm)
      ((C.toEmbeddingRealNormalAtlas.chart i).target ∩
        (C.toEmbeddingRealNormalAtlas.chart i).symm ⁻¹'
          (OpenPartialHomeomorph.normalFlip B (O.centerSide i)).target)
    exact hflip.comp ((C.contMDiffOn_chart_symm i).mono inter_subset_left) inter_subset_right

def coorientedAtlas
    (O : C.toEmbeddingRealNormalAtlas.Coorientation) :
    CoorientedSmoothEmbeddingRealNormalAtlas I J n f where
  toSmoothEmbeddingRealNormalAtlas := C.reorientedAtlas O
  transitionParity_eq_false _i _j _x hxi hxj :=
    O.reorientedAtlas_transitionParity_eq_false hxi hxj

theorem nonempty_coorientedAtlas
    (C : SmoothEmbeddingRealNormalAtlas I J n f)
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (b₀ : B) (side₀ : Bool) :
    Nonempty (CoorientedSmoothEmbeddingRealNormalAtlas I J n f) := by
  obtain ⟨O⟩ := BoolCocycle.nonempty_coorientation
    (C.toEmbeddingRealNormalAtlas).toBoolCocycle b₀ side₀
  exact ⟨coorientedAtlas C O⟩

end SmoothEmbeddingRealNormalAtlas

namespace CoorientedSmoothEmbeddingRealNormalAtlas

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {B : Type y} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type z} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {f : B → A}
    (C : CoorientedSmoothEmbeddingRealNormalAtlas I J n f)

theorem normalDeriv_transition_pos
    (hn : (1 : ℕ∞ω) ≤ n)
    {i j x : B}
    (hxi : x ∈ C.toEmbeddingRealNormalAtlas.baseSet i)
    (hxj : x ∈ C.toEmbeddingRealNormalAtlas.baseSet j) :
    0 < OpenPartialHomeomorph.normalDeriv
      (C.toEmbeddingRealNormalAtlas.transition i j) x :=
  C.toSmoothEmbeddingRealNormalAtlas.normalDeriv_transition_pos_of_transitionParity_eq_false
    hn hxi hxj (C.transitionParity_eq_false i j x hxi hxj)

end CoorientedSmoothEmbeddingRealNormalAtlas

theorem nonempty_coorientedSmoothSphereEmbeddingRealNormalAtlas
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {n : ℕ∞ω} {e : SphereTwo → N}
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e) :
    Nonempty (CoorientedSmoothEmbeddingRealNormalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e) := by
  let _ : LocallyPathConnectedSpace SphereTwo :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) SphereTwo
  exact SmoothEmbeddingRealNormalAtlas.nonempty_coorientedAtlas
    (C := smoothSphereEmbeddingRealNormalAtlas he)
    (b₀ := Classical.arbitrary SphereTwo) (side₀ := false)

end DifferentialGeometry.Topology
