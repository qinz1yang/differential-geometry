/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.UnitInterval
import DifferentialGeometry.Topology.VanKampen.CellAttachment

set_option autoImplicit false

open Set Topology
open scoped ContinuousMap unitInterval

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.CellAttachment


abbrev ConnectedSumNeckCylinder :=
  CellBoundary 3 × unitInterval


def connectedSumNeckBoundaryInclusion :
    CellBoundary 3 ⊕ CellBoundary 3 → ConnectedSumNeckCylinder
  | Sum.inl b => (b, 0)
  | Sum.inr b => (b, 1)


theorem continuous_connectedSumNeckBoundaryInclusion :
    Continuous connectedSumNeckBoundaryInclusion := by
  rw [continuous_sum_dom]
  constructor
  · change Continuous fun b : CellBoundary 3 => (b, (0 : unitInterval))
    exact continuous_id.prodMk continuous_const
  · change Continuous fun b : CellBoundary 3 => (b, (1 : unitInterval))
    exact continuous_id.prodMk continuous_const


def connectedSumNeckAttachingMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    CellBoundary 3 ⊕ CellBoundary 3 → K ⊕ L
  | Sum.inl b => Sum.inl (leftBoundary b)
  | Sum.inr b => Sum.inr (rightBoundary (glue b))


theorem continuous_connectedSumNeckAttachingMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    {leftBoundary : CellBoundary 3 → K} {rightBoundary : CellBoundary 3 → L}
    (hleft : Continuous leftBoundary) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) := by
  rw [continuous_sum_dom]
  constructor
  · simpa [Function.comp_def, connectedSumNeckAttachingMap] using
      continuous_inl.comp hleft
  · simpa [Function.comp_def, connectedSumNeckAttachingMap] using
      continuous_inr.comp (hright.comp glue.continuous)

abbrev ConnectedSumNeck
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :=
  AdjunctionSpace connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)


def connectedSumNeckLeftInclusion
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    K → ConnectedSumNeck leftBoundary rightBoundary glue :=
  adjunctionLower
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) ∘ Sum.inl


def connectedSumNeckRightInclusion
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    L → ConnectedSumNeck leftBoundary rightBoundary glue :=
  adjunctionLower
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) ∘ Sum.inr


theorem continuous_connectedSumNeckLeftInclusion
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckLeftInclusion leftBoundary rightBoundary glue) :=
  (continuous_adjunctionLower connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp continuous_inl


theorem continuous_connectedSumNeckRightInclusion
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckRightInclusion leftBoundary rightBoundary glue) :=
  (continuous_adjunctionLower connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp continuous_inr


theorem connectedSumNeckLeftInclusion_boundary
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (b : CellBoundary 3) :
    connectedSumNeckLeftInclusion leftBoundary rightBoundary glue (leftBoundary b) =
      adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (b, 0) :=
  (adjunction_coherence connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (Sum.inl b)).symm


theorem connectedSumNeckRightInclusion_boundary
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (b : CellBoundary 3) :
    connectedSumNeckRightInclusion leftBoundary rightBoundary glue (rightBoundary (glue b)) =
      adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (b, 1) :=
  (adjunction_coherence connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (Sum.inr b)).symm


def connectedSumNeckLeftRaw {K L : Type u} :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) → Prop
  | Sum.inl p => (p.2 : ℝ) < 2 / 3
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False


def connectedSumNeckRightRaw {K L : Type u} :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) → Prop
  | Sum.inl p => 1 / 3 < (p.2 : ℝ)
  | Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr _) => True

theorem connectedSumNeckLeftRaw_eq_of_rel
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (a b : ConnectedSumNeckCylinder ⊕ (K ⊕ L))
    (hab : adjunctionRel connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) a b) :
    connectedSumNeckLeftRaw a = connectedSumNeckLeftRaw b := by
  rcases hab with ⟨s, hs | hs⟩
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x => simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckLeftRaw]
    | inr x =>
      simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckLeftRaw]
      norm_num
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x => simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckLeftRaw]
    | inr x =>
      simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckLeftRaw]
      norm_num

theorem connectedSumNeckRightRaw_eq_of_rel
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (a b : ConnectedSumNeckCylinder ⊕ (K ⊕ L))
    (hab : adjunctionRel connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) a b) :
    connectedSumNeckRightRaw a = connectedSumNeckRightRaw b := by
  rcases hab with ⟨s, hs | hs⟩
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x => simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckRightRaw]
    | inr x =>
      simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckRightRaw]
      norm_num
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x => simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckRightRaw]
    | inr x =>
      simp [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap, connectedSumNeckRightRaw]
      norm_num


def connectedSumNeckLeft
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Set (ConnectedSumNeck leftBoundary rightBoundary glue) :=
  fun z => Quot.lift connectedSumNeckLeftRaw
    (connectedSumNeckLeftRaw_eq_of_rel leftBoundary rightBoundary glue) z


def connectedSumNeckRight
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Set (ConnectedSumNeck leftBoundary rightBoundary glue) :=
  fun z => Quot.lift connectedSumNeckRightRaw
    (connectedSumNeckRightRaw_eq_of_rel leftBoundary rightBoundary glue) z

@[simp]
theorem adjunctionMk_mem_connectedSumNeckLeft
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (x : ConnectedSumNeckCylinder ⊕ (K ⊕ L)) :
    adjunctionMk connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) x ∈
      connectedSumNeckLeft leftBoundary rightBoundary glue ↔
        connectedSumNeckLeftRaw x :=
  Iff.rfl

@[simp]
theorem adjunctionMk_mem_connectedSumNeckRight
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (x : ConnectedSumNeckCylinder ⊕ (K ⊕ L)) :
    adjunctionMk connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) x ∈
      connectedSumNeckRight leftBoundary rightBoundary glue ↔
        connectedSumNeckRightRaw x :=
  Iff.rfl


theorem isOpen_connectedSumNeckLeft
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    IsOpen (connectedSumNeckLeft leftBoundary rightBoundary glue) := by
  rw [← (isQuotientMap_adjunctionMk connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).isCoinducing.isOpen_preimage]
  change IsOpen {x | connectedSumNeckLeftRaw x}
  rw [isOpen_sum_iff]
  constructor
  · change IsOpen {p : ConnectedSumNeckCylinder | (p.2 : ℝ) < 2 / 3}
    exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  · change IsOpen {x : K ⊕ L | connectedSumNeckLeftRaw (Sum.inr x)}
    rw [isOpen_sum_iff]
    exact ⟨isOpen_univ, isOpen_empty⟩


theorem isOpen_connectedSumNeckRight
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    IsOpen (connectedSumNeckRight leftBoundary rightBoundary glue) := by
  rw [← (isQuotientMap_adjunctionMk connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).isCoinducing.isOpen_preimage]
  change IsOpen {x | connectedSumNeckRightRaw x}
  rw [isOpen_sum_iff]
  constructor
  · change IsOpen {p : ConnectedSumNeckCylinder | 1 / 3 < (p.2 : ℝ)}
    exact isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
  · change IsOpen {x : K ⊕ L | connectedSumNeckRightRaw (Sum.inr x)}
    rw [isOpen_sum_iff]
    exact ⟨isOpen_empty, isOpen_univ⟩


theorem connectedSumNeckLeft_union_right
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    connectedSumNeckLeft leftBoundary rightBoundary glue ∪
        connectedSumNeckRight leftBoundary rightBoundary glue = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  change Quot.lift connectedSumNeckLeftRaw
      (connectedSumNeckLeftRaw_eq_of_rel leftBoundary rightBoundary glue) z ∨
    Quot.lift connectedSumNeckRightRaw
      (connectedSumNeckRightRaw_eq_of_rel leftBoundary rightBoundary glue) z
  refine Quot.inductionOn z ?_
  intro x
  change connectedSumNeckLeftRaw x ∨ connectedSumNeckRightRaw x
  rcases x with p | (k | l)
  · change (p.2 : ℝ) < 2 / 3 ∨ 1 / 3 < (p.2 : ℝ)
    by_cases hp : (p.2 : ℝ) < 2 / 3
    · exact Or.inl hp
    · right
      have : 1 / 3 < (2 / 3 : ℝ) := by norm_num
      exact this.trans_le (le_of_not_gt hp)
  · exact Or.inl trivial
  · exact Or.inr trivial


noncomputable def connectedSumNeckMidpoint
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (b : CellBoundary 3) :
    ConnectedSumNeck leftBoundary rightBoundary glue :=
  adjunctionCell connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
    (b, ⟨1 / 2, by constructor <;> norm_num⟩)


theorem connectedSumNeckMidpoint_mem_inter
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    connectedSumNeckMidpoint leftBoundary rightBoundary glue b ∈
      connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue := by
  constructor
  · change (1 / 2 : ℝ) < 2 / 3
    norm_num
  · change (1 / 3 : ℝ) < 1 / 2
    norm_num


abbrev ConnectedSumNeckMiddle :=
  CellBoundary 3 × Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)


def connectedSumNeckMiddleCylinderInclusion :
    ConnectedSumNeckMiddle → ConnectedSumNeckCylinder :=
  fun p => (p.1, ⟨p.2, by
    constructor
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 3) p.2.2.1.le
    · exact le_trans p.2.2.2.le (by norm_num : (2 / 3 : ℝ) ≤ 1)⟩)


theorem injective_connectedSumNeckMiddleCylinderInclusion :
    Function.Injective connectedSumNeckMiddleCylinderInclusion := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun z : ConnectedSumNeckCylinder => z.1) hpq
  · apply Subtype.ext
    exact congrArg (fun z : ConnectedSumNeckCylinder => ((z.2 : unitInterval) : ℝ)) hpq


def connectedSumNeckMiddleMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckMiddle → ConnectedSumNeck leftBoundary rightBoundary glue :=
  adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) ∘
    connectedSumNeckMiddleCylinderInclusion


theorem continuous_connectedSumNeckMiddleMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckMiddleMap leftBoundary rightBoundary glue) := by
  apply (continuous_adjunctionCell connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp
  exact continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

noncomputable def connectedSumNeckMiddleRawProjection {K L : Type u} :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) → Option ConnectedSumNeckCylinder
  | Sum.inl p =>
      if 1 / 3 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 2 / 3 then
        some p
      else none
  | Sum.inr _ => none

theorem connectedSumNeckMiddleRawProjection_eq_of_rel
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (a b : ConnectedSumNeckCylinder ⊕ (K ⊕ L))
    (hab : adjunctionRel connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) a b) :
    connectedSumNeckMiddleRawProjection a =
      connectedSumNeckMiddleRawProjection b := by
  rcases hab with ⟨s, hs | hs⟩
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x =>
      norm_num [connectedSumNeckMiddleRawProjection.eq_def,
        connectedSumNeckBoundaryInclusion]
    | inr x =>
      norm_num [connectedSumNeckMiddleRawProjection.eq_def,
        connectedSumNeckBoundaryInclusion]
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x =>
      norm_num [connectedSumNeckMiddleRawProjection.eq_def,
        connectedSumNeckBoundaryInclusion]
    | inr x =>
      norm_num [connectedSumNeckMiddleRawProjection.eq_def,
        connectedSumNeckBoundaryInclusion]

noncomputable def connectedSumNeckMiddleProjection
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeck leftBoundary rightBoundary glue → Option ConnectedSumNeckCylinder :=
  Quot.lift connectedSumNeckMiddleRawProjection
    (connectedSumNeckMiddleRawProjection_eq_of_rel leftBoundary rightBoundary glue)

@[simp]
theorem connectedSumNeckMiddleProjection_middleMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (p : ConnectedSumNeckMiddle) :
    connectedSumNeckMiddleProjection leftBoundary rightBoundary glue
        (connectedSumNeckMiddleMap leftBoundary rightBoundary glue p) =
      some (connectedSumNeckMiddleCylinderInclusion p) := by
  change (@connectedSumNeckMiddleRawProjection K L)
      (Sum.inl (connectedSumNeckMiddleCylinderInclusion p)) =
    some (connectedSumNeckMiddleCylinderInclusion p)
  have h : 1 / 3 < ((connectedSumNeckMiddleCylinderInclusion p).2 : ℝ) ∧
      ((connectedSumNeckMiddleCylinderInclusion p).2 : ℝ) < 2 / 3 := by
    simpa [connectedSumNeckMiddleCylinderInclusion] using p.2.2
  simp only [connectedSumNeckMiddleRawProjection.eq_def]
  split
  · rfl
  · rename_i hn
    exact (hn h).elim


theorem injective_connectedSumNeckMiddleMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Function.Injective (connectedSumNeckMiddleMap leftBoundary rightBoundary glue) := by
  intro p q hpq
  have h := congrArg
    (connectedSumNeckMiddleProjection leftBoundary rightBoundary glue) hpq
  apply injective_connectedSumNeckMiddleCylinderInclusion
  exact Option.some.inj (by simpa using h)

theorem range_connectedSumNeckMiddleMap
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Set.range (connectedSumNeckMiddleMap leftBoundary rightBoundary glue) =
      connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    exact ⟨p.2.2.2, p.2.2.1⟩
  · intro z hz
    refine Quot.inductionOn z ?_ hz
    intro x hx
    change connectedSumNeckLeftRaw x ∧ connectedSumNeckRightRaw x at hx
    rcases x with p | (k | l)
    · let q : ConnectedSumNeckMiddle := (p.1, ⟨p.2, hx.2, hx.1⟩)
      refine ⟨q, ?_⟩
      apply congrArg (adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue))
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl
    · exact False.elim hx.2
    · exact False.elim hx.1


def connectedSumNeckMiddleIntervalInclusion :
    Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) → unitInterval :=
  fun t ↦ ⟨t, by
    constructor
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 3) t.2.1.le
    · exact le_trans t.2.2.le (by norm_num : (2 / 3 : ℝ) ≤ 1)⟩


theorem isOpenEmbedding_connectedSumNeckMiddleIntervalInclusion :
    IsOpenEmbedding connectedSumNeckMiddleIntervalInclusion := by
  let hst : Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) ⊆ Set.Icc 0 1 := by
    intro t ht
    exact ⟨le_trans (by norm_num) ht.1.le, le_trans ht.2.le (by norm_num)⟩
  change IsOpenEmbedding (Set.inclusion hst)
  apply Topology.IsOpenEmbedding.inclusion
  exact isOpen_Ioo.preimage continuous_subtype_val


def connectedSumNeckMiddleRawMap {K L : Type u} :
    ConnectedSumNeckMiddle → ConnectedSumNeckCylinder ⊕ (K ⊕ L) :=
  Sum.inl ∘ connectedSumNeckMiddleCylinderInclusion


theorem isOpenEmbedding_connectedSumNeckMiddleRawMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L] :
    IsOpenEmbedding (@connectedSumNeckMiddleRawMap K L) := by
  have hcyl : IsOpenEmbedding connectedSumNeckMiddleCylinderInclusion := by
    have heq : connectedSumNeckMiddleCylinderInclusion =
        Prod.map id connectedSumNeckMiddleIntervalInclusion := by
      funext p
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl
    rw [heq]
    exact
      (Topology.IsOpenEmbedding.id.prodMap
        isOpenEmbedding_connectedSumNeckMiddleIntervalInclusion)
  exact Topology.IsOpenEmbedding.inl.comp hcyl


abbrev ConnectedSumNeckMiddlePrequotient
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :=
  (adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)) ⁻¹'
    (connectedSumNeckLeft leftBoundary rightBoundary glue ∩
      connectedSumNeckRight leftBoundary rightBoundary glue)


def connectedSumNeckMiddlePrequotientMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckMiddle →
      ConnectedSumNeckMiddlePrequotient leftBoundary rightBoundary glue :=
  fun p ↦ ⟨connectedSumNeckMiddleRawMap p, ⟨p.2.2.2, p.2.2.1⟩⟩

theorem bijective_connectedSumNeckMiddlePrequotientMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Function.Bijective
      (connectedSumNeckMiddlePrequotientMap leftBoundary rightBoundary glue) := by
  constructor
  · intro p q hpq
    apply (isOpenEmbedding_connectedSumNeckMiddleRawMap (K := K) (L := L)).injective
    exact congrArg Subtype.val hpq
  · rintro ⟨x, hx⟩
    change connectedSumNeckLeftRaw x ∧ connectedSumNeckRightRaw x at hx
    rcases x with p | (k | l)
    · let q : ConnectedSumNeckMiddle := ⟨p.1, ⟨p.2, hx.2, hx.1⟩⟩
      refine ⟨q, ?_⟩
      apply Subtype.ext
      change Sum.inl (connectedSumNeckMiddleCylinderInclusion q) = Sum.inl p
      congr 1
    · exact False.elim hx.2
    · exact False.elim hx.1


noncomputable def connectedSumNeckMiddlePrequotientHomeomorph
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckMiddle ≃ₜ
      ConnectedSumNeckMiddlePrequotient leftBoundary rightBoundary glue :=
  let hemb : IsEmbedding
      (connectedSumNeckMiddlePrequotientMap leftBoundary rightBoundary glue) :=
    (isOpenEmbedding_connectedSumNeckMiddleRawMap (K := K) (L := L)).isEmbedding.codRestrict
      (ConnectedSumNeckMiddlePrequotient leftBoundary rightBoundary glue)
      (fun p ↦ (show connectedSumNeckMiddleRawMap p ∈
          ConnectedSumNeckMiddlePrequotient leftBoundary rightBoundary glue from
        ⟨p.2.2.2, p.2.2.1⟩))
  hemb.toHomeomorphOfSurjective
    (bijective_connectedSumNeckMiddlePrequotientMap
      leftBoundary rightBoundary glue).2


def connectedSumNeckMiddleQuotientMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckMiddlePrequotient leftBoundary rightBoundary glue →
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
  (connectedSumNeckLeft leftBoundary rightBoundary glue ∩
      connectedSumNeckRight leftBoundary rightBoundary glue).restrictPreimage
    (adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue))


theorem isQuotientMap_connectedSumNeckMiddleQuotientMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    IsQuotientMap (connectedSumNeckMiddleQuotientMap
      leftBoundary rightBoundary glue) :=
  (isQuotientMap_adjunctionMk connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).restrictPreimage_isOpen
      ((isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue).inter
        (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue))


theorem injective_connectedSumNeckMiddleQuotientMap
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Function.Injective (connectedSumNeckMiddleQuotientMap
      leftBoundary rightBoundary glue) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  apply Subtype.ext
  change connectedSumNeckLeftRaw x ∧ connectedSumNeckRightRaw x at hx
  change connectedSumNeckLeftRaw y ∧ connectedSumNeckRightRaw y at hy
  have hxy' : adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) x =
    adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) y :=
    congrArg Subtype.val hxy
  rcases x with p | (k | l)
  · rcases y with q | (k' | l')
    · have hproj := congrArg
          (connectedSumNeckMiddleProjection leftBoundary rightBoundary glue) hxy'
      change (@connectedSumNeckMiddleRawProjection K L) (Sum.inl p) =
        (@connectedSumNeckMiddleRawProjection K L) (Sum.inl q) at hproj
      simp only [connectedSumNeckMiddleRawProjection.eq_def] at hproj
      rw [if_pos ⟨hx.2, hx.1⟩, if_pos ⟨hy.2, hy.1⟩] at hproj
      exact congrArg (Sum.inl : ConnectedSumNeckCylinder →
        ConnectedSumNeckCylinder ⊕ (K ⊕ L)) (Option.some.inj hproj)
    · exact False.elim hy.2
    · exact False.elim hy.1
  · exact False.elim hx.2
  · exact False.elim hx.1


noncomputable def connectedSumNeckMiddleQuotientHomeomorph
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckMiddlePrequotient leftBoundary rightBoundary glue ≃ₜ
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
  IsHomeomorph.homeomorph _
    ((isHomeomorph_iff_isQuotientMap_injective).2
      ⟨isQuotientMap_connectedSumNeckMiddleQuotientMap
          leftBoundary rightBoundary glue,
        injective_connectedSumNeckMiddleQuotientMap
          leftBoundary rightBoundary glue⟩)


noncomputable def connectedSumNeckMiddleHomeomorph
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckMiddle ≃ₜ
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
  (connectedSumNeckMiddlePrequotientHomeomorph
      leftBoundary rightBoundary glue).trans
    (connectedSumNeckMiddleQuotientHomeomorph
      leftBoundary rightBoundary glue)

@[simp]
theorem connectedSumNeckMiddleHomeomorph_apply_coe
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (p : ConnectedSumNeckMiddle) :
    ↑(connectedSumNeckMiddleHomeomorph leftBoundary rightBoundary glue p) =
      connectedSumNeckMiddleMap leftBoundary rightBoundary glue p :=
  rfl


theorem simplyConnectedSpace_connectedSumNeck_inter
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) := by
  let hinterval : ContractibleSpace (Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) :=
    (convex_Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)).contractibleSpace
      ⟨(1 / 2 : ℝ), by norm_num⟩
  let _ := hinterval
  let _ : SimplyConnectedSpace (CellBoundary 3) :=
    simplyConnectedSpace_cellBoundaryThree
  let e :
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
          connectedSumNeckRight leftBoundary rightBoundary glue) ≃ₕ
        CellBoundary 3 :=
    (connectedSumNeckMiddleHomeomorph
        leftBoundary rightBoundary glue).symm.toHomotopyEquiv |>.trans
      (prodHomotopyEquivLeftOfContractible
        (CellBoundary 3) (Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)))
  exact e.simplyConnectedSpace

end DifferentialGeometry.Topology.ThreeManifold
