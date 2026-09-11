/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Homotopy.ClosedCell
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

set_option autoImplicit false

open Set
open scoped ContinuousMap
open unitInterval

namespace DifferentialGeometry.Topology.CellAttachment

open DifferentialGeometry.Topology

universe u

noncomputable def radiusRaw {X : Type u} (n : ℕ) : ClosedCell n ⊕ X → ℝ
  | Sum.inl d => ‖(d : EuclideanSpace ℝ (Fin n))‖
  | Sum.inr _ => 1

theorem radiusRaw_related {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (a b : ClosedCell n ⊕ X)
    (hab : adjunctionRel (cellBoundaryInclusion n) φ a b) :
    radiusRaw n a = radiusRaw n b := by
  rcases hab with ⟨x, hx | hx⟩
  · rcases hx with ⟨rfl, rfl⟩
    exact x.2
  · rcases hx with ⟨rfl, rfl⟩
    exact x.2.symm

noncomputable def radius {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    CellAdjunctionSpace n φ → ℝ :=
  Quot.lift (radiusRaw n) (radiusRaw_related n φ)

theorem radius_cell {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (d : ClosedCell n) :
    radius n φ (adjunctionCell (cellBoundaryInclusion n) φ d) =
      ‖(d : EuclideanSpace ℝ (Fin n))‖ := by
  rfl

theorem radius_lower {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (x : X) :
    radius n φ (adjunctionLower φ x) = 1 := by
  rfl

theorem continuous_radiusRaw {X : Type u} [TopologicalSpace X] (n : ℕ) :
    Continuous (radiusRaw (X := X) n) := by
  rw [continuous_sum_dom]
  constructor
  · change Continuous (fun d : ClosedCell n => ‖(d : EuclideanSpace ℝ (Fin n))‖)
    exact continuous_norm.comp continuous_subtype_val
  · change Continuous (fun _ : X => (1 : ℝ))
    exact continuous_const

theorem continuous_radius {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (radius n φ) :=
  continuous_quot_lift (radiusRaw_related n φ) (continuous_radiusRaw n)

def outer {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    Set (CellAdjunctionSpace n φ) := {q | (1 / 3 : ℝ) < radius n φ q}

def inner {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    Set (CellAdjunctionSpace n φ) := {q | radius n φ q < (2 / 3 : ℝ)}

theorem isOpen_outer {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : IsOpen (outer n φ) := by
  exact isOpen_lt continuous_const (continuous_radius n φ)

theorem isOpen_inner {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : IsOpen (inner n φ) := by
  exact isOpen_lt (continuous_radius n φ) continuous_const

theorem outer_union_inner {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : outer n φ ∪ inner n φ = Set.univ := by
  ext q
  constructor
  · intro h
    trivial
  · intro h
    change (1 / 3 : ℝ) < radius n φ q ∨ radius n φ q < (2 / 3 : ℝ)
    by_cases hr : (1 / 3 : ℝ) < radius n φ q
    · exact Or.inl hr
    · right
      have hle : radius n φ q ≤ (1 / 3 : ℝ) := le_of_not_gt hr
      norm_num at hle ⊢
      linarith

noncomputable def interiorCodeRaw {X : Type u} (n : ℕ) :
    ClosedCell n ⊕ X → Option (CellInterior n)
  | Sum.inl d => if h : ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1 then
      some ⟨d, h⟩ else none
  | Sum.inr _ => none

theorem interiorCodeRaw_related {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (a b : ClosedCell n ⊕ X)
    (hab : adjunctionRel (cellBoundaryInclusion n) φ a b) :
    interiorCodeRaw n a = interiorCodeRaw n b := by
  rcases hab with ⟨x, hx | hx⟩
  · rcases hx with ⟨rfl, rfl⟩
    change (if h : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 then
      some (⟨cellBoundaryInclusion n x, h⟩ : CellInterior n) else none) = none
    rw [dif_neg]
    simp [x.2]
  · rcases hx with ⟨rfl, rfl⟩
    change none = if h : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 then
      some (⟨cellBoundaryInclusion n x, h⟩ : CellInterior n) else none
    rw [dif_neg]
    simp [x.2]

noncomputable def interiorCode {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : CellAdjunctionSpace n φ → Option (CellInterior n) :=
  Quot.lift (interiorCodeRaw n) (interiorCodeRaw_related n φ)

theorem interiorCode_cellInterior {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (d : CellInterior n) :
    interiorCode n φ
      (adjunctionCell (cellBoundaryInclusion n) φ (cellInteriorInclusion n d)) = some d := by
  change (if h : ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1 then
    some (⟨(cellInteriorInclusion n d : EuclideanSpace ℝ (Fin n)), h⟩ : CellInterior n)
      else none) = some d
  rw [dif_pos d.2]
  exact congrArg some (Subtype.ext rfl)

def cellInteriorMap {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : CellInterior n → CellAdjunctionSpace n φ :=
  fun d => adjunctionCell (cellBoundaryInclusion n) φ (cellInteriorInclusion n d)

theorem cellInteriorMap_injective {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : Function.Injective (cellInteriorMap n φ) := by
  intro d e h
  have hc := congrArg (interiorCode n φ) h
  change interiorCode n φ
      (adjunctionCell (cellBoundaryInclusion n) φ (cellInteriorInclusion n d)) =
    interiorCode n φ
      (adjunctionCell (cellBoundaryInclusion n) φ (cellInteriorInclusion n e)) at hc
  rw [interiorCode_cellInterior, interiorCode_cellInterior] at hc
  exact Option.some.inj hc

theorem continuous_cellInteriorInclusion (n : ℕ) :
    Continuous (cellInteriorInclusion n) := by
  exact Continuous.subtype_mk (p := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ≤ 1)
    continuous_subtype_val (fun d => le_of_lt d.2)

theorem continuous_cellInteriorMap {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (cellInteriorMap n φ) :=
  (continuous_adjunctionCell (cellBoundaryInclusion n) φ).comp
    (continuous_cellInteriorInclusion n)

def rawCellInteriorImage {X : Type u} (n : ℕ)
    (s : Set (CellInterior n)) : Set (ClosedCell n ⊕ X) :=
  Sum.inl '' (cellInteriorInclusion n '' s)

theorem adjunctionMk_preimage_cellInteriorMap_image
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X)
    (s : Set (CellInterior n)) :
    adjunctionMk (cellBoundaryInclusion n) φ ⁻¹' (cellInteriorMap n φ '' s) =
      rawCellInteriorImage (X := X) n s := by
  ext z
  cases z with
  | inl d =>
      constructor
      · rintro ⟨e, he, hed⟩
        have hc := congrArg (interiorCode n φ) hed
        change interiorCode n φ
            (adjunctionCell (cellBoundaryInclusion n) φ (cellInteriorInclusion n e)) =
          interiorCode n φ
            (adjunctionMk (cellBoundaryInclusion n) φ (Sum.inl d)) at hc
        rw [interiorCode_cellInterior] at hc
        change some e = (if h : ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1 then
          some (⟨d, h⟩ : CellInterior n) else none) at hc
        split at hc
        next h =>
          have hed' : e = (⟨d, h⟩ : CellInterior n) := Option.some.inj hc
          subst e
          exact ⟨d, ⟨⟨d, h⟩, he, by apply Subtype.ext; rfl⟩, rfl⟩
        next h => simp at hc
      · rintro ⟨_, ⟨e, he, rfl⟩, hdinl⟩
        injection hdinl with hed
        subst d
        exact ⟨e, he, rfl⟩
  | inr x =>
      constructor
      · rintro ⟨e, he, hex⟩
        have hc := congrArg (interiorCode n φ) hex
        change interiorCode n φ
            (adjunctionCell (cellBoundaryInclusion n) φ (cellInteriorInclusion n e)) =
          interiorCode n φ
            (adjunctionMk (cellBoundaryInclusion n) φ (Sum.inr x)) at hc
        rw [interiorCode_cellInterior] at hc
        change some e = none at hc
        simp at hc
      · rintro ⟨d, hd, hdx⟩
        cases hdx

theorem isOpen_range_cellInteriorInclusion (n : ℕ) :
    IsOpen (Set.range (cellInteriorInclusion n)) := by
  have heq : Set.range (cellInteriorInclusion n) =
      {d : ClosedCell n | ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1} := by
    ext d
    constructor
    · rintro ⟨e, rfl⟩
      exact e.2
    · intro hd
      exact ⟨⟨d, hd⟩, by apply Subtype.ext; rfl⟩
  rw [heq]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem isOpenMap_cellInteriorInclusion (n : ℕ) :
    IsOpenMap (cellInteriorInclusion n) := by
  intro s hs
  have hopen : IsOpen (Subtype.val '' s : Set (EuclideanSpace ℝ (Fin n))) := by
    rcases hs with ⟨t, ht, hst⟩
    rw [← hst]
    have heq : Subtype.val ''
        (Subtype.val ⁻¹' t : Set (CellInterior n)) =
        t ∩ {x : EuclideanSpace ℝ (Fin n) | ‖x‖ < 1} := by
      ext x
      simp
    rw [heq]
    exact ht.inter (isOpen_lt continuous_norm continuous_const)
  have heq : cellInteriorInclusion n '' s =
      Subtype.val ⁻¹' (Subtype.val '' s : Set (EuclideanSpace ℝ (Fin n))) := by
    ext d
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, hed⟩
      refine ⟨e, he, ?_⟩
      apply Subtype.ext
      exact hed
  rw [heq]
  exact hopen.preimage continuous_subtype_val

theorem isOpen_rawCellInteriorImage {X : Type u} [TopologicalSpace X] (n : ℕ)
    {s : Set (CellInterior n)} (hs : IsOpen s) :
    IsOpen (rawCellInteriorImage (X := X) n s) :=
  isOpenMap_inl _ ((isOpenMap_cellInteriorInclusion n) s hs)

theorem isOpenMap_cellInteriorMap {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : IsOpenMap (cellInteriorMap n φ) := by
  intro s hs
  rw [← (isQuotientMap_adjunctionMk (cellBoundaryInclusion n) φ).isOpen_preimage,
    adjunctionMk_preimage_cellInteriorMap_image]
  exact isOpen_rawCellInteriorImage n hs

theorem isOpenEmbedding_cellInteriorMap {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Topology.IsOpenEmbedding (cellInteriorMap n φ) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_cellInteriorMap n φ) (cellInteriorMap_injective n φ)
    (isOpenMap_cellInteriorMap n φ)

theorem inner_subset_range_cellInteriorMap {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : inner n φ ⊆ Set.range (cellInteriorMap n φ) := by
  intro q hq
  refine Quot.inductionOn q ?_ hq
  intro z hz
  cases z with
  | inl d =>
      have hd : ‖(d : EuclideanSpace ℝ (Fin n))‖ < (2 / 3 : ℝ) := hz
      have hd1 : ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1 := by
        norm_num at hd ⊢
        linarith
      exact ⟨(⟨d, hd1⟩ : CellInterior n), rfl⟩
  | inr x =>
      norm_num [inner, radius, radiusRaw] at hz

noncomputable def innerHomeomorphDomain {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) :
    (cellInteriorMap n φ ⁻¹' inner n φ) ≃ₜ inner n φ :=
  (isOpenEmbedding_cellInteriorMap n φ).isEmbedding.homeomorphOfSubsetRange
    (inner_subset_range_cellInteriorMap n φ)

theorem innerHomeomorphDomain_apply {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) (d : cellInteriorMap n φ ⁻¹' inner n φ) :
    ((innerHomeomorphDomain n φ d : inner n φ) : CellAdjunctionSpace n φ) =
      cellInteriorMap n φ d := by
  rfl

noncomputable def innerDomainToBall {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) :
    (cellInteriorMap n φ ⁻¹' inner n φ) → Metric.ball
      (0 : EuclideanSpace ℝ (Fin n)) (2 / 3 : ℝ) :=
  fun d => ⟨(d.1 : EuclideanSpace ℝ (Fin n)), by
    have hd := d.2
    change radius n φ (cellInteriorMap n φ d.1) < (2 / 3 : ℝ) at hd
    change ‖(d.1 : EuclideanSpace ℝ (Fin n))‖ < (2 / 3 : ℝ) at hd
    simpa only [Metric.mem_ball, dist_zero_right] using hd⟩

theorem innerDomainToBall_bijective {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : Function.Bijective (innerDomainToBall n φ) := by
  constructor
  · intro d e h
    have hval : (d.1 : EuclideanSpace ℝ (Fin n)) =
        (e.1 : EuclideanSpace ℝ (Fin n)) :=
      congrArg (fun z : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 / 3 : ℝ) =>
        (z : EuclideanSpace ℝ (Fin n))) h
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  · intro x
    have hx23 : ‖(x : EuclideanSpace ℝ (Fin n))‖ < (2 / 3 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using x.2
    have hx1 : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 := by
      norm_num at hx23 ⊢
      linarith
    let d : CellInterior n := ⟨x, hx1⟩
    have hdinner : cellInteriorMap n φ d ∈ inner n φ := by
      exact hx23
    refine ⟨⟨d, hdinner⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem continuous_innerDomainToBall {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (innerDomainToBall n φ) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp continuous_subtype_val

noncomputable def innerDomainHomeomorphBall {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) :
    (cellInteriorMap n φ ⁻¹' inner n φ) ≃ₜ Metric.ball
      (0 : EuclideanSpace ℝ (Fin n)) (2 / 3 : ℝ) := by
  let e := Equiv.ofBijective (innerDomainToBall n φ) (innerDomainToBall_bijective n φ)
  exact e.toHomeomorphOfContinuousOpen (continuous_innerDomainToBall n φ) (by
    have hemb : Topology.IsOpenEmbedding (innerDomainToBall n φ) := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · exact continuous_innerDomainToBall n φ
      · exact (innerDomainToBall_bijective n φ).1
      · intro s hs
        have hopenDomain : IsOpen
            (cellInteriorMap n φ ⁻¹' inner n φ : Set (CellInterior n)) :=
          (isOpen_inner n φ).preimage (continuous_cellInteriorMap n φ)
        have hembVal : Topology.IsOpenEmbedding
            (fun d : cellInteriorMap n φ ⁻¹' inner n φ =>
              (d.1 : EuclideanSpace ℝ (Fin n))) :=
          (isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal.comp
            hopenDomain.isOpenEmbedding_subtypeVal
        have hballOpen : IsOpen (Metric.ball
            (0 : EuclideanSpace ℝ (Fin n)) (2 / 3 : ℝ)) := Metric.isOpen_ball
        rw [hballOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]
        rw [Set.image_image]
        change IsOpen ((fun d : cellInteriorMap n φ ⁻¹' inner n φ =>
          (d.1 : EuclideanSpace ℝ (Fin n))) '' s)
        exact hembVal.isOpenMap s hs
    exact hemb.isOpenMap)

theorem contractibleSpace_inner {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : ContractibleSpace (inner n φ) := by
  let hball : ContractibleSpace (Metric.ball
      (0 : EuclideanSpace ℝ (Fin n)) (2 / 3 : ℝ)) :=
    Metric.contractibleSpace_ball (by norm_num)
  let _ := hball
  let _ : ContractibleSpace (cellInteriorMap n φ ⁻¹' inner n φ) :=
    (innerDomainHomeomorphBall n φ).contractibleSpace
  exact (innerHomeomorphDomain n φ).symm.contractibleSpace

def overlapDomain {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : Set (CellInterior n) :=
  cellInteriorMap n φ ⁻¹' (outer n φ ∩ inner n φ)

abbrev shellInterval := Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)

theorem overlapDomain_norm_lower {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (d : overlapDomain n φ) :
    (1 / 3 : ℝ) < ‖(d.1 : EuclideanSpace ℝ (Fin n))‖ := by
  exact d.2.1

theorem overlapDomain_norm_upper {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (d : overlapDomain n φ) :
    ‖(d.1 : EuclideanSpace ℝ (Fin n))‖ < (2 / 3 : ℝ) := by
  exact d.2.2

theorem overlapDomain_ne_zero {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (d : overlapDomain n φ) :
    (d.1 : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
  rw [← norm_pos_iff]
  exact (by norm_num : (0 : ℝ) < 1 / 3).trans (overlapDomain_norm_lower n φ d)

noncomputable def overlapDomainToBoundaryInterval
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    overlapDomain n φ → CellBoundary n × shellInterval :=
  fun d => (Homotopy.boundaryNormalize (d.1 : EuclideanSpace ℝ (Fin n))
      (overlapDomain_ne_zero n φ d),
    ⟨‖(d.1 : EuclideanSpace ℝ (Fin n))‖,
      overlapDomain_norm_lower n φ d, overlapDomain_norm_upper n φ d⟩)

theorem continuous_overlapDomainToBoundaryInterval
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    Continuous (overlapDomainToBoundaryInterval n φ) := by
  have hval : Continuous (fun d : overlapDomain n φ =>
      (d.1 : EuclideanSpace ℝ (Fin n))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnorm : Continuous (fun d : overlapDomain n φ =>
      ‖(d.1 : EuclideanSpace ℝ (Fin n))‖) := continuous_norm.comp hval
  have hnormalize : Continuous (fun d : overlapDomain n φ =>
      (Homotopy.boundaryNormalize (d.1 : EuclideanSpace ℝ (Fin n))
        (overlapDomain_ne_zero n φ d) : CellBoundary n)) := by
    apply Continuous.subtype_mk
    exact (Continuous.inv₀ hnorm (fun d =>
      norm_ne_zero_iff.mpr (overlapDomain_ne_zero n φ d))).smul hval
  exact hnormalize.prodMk (Continuous.subtype_mk hnorm (fun d =>
    ⟨overlapDomain_norm_lower n φ d, overlapDomain_norm_upper n φ d⟩))

noncomputable def boundaryIntervalToOverlapDomain
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    CellBoundary n × shellInterval → overlapDomain n φ :=
  fun p => ⟨⟨(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)), by
    have hp0 : (0 : ℝ) < p.2 := (by norm_num : (0 : ℝ) < 1 / 3).trans p.2.2.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp0, p.1.2, mul_one]
    exact p.2.2.2.trans (by norm_num)⟩, by
      have hp0 : (0 : ℝ) < p.2 := (by norm_num : (0 : ℝ) < 1 / 3).trans p.2.2.1
      change (1 / 3 : ℝ) < ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))‖ ∧
        ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))‖ < (2 / 3 : ℝ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp0, p.1.2, mul_one]
      exact ⟨p.2.2.1, p.2.2.2⟩⟩

theorem continuous_boundaryIntervalToOverlapDomain
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    Continuous (boundaryIntervalToOverlapDomain n φ) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)

theorem boundaryIntervalToOverlapDomain_leftInverse
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    Function.LeftInverse (boundaryIntervalToOverlapDomain n φ)
      (overlapDomainToBoundaryInterval n φ) := by
  intro d
  apply Subtype.ext
  apply Subtype.ext
  exact Homotopy.smul_boundaryNormalize _ (overlapDomain_ne_zero n φ d)

theorem boundaryIntervalToOverlapDomain_rightInverse
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    Function.RightInverse (boundaryIntervalToOverlapDomain n φ)
      (overlapDomainToBoundaryInterval n φ) := by
  intro p
  apply Prod.ext
  · apply Subtype.ext
    simp only [overlapDomainToBoundaryInterval, boundaryIntervalToOverlapDomain]
    change ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))‖⁻¹ •
        ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))) = p.1
    have hp0 : (0 : ℝ) < p.2 := (by norm_num : (0 : ℝ) < 1 / 3).trans p.2.2.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp0, p.1.2, mul_one,
      smul_smul, inv_mul_cancel₀ hp0.ne', one_smul]
  · apply Subtype.ext
    simp only [overlapDomainToBoundaryInterval, boundaryIntervalToOverlapDomain]
    have hp0 : (0 : ℝ) < p.2 := (by norm_num : (0 : ℝ) < 1 / 3).trans p.2.2.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp0, p.1.2, mul_one]

noncomputable def overlapDomainHomeomorphBoundaryInterval
    {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    overlapDomain n φ ≃ₜ CellBoundary n × shellInterval where
  toFun := overlapDomainToBoundaryInterval n φ
  invFun := boundaryIntervalToOverlapDomain n φ
  left_inv := boundaryIntervalToOverlapDomain_leftInverse n φ
  right_inv := boundaryIntervalToOverlapDomain_rightInverse n φ
  continuous_toFun := continuous_overlapDomainToBoundaryInterval n φ
  continuous_invFun := continuous_boundaryIntervalToOverlapDomain n φ

theorem overlap_subset_range_cellInteriorMap {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) :
    outer n φ ∩ inner n φ ⊆ Set.range (cellInteriorMap n φ) :=
  fun _ hq => inner_subset_range_cellInteriorMap n φ hq.2

noncomputable def overlapHomeomorphDomain {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) :
    overlapDomain n φ ≃ₜ ↑(outer n φ ∩ inner n φ) :=
  (isOpenEmbedding_cellInteriorMap n φ).isEmbedding.homeomorphOfSubsetRange
    (overlap_subset_range_cellInteriorMap n φ)

noncomputable def prodHomotopyEquivLeftOfContractible
    (A B : Type*) [TopologicalSpace A] [TopologicalSpace B] [ContractibleSpace B] :
    A × B ≃ₕ A :=
  ((ContinuousMap.HomotopyEquiv.refl A).prodCongr
      (ContractibleSpace.hequiv_unit B).some).trans
    (Homeomorph.prodUnique A Unit).toHomotopyEquiv

noncomputable def cellBoundaryThreeHomeomorphSphereTwo :
    CellBoundary 3 ≃ₜ SphereTwo where
  toFun := fun x => ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using x.2⟩
  invFun := fun x => ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using x.2⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun x => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val (fun x => by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2)
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val (fun x => by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2)

theorem simplyConnectedSpace_cellBoundaryThree :
    SimplyConnectedSpace (CellBoundary 3) :=
  cellBoundaryThreeHomeomorphSphereTwo.toHomotopyEquiv.simplyConnectedSpace

theorem simplyConnectedSpace_overlapThree {X : Type u} [TopologicalSpace X]
    (φ : CellBoundary 3 → X) :
    SimplyConnectedSpace ↑(outer 3 φ ∩ inner 3 φ) := by
  let hinterval : ContractibleSpace shellInterval :=
    (convex_Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)).contractibleSpace
      ⟨(1 / 2 : ℝ), by norm_num⟩
  let _ := hinterval
  let e : ↑(outer 3 φ ∩ inner 3 φ) ≃ₕ SphereTwo :=
    (overlapHomeomorphDomain 3 φ).symm.toHomotopyEquiv |>.trans
      (overlapDomainHomeomorphBoundaryInterval 3 φ).toHomotopyEquiv |>.trans
        (prodHomotopyEquivLeftOfContractible (CellBoundary 3) shellInterval) |>.trans
          cellBoundaryThreeHomeomorphSphereTwo.toHomotopyEquiv
  exact e.simplyConnectedSpace

noncomputable def outerRadialScale (t : I) (r : ℝ) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * (max r (1 / 3 : ℝ))⁻¹

theorem outerRadialScale_nonneg (t : I) (r : ℝ) :
    0 ≤ outerRadialScale t r := by
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hmpos : (0 : ℝ) < max r (1 / 3 : ℝ) :=
    (by norm_num : (0 : ℝ) < 1 / 3).trans_le (le_max_right _ _)
  have hm : (0 : ℝ) ≤ (max r (1 / 3 : ℝ))⁻¹ := inv_nonneg.mpr hmpos.le
  unfold outerRadialScale
  exact add_nonneg (sub_nonneg.mpr ht1) (mul_nonneg ht0 hm)

noncomputable def outerPushCell (n : ℕ) (t : I) (d : ClosedCell n) : ClosedCell n :=
  ⟨outerRadialScale t ‖(d : EuclideanSpace ℝ (Fin n))‖ •
      (d : EuclideanSpace ℝ (Fin n)), by
    let r : ℝ := ‖(d : EuclideanSpace ℝ (Fin n))‖
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr1 : r ≤ 1 := d.2
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hmpos : (0 : ℝ) < max r (1 / 3 : ℝ) :=
      (by norm_num : (0 : ℝ) < 1 / 3).trans_le (le_max_right _ _)
    have hratio : r * (max r (1 / 3 : ℝ))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hmpos]
      exact le_max_left _ _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (outerRadialScale_nonneg t r)]
    change outerRadialScale t r * r ≤ 1
    unfold outerRadialScale
    calc
      ((1 - (t : ℝ)) + (t : ℝ) * (max r (1 / 3 : ℝ))⁻¹) * r =
          (1 - (t : ℝ)) * r + (t : ℝ) *
            (r * (max r (1 / 3 : ℝ))⁻¹) := by ring
      _ ≤ (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hr1 (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left hratio ht0)
      _ = 1 := by ring⟩

@[simp] theorem outerPushCell_zero (n : ℕ) (d : ClosedCell n) :
    outerPushCell n 0 d = d := by
  apply Subtype.ext
  simp [outerPushCell, outerRadialScale]

theorem outerPushCell_boundary (n : ℕ) (t : I) (b : CellBoundary n) :
    outerPushCell n t (cellBoundaryInclusion n b) = cellBoundaryInclusion n b := by
  apply Subtype.ext
  change outerRadialScale t ‖(b : EuclideanSpace ℝ (Fin n))‖ •
      (b : EuclideanSpace ℝ (Fin n)) = b
  rw [b.2]
  norm_num [outerRadialScale, max_eq_left]

theorem continuous_outerPushCell (n : ℕ) :
    Continuous (fun p : I × ClosedCell n => outerPushCell n p.1 p.2) := by
  apply Continuous.subtype_mk
  have hnorm : Continuous (fun p : I × ClosedCell n =>
      ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) :=
    continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
  have hmax : Continuous (fun p : I × ClosedCell n =>
      max ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ (1 / 3 : ℝ)) :=
    hnorm.max continuous_const
  have hmax_ne : ∀ p : I × ClosedCell n,
      max ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ (1 / 3 : ℝ) ≠ 0 := fun p => by
    positivity
  have hscale : Continuous (fun p : I × ClosedCell n =>
      outerRadialScale p.1 ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) := by
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul (hmax.inv₀ hmax_ne))
  exact hscale.smul (continuous_subtype_val.comp continuous_snd)

noncomputable def outerPushRaw {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) :
    I × (ClosedCell n ⊕ X) → CellAdjunctionSpace n φ
  | (t, Sum.inl d) => adjunctionCell (cellBoundaryInclusion n) φ (outerPushCell n t d)
  | (_, Sum.inr x) => adjunctionLower φ x

theorem continuous_outerPushRaw {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (outerPushRaw n φ) := by
  have hsum : Continuous (Sum.elim
      (fun p : I × ClosedCell n =>
        adjunctionCell (cellBoundaryInclusion n) φ (outerPushCell n p.1 p.2))
      (fun p : I × X => adjunctionLower φ p.2)) := by
    apply Continuous.sumElim
    · exact (continuous_adjunctionCell (cellBoundaryInclusion n) φ).comp
        (continuous_outerPushCell n)
    · exact (continuous_adjunctionLower (cellBoundaryInclusion n) φ).comp continuous_snd
  let e : I × (ClosedCell n ⊕ X) ≃ₜ (I × ClosedCell n) ⊕ (I × X) :=
    Homeomorph.prodSumDistrib
  have hcomp := hsum.comp e.continuous
  have heq : (Sum.elim
      (fun p : I × ClosedCell n =>
        adjunctionCell (cellBoundaryInclusion n) φ (outerPushCell n p.1 p.2))
      (fun p : I × X => adjunctionLower φ p.2)) ∘ e = outerPushRaw n φ := by
    funext p
    rcases p with ⟨t, z⟩
    cases z <;> rfl
  rw [← heq]
  exact hcomp

theorem outerPushRaw_related {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (t : I) (a b : ClosedCell n ⊕ X)
    (hab : adjunctionRel (cellBoundaryInclusion n) φ a b) :
    outerPushRaw n φ (t, a) = outerPushRaw n φ (t, b) := by
  rcases hab with ⟨x, hx | hx⟩
  · rcases hx with ⟨rfl, rfl⟩
    rw [outerPushRaw, outerPushCell_boundary]
    exact adjunction_coherence (cellBoundaryInclusion n) φ x
  · rcases hx with ⟨rfl, rfl⟩
    rw [outerPushRaw, outerPushCell_boundary]
    exact (adjunction_coherence (cellBoundaryInclusion n) φ x).symm

noncomputable def outerPush {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) :
    I × CellAdjunctionSpace n φ → CellAdjunctionSpace n φ :=
  fun p => Quot.lift (fun z => outerPushRaw n φ (p.1, z))
    (outerPushRaw_related n φ p.1) p.2

theorem continuous_outerPush {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (outerPush n φ) := by
  apply (isQuotientMap_adjunctionMk (cellBoundaryInclusion n) φ).continuous_lift_prod_right
  change Continuous (outerPushRaw n φ)
  exact continuous_outerPushRaw n φ

@[simp] theorem outerPush_zero {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (q : CellAdjunctionSpace n φ) :
    outerPush n φ (0, q) = q := by
  refine Quot.inductionOn q ?_
  intro z
  cases z with
  | inl d =>
      change adjunctionCell (cellBoundaryInclusion n) φ (outerPushCell n 0 d) =
        adjunctionCell (cellBoundaryInclusion n) φ d
      rw [outerPushCell_zero]
  | inr x => rfl

theorem outerPushCell_norm_of_gt (n : ℕ) (t : I) (d : ClosedCell n)
    (hd : (1 / 3 : ℝ) < ‖(d : EuclideanSpace ℝ (Fin n))‖) :
    ‖(outerPushCell n t d : EuclideanSpace ℝ (Fin n))‖ =
      (1 - (t : ℝ)) * ‖(d : EuclideanSpace ℝ (Fin n))‖ + (t : ℝ) := by
  have hrpos : (0 : ℝ) < ‖(d : EuclideanSpace ℝ (Fin n))‖ :=
    (by norm_num : (0 : ℝ) < 1 / 3).trans hd
  rw [outerPushCell, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (outerRadialScale_nonneg t _)]
  unfold outerRadialScale
  rw [max_eq_left hd.le]
  calc
    ((1 - (t : ℝ)) + (t : ℝ) * ‖(d : EuclideanSpace ℝ (Fin n))‖⁻¹) *
        ‖(d : EuclideanSpace ℝ (Fin n))‖ =
      (1 - (t : ℝ)) * ‖(d : EuclideanSpace ℝ (Fin n))‖ +
        (t : ℝ) * (‖(d : EuclideanSpace ℝ (Fin n))‖⁻¹ *
          ‖(d : EuclideanSpace ℝ (Fin n))‖) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hrpos.ne', mul_one]

theorem outerPush_mem_outer {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (t : I) (q : CellAdjunctionSpace n φ)
    (hq : q ∈ outer n φ) : outerPush n φ (t, q) ∈ outer n φ := by
  refine Quot.inductionOn q ?_ hq
  intro z hz
  cases z with
  | inl d =>
      change (1 / 3 : ℝ) < ‖(d : EuclideanSpace ℝ (Fin n))‖ at hz
      have hstay : 0 ≤ (t : ℝ) * (1 - ‖(d : EuclideanSpace ℝ (Fin n))‖) :=
        mul_nonneg t.2.1 (sub_nonneg.mpr d.2)
      change (1 / 3 : ℝ) < ‖(outerPushCell n t d : EuclideanSpace ℝ (Fin n))‖
      rw [outerPushCell_norm_of_gt n t d hz]
      have heq : (1 - (t : ℝ)) * ‖(d : EuclideanSpace ℝ (Fin n))‖ + (t : ℝ) =
          ‖(d : EuclideanSpace ℝ (Fin n))‖ +
            (t : ℝ) * (1 - ‖(d : EuclideanSpace ℝ (Fin n))‖) := by ring
      rw [heq]
      exact hz.trans_le (le_add_of_nonneg_right hstay)
  | inr x =>
      change (1 / 3 : ℝ) < 1
      norm_num

noncomputable def outerPushRestricted {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : I × outer n φ → outer n φ :=
  fun p => ⟨outerPush n φ (p.1, p.2), outerPush_mem_outer n φ p.1 p.2 p.2.2⟩

theorem continuous_outerPushRestricted {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (outerPushRestricted n φ) := by
  apply Continuous.subtype_mk
  exact (continuous_outerPush n φ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

@[simp] theorem outerPushRestricted_zero {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (q : outer n φ) :
    outerPushRestricted n φ (0, q) = q := by
  apply Subtype.ext
  exact outerPush_zero n φ q

@[simp] theorem outerPush_lower {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (t : I) (x : X) :
    outerPush n φ (t, adjunctionLower φ x) = adjunctionLower φ x := by
  rfl

theorem outerPushCell_one_of_gt (n : ℕ) (d : ClosedCell n)
    (hd : (1 / 3 : ℝ) < ‖(d : EuclideanSpace ℝ (Fin n))‖) :
    outerPushCell n 1 d = cellBoundaryInclusion n
      (Homotopy.boundaryNormalize (d : EuclideanSpace ℝ (Fin n))
        (norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 3).trans hd))) := by
  apply Subtype.ext
  have hrpos : (0 : ℝ) < ‖(d : EuclideanSpace ℝ (Fin n))‖ :=
    (by norm_num : (0 : ℝ) < 1 / 3).trans hd
  change outerRadialScale 1 ‖(d : EuclideanSpace ℝ (Fin n))‖ •
      (d : EuclideanSpace ℝ (Fin n)) =
    ‖(d : EuclideanSpace ℝ (Fin n))‖⁻¹ •
      (d : EuclideanSpace ℝ (Fin n))
  unfold outerRadialScale
  rw [max_eq_left hd.le]
  norm_num

noncomputable def lowerCodeRaw {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : ClosedCell n ⊕ X → Option X
  | Sum.inl d => if h : ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1 then
      some (φ ⟨d, h⟩) else none
  | Sum.inr x => some x

theorem lowerCodeRaw_related {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (a b : ClosedCell n ⊕ X)
    (hab : adjunctionRel (cellBoundaryInclusion n) φ a b) :
    lowerCodeRaw n φ a = lowerCodeRaw n φ b := by
  rcases hab with ⟨x, hx | hx⟩
  · rcases hx with ⟨rfl, rfl⟩
    change (if h : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 then
      some (φ ⟨cellBoundaryInclusion n x, h⟩) else none) = some (φ x)
    rw [dif_pos x.2]
    congr 2
  · rcases hx with ⟨rfl, rfl⟩
    change some (φ x) = if h : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 then
      some (φ ⟨cellBoundaryInclusion n x, h⟩) else none
    rw [dif_pos x.2]
    congr 2

noncomputable def lowerCode {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : CellAdjunctionSpace n φ → Option X :=
  Quot.lift (lowerCodeRaw n φ) (lowerCodeRaw_related n φ)

@[simp] theorem lowerCode_lower {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) (x : X) :
    lowerCode n φ (adjunctionLower φ x) = some x := by
  rfl

theorem adjunctionLower_injective {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) :
    Function.Injective (adjunctionLower (i := cellBoundaryInclusion n) φ) := by
  intro x y h
  have hc := congrArg (lowerCode n φ) h
  simpa using hc

def outerCellDomain (n : ℕ) : Set (ClosedCell n) :=
  {d | (1 / 3 : ℝ) < ‖(d : EuclideanSpace ℝ (Fin n))‖}

def rawOuter {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : Set (ClosedCell n ⊕ X) :=
  adjunctionMk (cellBoundaryInclusion n) φ ⁻¹' outer n φ

def outerRawInclusion {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : outerCellDomain n ⊕ X → rawOuter n φ
  | Sum.inl d => ⟨Sum.inl d.1, d.2⟩
  | Sum.inr x => ⟨Sum.inr x, by
      change (1 / 3 : ℝ) < 1
      norm_num⟩

theorem continuous_outerRawInclusion {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (outerRawInclusion n φ) := by
  have h : Continuous (Sum.elim
      (fun d : outerCellDomain n => (⟨Sum.inl d.1, d.2⟩ : rawOuter n φ))
      (fun x : X => (⟨Sum.inr x, by
        change (1 / 3 : ℝ) < 1
        norm_num⟩ : rawOuter n φ))) := by
    apply Continuous.sumElim
    · apply Continuous.subtype_mk
      exact continuous_inl.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_inr
  have heq : outerRawInclusion n φ = Sum.elim
      (fun d : outerCellDomain n => (⟨Sum.inl d.1, d.2⟩ : rawOuter n φ))
      (fun x : X => (⟨Sum.inr x, by
        change (1 / 3 : ℝ) < 1
        norm_num⟩ : rawOuter n φ)) := by
    funext z
    cases z <;> rfl
  rw [heq]
  exact h

theorem isOpen_outerCellDomain (n : ℕ) : IsOpen (outerCellDomain n) :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)

theorem isOpenMap_outerRawInclusion {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : IsOpenMap (outerRawInclusion n φ) := by
  rw [isOpenMap_sum]
  constructor
  · apply IsOpenMap.codRestrict
    exact isOpenMap_inl.comp (isOpen_outerCellDomain n).isOpenEmbedding_subtypeVal.isOpenMap
  · apply IsOpenMap.codRestrict
    exact isOpenMap_inr

theorem outerRawInclusion_bijective {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : Function.Bijective (outerRawInclusion n φ) := by
  constructor
  · intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            have hab : (a.1 : ClosedCell n) = b.1 := by
              injection congrArg Subtype.val h
            exact congrArg Sum.inl (Subtype.ext hab)
        | inr b => cases congrArg Subtype.val h
    | inr a =>
        cases b with
        | inl b => cases congrArg Subtype.val h
        | inr b =>
            have hab : a = b := by
              injection congrArg Subtype.val h
            exact congrArg Sum.inr hab
  · intro z
    rcases z with ⟨z, hz⟩
    cases z with
    | inl d => exact ⟨Sum.inl ⟨d, hz⟩, rfl⟩
    | inr x => exact ⟨Sum.inr x, rfl⟩

noncomputable def outerRawHomeomorph {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : outerCellDomain n ⊕ X ≃ₜ rawOuter n φ :=
  (Equiv.ofBijective (outerRawInclusion n φ) (outerRawInclusion_bijective n φ))
    |>.toHomeomorphOfContinuousOpen (continuous_outerRawInclusion n φ)
      (isOpenMap_outerRawInclusion n φ)

noncomputable def outerCellToBoundary (n : ℕ) : outerCellDomain n → CellBoundary n :=
  fun d => Homotopy.boundaryNormalize (d.1 : EuclideanSpace ℝ (Fin n))
    (norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 3).trans d.2))

theorem continuous_outerCellToBoundary (n : ℕ) :
    Continuous (outerCellToBoundary n) := by
  have hval : Continuous (fun d : outerCellDomain n =>
      (d.1 : EuclideanSpace ℝ (Fin n))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnorm : Continuous (fun d : outerCellDomain n =>
      ‖(d.1 : EuclideanSpace ℝ (Fin n))‖) := continuous_norm.comp hval
  apply Continuous.subtype_mk
  exact (Continuous.inv₀ hnorm (fun d => norm_ne_zero_iff.mpr
    (norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 3).trans d.2)))).smul hval

noncomputable def outerRawRetraction {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : rawOuter n φ → X :=
  (Sum.elim (φ ∘ outerCellToBoundary n) id) ∘ (outerRawHomeomorph n φ).symm

theorem continuous_outerRawRetraction {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) (hφ : Continuous φ) :
    Continuous (outerRawRetraction n φ) := by
  apply Continuous.comp _ (outerRawHomeomorph n φ).symm.continuous
  apply Continuous.sumElim
  · exact hφ.comp (continuous_outerCellToBoundary n)
  · exact continuous_id

theorem outerRawRetraction_inl {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) (d : ClosedCell n)
    (hd : Sum.inl d ∈ rawOuter n φ) :
    outerRawRetraction n φ ⟨Sum.inl d, hd⟩ = φ
      (Homotopy.boundaryNormalize (d : EuclideanSpace ℝ (Fin n))
        (norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 3).trans hd))) := by
  have hinv : (outerRawHomeomorph n φ).symm ⟨Sum.inl d, hd⟩ =
      Sum.inl (⟨d, hd⟩ : outerCellDomain n) := by
    apply (outerRawHomeomorph n φ).injective
    rw [(outerRawHomeomorph n φ).apply_symm_apply]
    rfl
  change (Sum.elim (φ ∘ outerCellToBoundary n) id)
    ((outerRawHomeomorph n φ).symm ⟨Sum.inl d, hd⟩) = _
  rw [hinv]
  rfl

@[simp] theorem outerRawRetraction_inr {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) (x : X)
    (hx : Sum.inr x ∈ rawOuter n φ) :
    outerRawRetraction n φ ⟨Sum.inr x, hx⟩ = x := by
  have hinv : (outerRawHomeomorph n φ).symm ⟨Sum.inr x, hx⟩ = Sum.inr x := by
    apply (outerRawHomeomorph n φ).injective
    rw [(outerRawHomeomorph n φ).apply_symm_apply]
    rfl
  change (Sum.elim (φ ∘ outerCellToBoundary n) id)
    ((outerRawHomeomorph n φ).symm ⟨Sum.inr x, hx⟩) = _
  rw [hinv]
  rfl

def outerAdjunctionMk {X : Type u} (n : ℕ)
    (φ : CellBoundary n → X) : rawOuter n φ → outer n φ :=
  (outer n φ).restrictPreimage (adjunctionMk (cellBoundaryInclusion n) φ)

theorem continuous_outerAdjunctionMk {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Continuous (outerAdjunctionMk n φ) :=
  (continuous_adjunctionMk (cellBoundaryInclusion n) φ).restrictPreimage

theorem isQuotientMap_outerAdjunctionMk {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : Topology.IsQuotientMap (outerAdjunctionMk n φ) :=
  (isQuotientMap_adjunctionMk (cellBoundaryInclusion n) φ).restrictPreimage_isOpen
    (isOpen_outer n φ)

theorem outerPush_one_eq_lower_outerRawRetraction
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (z : rawOuter n φ) :
    outerPush n φ (1, (outerAdjunctionMk n φ z : outer n φ)) =
      adjunctionLower φ (outerRawRetraction n φ z) := by
  rcases z with ⟨z, hz⟩
  cases z with
  | inl d =>
      rw [outerRawRetraction_inl]
      change adjunctionCell (cellBoundaryInclusion n) φ (outerPushCell n 1 d) = _
      rw [outerPushCell_one_of_gt n d hz]
      exact adjunction_coherence (cellBoundaryInclusion n) φ _
  | inr x =>
      rw [outerRawRetraction_inr]
      rfl

theorem outerRawRetraction_factorsThrough
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X) :
    Function.FactorsThrough (outerRawRetraction n φ) (outerAdjunctionMk n φ) := by
  intro z w hzw
  apply adjunctionLower_injective n φ
  rw [← outerPush_one_eq_lower_outerRawRetraction n φ z,
    ← outerPush_one_eq_lower_outerRawRetraction n φ w]
  exact congrArg (fun q : outer n φ => outerPush n φ (1, (q : CellAdjunctionSpace n φ))) hzw

noncomputable def outerAdjunctionMkContinuousMap
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X) :
    C(rawOuter n φ, outer n φ) :=
  ⟨outerAdjunctionMk n φ, continuous_outerAdjunctionMk n φ⟩

noncomputable def outerRawRetractionContinuousMap
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) : C(rawOuter n φ, X) :=
  ⟨outerRawRetraction n φ, continuous_outerRawRetraction n φ hφ⟩

theorem isQuotientMap_outerAdjunctionMkContinuousMap
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X) :
    Topology.IsQuotientMap ⇑(outerAdjunctionMkContinuousMap n φ) :=
  isQuotientMap_outerAdjunctionMk n φ

theorem outerRawRetractionContinuousMap_factorsThrough
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) :
    Function.FactorsThrough ⇑(outerRawRetractionContinuousMap n φ hφ)
      ⇑(outerAdjunctionMkContinuousMap n φ) :=
  outerRawRetraction_factorsThrough n φ

noncomputable def outerRetraction {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) (hφ : Continuous φ) : C(outer n φ, X) :=
  (isQuotientMap_outerAdjunctionMkContinuousMap n φ).lift
    (outerRawRetractionContinuousMap n φ hφ)
    (outerRawRetractionContinuousMap_factorsThrough n φ hφ)

theorem outerRetraction_comp_outerAdjunctionMk
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) :
    (outerRetraction n φ hφ).comp
      (outerAdjunctionMkContinuousMap n φ) =
        outerRawRetractionContinuousMap n φ hφ := by
  exact (isQuotientMap_outerAdjunctionMkContinuousMap n φ).lift_comp _ _

noncomputable def outerLower {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : C(X, outer n φ) where
  toFun x := ⟨adjunctionLower φ x, by
    change (1 / 3 : ℝ) < 1
    norm_num⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_adjunctionLower (cellBoundaryInclusion n) φ) _

@[simp] theorem outerRetraction_outerLower
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) (x : X) :
    outerRetraction n φ hφ (outerLower n φ x) = x := by
  let z : rawOuter n φ := ⟨Sum.inr x, by
    change (1 / 3 : ℝ) < 1
    norm_num⟩
  have hcomp := ContinuousMap.congr_fun
    (outerRetraction_comp_outerAdjunctionMk n φ hφ)
    z
  change outerRetraction n φ hφ (outerAdjunctionMk n φ z) =
    outerRawRetraction n φ z at hcomp
  have hlower : outerLower n φ x = outerAdjunctionMk n φ z := by
    apply Subtype.ext
    rfl
  rw [hlower, hcomp]
  exact outerRawRetraction_inr n φ x z.2

theorem outerPush_one_eq_lower_outerRetraction
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) (q : outer n φ) :
    outerPush n φ (1, (q : CellAdjunctionSpace n φ)) =
      adjunctionLower φ (outerRetraction n φ hφ q) := by
  obtain ⟨z, rfl⟩ := (isQuotientMap_outerAdjunctionMk n φ).surjective q
  have hcomp := ContinuousMap.congr_fun
    (outerRetraction_comp_outerAdjunctionMk n φ hφ) z
  change outerRetraction n φ hφ (outerAdjunctionMk n φ z) =
    outerRawRetraction n φ z at hcomp
  rw [hcomp]
  exact outerPush_one_eq_lower_outerRawRetraction n φ z

noncomputable def outerHomotopyEquiv
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) : X ≃ₕ outer n φ where
  toFun := outerLower n φ
  invFun := outerRetraction n φ hφ
  left_inv := by
    rw [show (outerRetraction n φ hφ).comp (outerLower n φ) =
        ContinuousMap.id X by
      ext x
      exact outerRetraction_outerLower n φ hφ x]
  right_inv := by
    let H : ContinuousMap.Homotopy (ContinuousMap.id (outer n φ))
        ((outerLower n φ).comp (outerRetraction n φ hφ)) := {
      toContinuousMap := ⟨outerPushRestricted n φ, continuous_outerPushRestricted n φ⟩
      map_zero_left := outerPushRestricted_zero n φ
      map_one_left := by
        intro q
        apply Subtype.ext
        exact outerPush_one_eq_lower_outerRetraction n φ hφ q
    }
    exact ⟨H.symm⟩

end DifferentialGeometry.Topology.CellAttachment
