/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CornerRounding
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold

def halfOpenStrip : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

noncomputable def halfOpenStripReflection : halfOpenStrip ≃ₜ halfOpenStrip where
  toFun p := ⟨(p.val.1, 1 - p.val.2), p.property.1, p.property.2.1,
    by linarith [p.property.2.2.2], by linarith [p.property.2.2.1]⟩
  invFun p := ⟨(p.val.1, 1 - p.val.2), p.property.1, p.property.2.1,
    by linarith [p.property.2.2.2], by linarith [p.property.2.2.1]⟩
  left_inv p := by apply Subtype.ext; refine Prod.ext rfl ?_; dsimp; ring
  right_inv p := by apply Subtype.ext; refine Prod.ext rfl ?_; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def stripCornerMap (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(cornerSquaring p).1, (cornerSquaring p).2]

noncomputable def stripCornerRoot (q : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  cornerRoot (q 0, q 1)

theorem continuous_stripCornerMap : Continuous stripCornerMap := by
  unfold stripCornerMap cornerSquaring
  fun_prop

theorem continuous_stripCornerRoot : Continuous stripCornerRoot :=
  continuous_cornerRoot.comp (by fun_prop)

theorem stripCornerRoot_map {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    stripCornerRoot (stripCornerMap p) = p :=
  cornerRoot_cornerSquaring hp

theorem stripCornerMap_root {q : EuclideanSpace ℝ (Fin 2)} (hq : 0 ≤ q 0) :
    stripCornerMap (stripCornerRoot q) = q := by
  have h := cornerSquaring_cornerRoot (p := (q 0, q 1)) hq
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

private noncomputable def stripCornerInv (q : EuclideanHalfSpace 2) : halfOpenStrip :=
  if h : (stripCornerRoot q.val).1 < 1 ∧ (stripCornerRoot q.val).2 ≤ 1 then
    ⟨stripCornerRoot q.val, (cornerRoot_nonneg _).1, h.1, (cornerRoot_nonneg _).2, h.2⟩
  else ⟨(0, 0), by norm_num [halfOpenStrip]⟩

private theorem stripCornerInv_val {q : EuclideanHalfSpace 2}
    (hq : (stripCornerRoot q.val).1 < 1 ∧ (stripCornerRoot q.val).2 < 1) :
    (stripCornerInv q).val = stripCornerRoot q.val := by
  simp [stripCornerInv, hq.1, hq.2.le]

noncomputable def halfOpenStripLowerChart :
    OpenPartialHomeomorph halfOpenStrip (EuclideanHalfSpace 2) where
  toFun p := ⟨stripCornerMap p.val,
    mul_nonneg (mul_nonneg (by norm_num) p.property.1) p.property.2.2.1⟩
  invFun := stripCornerInv
  source := {p | p.val.2 < 1}
  target := {q | (stripCornerRoot q.val).1 < 1 ∧ (stripCornerRoot q.val).2 < 1}
  map_source' p hp := by
    change (stripCornerRoot (stripCornerMap p.val)).1 < 1 ∧
      (stripCornerRoot (stripCornerMap p.val)).2 < 1
    rw [stripCornerRoot_map ⟨p.property.1, p.property.2.2.1⟩]
    exact ⟨p.property.2.1, hp⟩
  map_target' q hq := by
    change (stripCornerInv q).val.2 < 1
    rw [stripCornerInv_val hq]
    exact hq.2
  left_inv' p hp := by
    apply Subtype.ext
    have hr := stripCornerRoot_map ⟨p.property.1, p.property.2.2.1⟩
    change (stripCornerInv ⟨stripCornerMap p.val, _⟩).val = p.val
    rw [stripCornerInv_val (by rw [hr]; exact ⟨p.property.2.1, hp⟩)]
    exact hr
  right_inv' q hq := by
    apply Subtype.ext
    change stripCornerMap (stripCornerInv q).val = q.val
    rw [stripCornerInv_val hq]
    exact stripCornerMap_root q.property
  open_source := isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const
  open_target :=
    (isOpen_lt ((continuous_stripCornerRoot.comp continuous_subtype_val).fst)
      continuous_const).inter
      (isOpen_lt ((continuous_stripCornerRoot.comp continuous_subtype_val).snd)
        continuous_const)
  continuousOn_toFun := by
    exact ((continuous_stripCornerMap.comp continuous_subtype_val).subtype_mk _).continuousOn
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have h : Continuous (fun q : {q : EuclideanHalfSpace 2 |
        (stripCornerRoot q.val).1 < 1 ∧ (stripCornerRoot q.val).2 < 1} =>
        stripCornerRoot q.val.val) := continuous_stripCornerRoot.comp
      (continuous_subtype_val.comp continuous_subtype_val)
    exact h.congr (fun q => (stripCornerInv_val q.property).symm)

noncomputable def halfOpenStripChart (upper : Bool) :
    OpenPartialHomeomorph halfOpenStrip (EuclideanHalfSpace 2) :=
  if upper then halfOpenStripReflection.toOpenPartialHomeomorph.trans halfOpenStripLowerChart
  else halfOpenStripLowerChart

theorem mem_halfOpenStripChart_source (p : halfOpenStrip) (upper : Bool) :
    p ∈ (halfOpenStripChart upper).source ↔ if upper then 0 < p.val.2 else p.val.2 < 1 := by
  cases upper
  · rfl
  · change (True ∧ 1 - p.val.2 < 1) ↔ 0 < p.val.2
    constructor
    · intro h; linarith [h.2]
    · intro h; exact ⟨trivial, by linarith⟩

theorem halfOpenStripChart_cover (p : halfOpenStrip) :
    ∃ upper : Bool, p ∈ (halfOpenStripChart upper).source := by
  by_cases h : p.val.2 < 1
  · exact ⟨false, (mem_halfOpenStripChart_source p false).mpr h⟩
  · refine ⟨true, (mem_halfOpenStripChart_source p true).mpr ?_⟩
    simp only [↓reduceIte]
    linarith

@[instance_reducible]
noncomputable def halfOpenStripChartedSpace :
    ChartedSpace (EuclideanHalfSpace 2) halfOpenStrip where
  atlas := range halfOpenStripChart
  chartAt p := halfOpenStripChart (halfOpenStripChart_cover p).choose
  mem_chart_source p := (halfOpenStripChart_cover p).choose_spec
  chart_mem_atlas _ := mem_range_self _

theorem contDiff_stripCornerMap : ContDiff ℝ ∞ stripCornerMap := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i <;> dsimp [stripCornerMap, cornerSquaring] <;> fun_prop

noncomputable def stripCornerTransition (q : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  stripCornerMap ((stripCornerRoot q).1, 1 - (stripCornerRoot q).2)

theorem contDiffWithinAt_stripCornerTransition {q : EuclideanSpace ℝ (Fin 2)}
    (hq : 0 ≤ q 0) (hne : (q 0, q 1) ≠ 0) :
    ContDiffWithinAt ℝ ∞ stripCornerTransition {z | 0 ≤ z 0} q := by
  have hr := (contDiffWithinAt_cornerRoot hq hne).comp q
    (show ContDiffWithinAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1))
      {z | 0 ≤ z 0} q from by fun_prop) (fun _ h => h)
  change ContDiffWithinAt ℝ ∞ stripCornerRoot {z | 0 ≤ z 0} q at hr
  exact contDiff_stripCornerMap.comp_contDiffWithinAt
    (hr.fst.prodMk (contDiffWithinAt_const.sub hr.snd))

theorem halfOpenStripChart_transition_eq (i j : Bool) (hij : i ≠ j)
    (q : EuclideanHalfSpace 2) (hq : q ∈ (halfOpenStripChart i).target) :
    ((halfOpenStripChart j) ((halfOpenStripChart i).symm q)).val =
      stripCornerTransition q.val := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · change stripCornerMap ((stripCornerInv q).val.1, 1 - (stripCornerInv q).val.2) = _
    rw [stripCornerInv_val hq]
    rfl
  · change stripCornerMap ((stripCornerInv q).val.1, 1 - (stripCornerInv q).val.2) = _
    rw [stripCornerInv_val hq.1]
    rfl
  · exact (hij rfl).elim

theorem halfOpenStripChart_overlap_root_pos (i j : Bool) (hij : i ≠ j)
    {q : EuclideanHalfSpace 2}
    (hq : q ∈ ((halfOpenStripChart i).symm.trans (halfOpenStripChart j)).source) :
    0 < (stripCornerRoot q.val).2 := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · have ht := (mem_halfOpenStripChart_source _ true).mp hq.2
    change 0 < (stripCornerInv q).val.2 at ht
    rwa [stripCornerInv_val hq.1] at ht
  · have ht := (mem_halfOpenStripChart_source _ false).mp hq.2
    change 1 - (stripCornerInv q).val.2 < 1 at ht
    rw [stripCornerInv_val hq.1.1] at ht
    linarith
  · exact (hij rfl).elim

theorem halfOpenStripChart_transition_contDiffOn (i j : Bool) :
    ContDiffOn ℝ ∞
      ((𝓡∂ 2) ∘ ((halfOpenStripChart i).symm.trans (halfOpenStripChart j)) ∘ (𝓡∂ 2).symm)
      ((𝓡∂ 2).symm ⁻¹' ((halfOpenStripChart i).symm.trans (halfOpenStripChart j)).source ∩
        range (𝓡∂ 2)) := by
  by_cases hij : i = j
  · subst j
    apply contDiffOn_id.congr
    intro q hq
    change (((halfOpenStripChart i) ((halfOpenStripChart i).symm ((𝓡∂ 2).symm q))).val) = q
    rw [(halfOpenStripChart i).right_inv hq.1.1]
    exact (𝓡∂ 2).right_inv hq.2
  · have ht : ContDiffOn ℝ ∞ stripCornerTransition
        ((𝓡∂ 2).symm ⁻¹' ((halfOpenStripChart i).symm.trans (halfOpenStripChart j)).source ∩
          range (𝓡∂ 2)) := by
      intro q hq
      have hv : ((𝓡∂ 2).symm q).val = q := (𝓡∂ 2).right_inv hq.2
      have hn : 0 ≤ q 0 := by
        rw [← hv]
        exact ((𝓡∂ 2).symm q).property
      have hpos := halfOpenStripChart_overlap_root_pos i j hij hq.1
      rw [hv] at hpos
      have hne : (q 0, q 1) ≠ 0 := by
        intro heq
        change 0 < (cornerRoot (q 0, q 1)).2 at hpos
        rw [heq] at hpos
        norm_num [cornerRoot] at hpos
      apply (contDiffWithinAt_stripCornerTransition hn hne).mono
      rintro z ⟨_, w, rfl⟩
      exact w.property
    apply ht.congr
    intro q hq
    change (((halfOpenStripChart j) ((halfOpenStripChart i).symm ((𝓡∂ 2).symm q))).val) = _
    rw [halfOpenStripChart_transition_eq i j hij _ hq.1.1]
    rw [show ((𝓡∂ 2).symm q).val = q from (𝓡∂ 2).right_inv hq.2]

theorem halfOpenStrip_isManifold :
    let _ := halfOpenStripChartedSpace
    IsManifold (𝓡∂ 2) ∞ halfOpenStrip := by
  let _ := halfOpenStripChartedSpace
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  exact halfOpenStripChart_transition_contDiffOn i j

theorem halfOpenStripChart_attaching_iff (p : halfOpenStrip) (i : Bool) :
    p.val.1 = 0 ↔
      (halfOpenStripChart i p).val 0 = 0 ∧ (halfOpenStripChart i p).val 1 ≤ 0 := by
  cases i
  · exact (cornerSquaring_first_face_iff ⟨p.property.1, p.property.2.2.1⟩).symm
  · exact (cornerSquaring_first_face_iff
      (p := (p.val.1, 1 - p.val.2))
      ⟨p.property.1, by linarith [p.property.2.2.2]⟩).symm

theorem halfOpenStripChart_normal_zero_iff (p : halfOpenStrip) (i : Bool)
    (hp : p ∈ (halfOpenStripChart i).source) :
    (halfOpenStripChart i p).val 0 = 0 ↔
      p.val.1 = 0 ∨ p.val.2 = 0 ∨ p.val.2 = 1 := by
  have hs := (mem_halfOpenStripChart_source p i).mp hp
  cases i
  · change 2 * p.val.1 * p.val.2 = 0 ↔ _
    have ht : p.val.2 ≠ 1 := ne_of_lt hs
    simp [mul_eq_zero, ht]
  · change 2 * p.val.1 * (1 - p.val.2) = 0 ↔ _
    have ht : p.val.2 ≠ 0 := ne_of_gt hs
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ht, false_or,
      sub_eq_zero, eq_comm (a := (1 : ℝ))]

theorem halfOpenStrip_boundary_iff (p : halfOpenStrip) :
    let _ := halfOpenStripChartedSpace
    p ∈ (𝓡∂ 2).boundary halfOpenStrip ↔
      p.val.1 = 0 ∨ p.val.2 = 0 ∨ p.val.2 = 1 := by
  let _ := halfOpenStripChartedSpace
  dsimp only
  change (𝓡∂ 2).IsBoundaryPoint p ↔ _
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = (halfOpenStripChart (halfOpenStripChart_cover p).choose p).val 0 ↔ _
  rw [eq_comm]
  exact halfOpenStripChart_normal_zero_iff p _ (halfOpenStripChart_cover p).choose_spec

end DifferentialGeometry.Manifold
