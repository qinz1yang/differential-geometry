/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFacePoset

/-!
# Source face order of a compact cut frame

This probe isolates facet production, two boundary thinness assertions, and
codimension-one incidence classification. The two directions of the source
order relation follow by finite-dimensional induction.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem exists_facet_above_of_source_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : src m ⊆ src l) (hne : m ≠ l) :
    ∃ k : Section34CompactLabelOf K K',
      section34BoundedDim k + 1 = section34BoundedDim l ∧
        src m ⊆ src k ∧ src k ⊆ src l := by
  sorry

theorem split_disk_boundary_thin
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (e : Section34CompactEdgeIndex K K') (p : Section34CompactMarkIndex K K')
    (hp : src (.markedPoint p) ⊆ srcBd (.splitDisk e)) :
    ∃ a b : Section34CompactLabelOf K K', a ≠ b ∧
      section34BoundedDim a = 1 ∧ section34BoundedDim b = 1 ∧
      src (.markedPoint p) ⊆ src a ∧ src a ⊆ srcBd (.splitDisk e) ∧
      src (.markedPoint p) ⊆ src b ∧ src b ⊆ srcBd (.splitDisk e) ∧
      ∀ c : Section34CompactLabelOf K K', section34BoundedDim c = 1 →
        src (.markedPoint p) ⊆ src c → src c ⊆ srcBd (.splitDisk e) → c = a ∨ c = b := by
  sorry

theorem vertex_ball_boundary_thin
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (w : Section34CompactVertexIndex K K') (r : Section34CompactLabelOf K K')
    (hr : section34BoundedDim r = 1) (hrw : src r ⊆ srcBd (.vertexBall w)) :
    ∃ a b : Section34CompactLabelOf K K', a ≠ b ∧
      section34BoundedDim a = 2 ∧ section34BoundedDim b = 2 ∧
      src r ⊆ src a ∧ src a ⊆ srcBd (.vertexBall w) ∧
      src r ⊆ src b ∧ src b ⊆ srcBd (.vertexBall w) ∧
      ∀ c : Section34CompactLabelOf K K', section34BoundedDim c = 2 →
        src r ⊆ src c → src c ⊆ srcBd (.vertexBall w) → c = a ∨ c = b := by
  sorry

theorem cut_step_iff_codimension_one_source_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'}
    (hd : section34BoundedDim l = section34BoundedDim m + 1) :
    Section34CompactCutStep m l ↔ src m ⊆ src l := by
  sorry

theorem cut_order_of_source_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : src m ⊆ src l) :
    Section34CompactCutLe m l := by
  have aux : ∀ d, ∀ l : Section34CompactLabelOf K K',
      section34BoundedDim l = d → ∀ m, src m ⊆ src l → Section34CompactCutLe m l := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro l hld m hml
        by_cases h : m = l
        · subst m
          exact Relation.ReflTransGen.refl
        obtain ⟨k, hkd, hmk, hkl⟩ := exists_facet_above_of_source_subset hcut hml h
        have hklt : section34BoundedDim k < d := by omega
        have hstep : Section34CompactCutStep k l :=
          (cut_step_iff_codimension_one_source_subset hcut (by omega)).2 hkl
        exact Relation.ReflTransGen.tail (ih _ hklt k rfl m hmk) hstep
  exact aux _ l rfl m hml

theorem source_subset_of_cut_order
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : Section34CompactCutLe m l) :
    src m ⊆ src l := by
  induction hml using Relation.ReflTransGen.head_induction_on with
  | refl => exact subset_rfl
  | @head b c hab hbc ih =>
      exact ((cut_step_iff_codimension_one_source_subset hcut
        (Section34CompactCutStep.dim_succ hab)).1 hab).trans ih

end DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe
