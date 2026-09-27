/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphSimplexCofaces
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

private theorem exists_pair_markedPoint_cutStep_edgeArc
    (hcut : Section34CompactCutFrame C K K' src srcBd) (i : Section34CompactEdgeArcIndex K K') :
    ∃ p q : Section34CompactMarkIndex K K', p ≠ q ∧
      Section34CompactCutStep (.markedPoint p) (.edgeArc i) ∧
      Section34CompactCutStep (.markedPoint q) (.edgeArc i) := by
  classical
  obtain ⟨-, -, -, -, hsub, -⟩ := hcut
  have hgraph := i.1.2.2.2.2
  have het : convexHull ℝ (i.1.2.1 : Set E3) ⊆ convexHull ℝ (i.1.1.1 : Set E3) :=
    convexHull_min i.2 (convex_convexHull ℝ _)
  obtain ⟨s, t, hs, ht, hsc, htc, hst, hsi, hti, hes, het'⟩ :=
    hsub.exists_two_triangles_over_graph_simplex i.1.2.2.1 i.1.1.2.1 i.1.1.2.2 hgraph het
  let s' : Section34CompactSimplexIndex K 3 := ⟨s, hs, hsc⟩
  let t' : Section34CompactSimplexIndex K 3 := ⟨t, ht, htc⟩
  let p : Section34CompactMarkIndex K K' :=
    ⟨(s', i.1.2), (subset_convexHull ℝ _).trans hes⟩
  let q : Section34CompactMarkIndex K K' :=
    ⟨(t', i.1.2), (subset_convexHull ℝ _).trans het'⟩
  refine ⟨p, q, ?_, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩
  · intro hpq
    exact hst (congrArg (fun r : Section34CompactMarkIndex K K' => r.1.1.1) hpq)
  · exact (Finset.coe_subset.mpr hsi).trans (subset_convexHull ℝ _)
  · exact (Finset.coe_subset.mpr hti).trans (subset_convexHull ℝ _)

private theorem markedPoint_subset_edgeArc_of_step
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {p : Section34CompactMarkIndex K K'} {i : Section34CompactEdgeArcIndex K K'}
    (hstep : Section34CompactCutStep (.markedPoint p) (.edgeArc i)) :
    src (.markedPoint p) ⊆ src (.edgeArc i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmark, -, hedge, -, -, -, -, -, -, -, -, -, -, -, -,
    hface, -⟩ := hcut
  rcases hstep with ⟨he, hi⟩
  rw [hmark p, hedge i]
  exact fun x hx => ⟨hface i.1.1 p.1.1 hi hx.2, he ▸ hx.1⟩

theorem Section34CompactCutFrame.markedPoint_subset_edgeArc_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (p : Section34CompactMarkIndex K K') (i : Section34CompactEdgeArcIndex K K') :
    src (.markedPoint p) ⊆ src (.edgeArc i) ↔
      p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1 := by
  constructor
  · intro hp
    obtain ⟨-, -, -, -, -, -, hcell, hbd, -, hdim, -⟩ := id hcut
    have hmarkedBd (q : Section34CompactMarkIndex K K')
        (hq : src (.markedPoint q) ⊆ src (.edgeArc i)) :
        src (.markedPoint q) ⊆ srcBd (.edgeArc i) := by
      rw [hbd]
      exact fun x hx => mem_iUnion₂.mpr ⟨.markedPoint q, ⟨hq, by simp⟩, hx⟩
    have hpointEq (q r : Section34CompactMarkIndex K K')
        (hqr : src (.markedPoint q) = src (.markedPoint r)) : q = r := by
      rcases hdim (.markedPoint r) (.markedPoint q) hqr.subset with heq | hlt
      · exact Section34BoundedLabel.markedPoint.inj heq
      · simp only [section34BoundedDim, lt_self_iff_false] at hlt
    obtain ⟨p₁, p₂, hp₁₂, hs₁, hs₂⟩ := exists_pair_markedPoint_cutStep_edgeArc hcut i
    have hchoice := (hcell (.edgeArc i)).eq_or_eq_of_subset_boundary
      (hcell (.markedPoint p)) (hcell (.markedPoint p₁)) (hcell (.markedPoint p₂))
      (hmarkedBd p hp) (hmarkedBd p₁ (markedPoint_subset_edgeArc_of_step hcut hs₁))
      (hmarkedBd p₂ (markedPoint_subset_edgeArc_of_step hcut hs₂))
      (fun h => hp₁₂ (hpointEq p₁ p₂ h))
    rcases hchoice with heq | heq
    · have hpp₁ := hpointEq p p₁ heq
      subst p
      exact hs₁
    · have hpp₂ := hpointEq p p₂ heq
      subst p
      exact hs₂
  · intro hp
    exact markedPoint_subset_edgeArc_of_step hcut
      (show Section34CompactCutStep (.markedPoint p) (.edgeArc i) from hp)

end DifferentialGeometry.Topology.PiecewiseLinear
