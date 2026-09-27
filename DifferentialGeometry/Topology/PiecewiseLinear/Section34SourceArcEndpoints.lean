/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphSimplexCofaces
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceCutOrder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

private theorem exists_pair_markedPoint_cutStep_edgeArc
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (i : Section34EdgeArcIndex 𝒦 𝒦') :
    ∃ p q : Section34MarkIndex 𝒦 𝒦', p ≠ q ∧
      Section34CutStep (.markedPoint p) (.edgeArc i) ∧
      Section34CutStep (.markedPoint q) (.edgeArc i) := by
  classical
  obtain ⟨-, hsub, hmap, -⟩ := hcut
  have hgraph : convexHull ℝ (i.1.2.1 : Set Ea) ⊆
      ⋃ q ∈ {q : Finset Ea | q ∈ 𝒦.complex.faces ∧ q.card ≤ 2},
        convexHull ℝ (q : Set Ea) := by
    intro x hx
    have hxK := hsub.1.le (𝒦'.complex.convexHull_subset_space i.1.2.2.1 hx)
    have hxg := i.1.2.2.2.2 (show 𝒦'.map x ∈ simplexBody 𝒦' i.1.2.1 from ⟨x, hx, rfl⟩)
    rw [hmap] at hxg
    obtain ⟨q, ⟨hq, hqc⟩, y, hy, hyx⟩ := mem_iUnion₂.mp hxg
    have hyx' := 𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space hq hy) hxK hyx
    exact mem_iUnion₂.mpr ⟨q, ⟨hq, hqc⟩, hyx' ▸ hy⟩
  have het : convexHull ℝ (i.1.2.1 : Set Ea) ⊆ convexHull ℝ (i.1.1.1 : Set Ea) :=
    convexHull_min i.2 (convex_convexHull ℝ _)
  obtain ⟨s, t, hs, ht, hsc, htc, hst, hsi, hti, hes, het'⟩ :=
    hsub.exists_two_triangles_over_graph_simplex i.1.2.2.1 i.1.1.2.1 i.1.1.2.2 hgraph het
  let s' : Section34SimplexIndex 𝒦 3 := ⟨s, hs, hsc⟩
  let t' : Section34SimplexIndex 𝒦 3 := ⟨t, ht, htc⟩
  let p : Section34MarkIndex 𝒦 𝒦' :=
    ⟨(s', i.1.2), (subset_convexHull ℝ _).trans hes⟩
  let q : Section34MarkIndex 𝒦 𝒦' :=
    ⟨(t', i.1.2), (subset_convexHull ℝ _).trans het'⟩
  refine ⟨p, q, ?_, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩
  · intro hpq
    exact hst (congrArg (fun r : Section34MarkIndex 𝒦 𝒦' => r.1.1.1) hpq)
  · exact (Finset.coe_subset.mpr hsi).trans (subset_convexHull ℝ _)
  · exact (Finset.coe_subset.mpr hti).trans (subset_convexHull ℝ _)

theorem Section34CutFrame.markedPoint_subset_edgeArc_iff
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (p : Section34MarkIndex 𝒦 𝒦') (i : Section34EdgeArcIndex 𝒦 𝒦') :
    src (.markedPoint p) ⊆ src (.edgeArc i) ↔
      p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1 := by
  constructor
  · intro hp
    obtain ⟨-, -, -, hcell, hbd, -, hdim, -⟩ := id hcut
    have hmarkedBd (q : Section34MarkIndex 𝒦 𝒦')
        (hq : src (.markedPoint q) ⊆ src (.edgeArc i)) :
        src (.markedPoint q) ⊆ srcBd (.edgeArc i) := by
      rw [hbd]
      exact fun x hx => mem_iUnion₂.mpr ⟨.markedPoint q, ⟨hq, by simp⟩, hx⟩
    have hpointEq (q r : Section34MarkIndex 𝒦 𝒦')
        (hqr : src (.markedPoint q) = src (.markedPoint r)) : q = r := by
      rcases hdim (.markedPoint r) (.markedPoint q) hqr.subset with heq | hlt
      · exact Section34Label.markedPoint.inj heq
      · simp only [section34Dim, lt_self_iff_false] at hlt
    obtain ⟨p₁, p₂, hp₁₂, hs₁, hs₂⟩ := exists_pair_markedPoint_cutStep_edgeArc hcut i
    have hchoice := (hcell (.edgeArc i)).eq_or_eq_of_subset_boundary
      (hcell (.markedPoint p)) (hcell (.markedPoint p₁)) (hcell (.markedPoint p₂))
      (hmarkedBd p hp) (hmarkedBd p₁ (hcut.src_subset_of_cutStep hs₁))
      (hmarkedBd p₂ (hcut.src_subset_of_cutStep hs₂)) (fun h => hp₁₂ (hpointEq p₁ p₂ h))
    rcases hchoice with heq | heq
    · have hpp₁ := hpointEq p p₁ heq
      subst p
      exact hs₁
    · have hpp₂ := hpointEq p p₂ heq
      subst p
      exact hs₂
  · intro hp
    exact hcut.src_subset_of_cutStep (show Section34CutStep (.markedPoint p) (.edgeArc i) from hp)

end DifferentialGeometry.Topology.PiecewiseLinear
