/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCarrying

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactFaceBallInvariants.trace_circle_separates_other_face_torus
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {s t : Section34CompactSimplexIndex K 3} (hst : s ≠ t)
    (w : Section34CompactVertexIndex K K') (hwt : Section34Incident w.1 t.1)
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v)) :
    ¬ IsPreconnected
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) t) \ J) := by
  intro hnonsep
  let T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) t
  have hVT : section34CompactVertexBallImage src f₁ w ⊆ T :=
    fun x hx => mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hx⟩
  have hTN : T ⊆ ⋃ v, section34CompactVertexBallImage src f₁ v := by
    intro x hx
    obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
  have hJT : J ⊆ T := hJV.trans hVT
  have hJΘ : J ⊆ frontier T := by
    intro x hx
    exact ⟨subset_closure (hJT hx), fun hxi => (hJN hx).2 (interior_mono hTN hxi)⟩
  obtain ⟨-, hf₁, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest t
  obtain ⟨n, L, -, hL, -, -, hLT, -, k, hk, hkc⟩ :=
    exists_positive_finite_compact_trace_circles hcut hgraph hinv t
  have hLP : L k ⊆ fbl t := by
    intro x hx
    exact (hinv.1 t).boundary_subset (hLT.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)).1
  have hLΘ : L k ⊆ frontier T := by
    intro x hx
    exact (hLT.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)).2
  have hJL : Disjoint J (L k) := by
    apply Set.disjoint_left.mpr
    intro x hxJ hxL
    exact (hJN hxJ).2
      (hinv.2.2.2.1 s t hst ⟨(hinv.1 s).boundary_subset (hJP hxJ), hLP hxL⟩)
  have hΘT : id '' frontier T ⊆ T := by
    simpa only [image_id] using hT.isPolyhedron.isClosed.frontier_subset
  have hkc' : CarriesFirstHomologyOnto (id '' L k) T := by
    simpa only [image_id] using hkc
  have hJcarry : CarriesFirstHomologyOnto J T := by
    have hc := hT.isPLTorus_frontier.carriesFirstHomologyOnto_image_of_disjoint
      (hL k) hLΘ hJ hJΘ hJL hk hnonsep continuous_id.continuousOn
      (fun _ _ _ _ heq => heq) hΘT hkc'
    simpa only [image_id] using hc
  have hnull := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three.nullhomotopic_inclusion
    hJV hVT
  have hzero := integralSingularHomologyMap_nullhomotopic 1 one_ne_zero hnull
  let _ := hT.1.nontrivial_integralSingularHomology_one
  obtain ⟨z, hz⟩ := exists_ne (0 : integralSingularHomology 1 T)
  obtain ⟨x, hx⟩ := hJcarry.2 hJT z
  rw [hzero, LinearMap.zero_apply] at hx
  exact hz hx.symm

end DifferentialGeometry.Topology.PiecewiseLinear
