/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellInteriorImage
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexMarkerInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [T2Space M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_source_target_vertex_interiors_meet
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hsep : ∀ w w', w ≠ w' →
      Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w'))
    (hDvsub : ∀ w, Dv w ⊆ G w '' Cp w)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦))
    (w : Section34VertexIndex 𝒦 𝒦') :
    (h '' interior (src (.vertexBall w)) ∩ interior (Dv w)).Nonempty := by
  classical
  obtain ⟨-, -, -, hcell, -, -, -, -, hcover, -, -, -, -, -, -, -, -, -, -, -,
    hvertex, -, -, -, -⟩ := hframe
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp w.2.2.1
  have haw : a ∈ w.1 := by rw [ha]; simp
  let x : M₁ := 𝒦'.map a
  have hxbody : x ∈ simplexBody 𝒦' w.1 :=
    ⟨a, subset_convexHull ℝ _ haw, rfl⟩
  have hxsrc : x ∈ src (.vertexBall w) := hvertex w hxbody
  have hxU : x ∈ U := hcover ▸ mem_iUnion.mpr ⟨.vertexBall w, hxsrc⟩
  have hcontU : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hcont : ContinuousAt h x := hcontU.continuousAt (hU.mem_nhds hxU)
  have hmark : h x ∈ interior (Dv w) :=
    section34_vertex_marker_interior_of_deleted_family
      hsep hDvsub hDv hDvQ hQlf hDnbhd w ⟨x, hxbody, rfl⟩
  exact (hcell (.vertexBall w)).exists_image_interior_mem_open
    hxsrc hcont isOpen_interior hmark

end DifferentialGeometry.Topology.PiecewiseLinear
