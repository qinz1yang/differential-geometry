/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Compactness.LocallyFiniteClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

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
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_vertex_marker_interior_of_deleted_family
    (hsep : ∀ w w', w ≠ w' →
      Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w'))
    (hDvsub : ∀ w, Dv w ⊆ G w '' Cp w)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (Dv w) := by
  intro w y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxgraph : x ∈ graphSkeletonSpace 𝒦 := w.2.2.2 hx
  have hnear : h x ∈ interior (⋃ v, Dv v) :=
    (subset_interior_iff_mem_nhdsSet.mpr hDnbhd) ⟨x, hxgraph, rfl⟩
  have hQy : h x ∈ ⋃ v, Q v := by
    obtain ⟨v, hv⟩ := mem_iUnion.mp (interior_subset hnear)
    exact mem_iUnion.mpr ⟨v, hDvQ v hv⟩
  have hother (v : Section34VertexIndex 𝒦 𝒦') (hv : v ≠ w) : h x ∉ Dv v := by
    intro hyv
    exact disjoint_left.mp (hsep w v hv.symm)
      ⟨x, hx, rfl⟩ (hDvsub v hyv)
  exact DifferentialGeometry.Topology.mem_interior_of_locally_finite_closed_cover_unique
    (D := Dv) (Q := Q) (i₀ := w)
    (fun v => (hDv v).isCompact.isClosed) hDvQ
    (hQlf (h x) hQy) hother hnear

end DifferentialGeometry.Topology.PiecewiseLinear
