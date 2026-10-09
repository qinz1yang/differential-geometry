/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexIncidentFacesFinite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {H : Finset Ea → Set M₂} {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem finite_section34Trace_inter_vertex_rim
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') {R : Set M₂}
    (hRV : R ⊆ section34VertexBallImage src f₁ w)
    (hRE : R ⊆ section34SplitDiskImage srcBd f₁ e) :
    (R ∩ ⋃ t : Section34SimplexIndex 𝒦 3, fblBd t).Finite := by
  have hfaces := finite_setOf_section34Faces_incident_vertex hcut.2.1 w 3
  have hfinite := hinv.2.2.2.2.2.2.2.1
  have hfin : (⋃ t ∈ {t : Section34SimplexIndex 𝒦 3 | Section34Incident w.1 t.1},
      fblBd t ∩ ⋃ d : Section34EdgeIndex 𝒦 𝒦', section34SplitDiskImage srcBd f₁ d).Finite :=
    hfaces.biUnion fun t _ => hfinite t
  apply hfin.subset
  rintro x ⟨hxR, hxF⟩
  obtain ⟨t, hxt⟩ := mem_iUnion.mp hxF
  have hwt : Section34Incident w.1 t.1 := by
    by_contra hnot
    exact notMem_empty x (hinv.2.2.1 t w hnot ▸
      ⟨(hinv.1 t).boundary_subset hxt, hRV hxR⟩)
  exact mem_iUnion₂.mpr ⟨t, hwt, hxt, mem_iUnion.mpr ⟨e, hRE hxR⟩⟩

omit [FiniteDimensional ℝ Ea] in
theorem finite_section34Trace_inter_model_vertex_rim
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    {P R : Set E3} {u : E3 → M₂} (hu : InjOn u P) (hRP : R ⊆ P)
    (hRV : R ⊆ u ⁻¹' section34VertexBallImage src f₁ w)
    (hRE : R ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e) :
    (R ∩ ⋃ t : Section34SimplexIndex 𝒦 3, u ⁻¹' fblBd t).Finite := by
  have hfin := finite_section34Trace_inter_vertex_rim hcut hinv w e
    (image_subset_iff.mpr hRV) (image_subset_iff.mpr hRE)
  apply Set.Finite.of_finite_image (f := u) (hfin.subset ?_)
    (hu.mono (inter_subset_left.trans hRP))
  rintro y ⟨x, hx, rfl⟩
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  obtain ⟨t, hxt⟩ := mem_iUnion.mp hx.2
  exact mem_iUnion.mpr ⟨t, hxt⟩

end DifferentialGeometry.Topology.PiecewiseLinear
