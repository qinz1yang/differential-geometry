/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ControlledGraphCore
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceRimTori
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterTorusCarriers

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [T2Space M₁] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {H : Finset Ea → Set M₂}

theorem exists_section34_controlled_graph_neighborhood_with_outer_tori
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (hH : Section34CarrierControl U 𝒦 h η H) (hW : IsOpen W)
    (hΓW : graphSkeletonSpace 𝒦 ⊆ W)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
      (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (ct : Section34SimplexIndex 𝒦 3 →
        OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
      (Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
      IsCombinatorialManifold 3 𝒦'.complex ∧
      (∀ w, IsPLCellOn 3 (section34GraphVertexCell 𝒦 𝒦' w)
        (section34GraphVertexBoundary 𝒦 𝒦' w)) ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3)
        (⋃ w, section34GraphVertexCell 𝒦 𝒦' w) (graphSkeletonSpace 𝒦) U ∧
      (⋃ w, section34GraphVertexCell 𝒦 𝒦' w) ⊆ W ∧
      (∀ x ∈ U, ∃ V ∈ 𝓝 x, {w : Section34VertexIndex 𝒦 𝒦' |
        (section34GraphVertexCell 𝒦 𝒦' w ∩ V).Nonempty}.Finite) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ section34GraphVertexCell 𝒦 𝒦' w) ∧
      (∀ w, car w ∈ 𝒦.complex.faces) ∧
      (∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
      (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
      (∀ w, h '' section34GraphVertexCell 𝒦 𝒦' w ⊆ interior (Q w)) ∧
      (∀ w, Q w ⊆ H (car w)) ∧
      (∀ w, ∀ x ∈ section34GraphVertexCell 𝒦 𝒦' w, ∀ y ∈ Q w, ∀ z ∈ Q w,
        dist y z < ψ x) ∧
      (∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
        (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1) ∧
      (∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
        Section34Incident w.1 s.1 → Q w ⊆ interior (H s.1)) ∧
      Section34OuterTorus 𝒦 𝒦' h Q ct Sd := by
  obtain ⟨ct, Sd, B, hct, hspine, hB, hrim, -, hBc, hBS⟩ :=
    exists_section34_source_rim_tori hU hh 𝒦 h𝒦 hH
  obtain ⟨𝒦', car, hsub, hmap, hman, hcell, hN, hNW, hlf, hmarker, -, hcar, -, hCcar,
    hfinite, -, -, hCB, hsmall⟩ :=
    exists_section34_controlled_graph_core hU 𝒦 h𝒦 hW hΓW
      (continuousOn_iff_continuous_domRestrict.mpr hh.continuous) B hB hrim ψ hψc hψpos
  have hbuffer : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident w.1 s.1 → h '' section34GraphVertexCell 𝒦 𝒦' w ⊆
        (ct s).source ∩ (ct s) ⁻¹' interior (Sd s) := by
    intro w s hws y hy
    have hyB := image_mono (hCB w s hws) hy
    exact ⟨hBc s hyB, hBS s (mem_image_of_mem (ct s) hyB)⟩
  obtain ⟨Q, hQ, htorus⟩ := exists_section34_outer_torus_carriers hU hh hH.1 hsub hmap
    hman.isCombinatorialManifoldWithBoundary car hcar hCcar ψ hψc hsmall ct
    (fun s => (hct s).1) Sd hspine hbuffer
  exact ⟨𝒦', car, Q, ct, Sd, hsub, hmap, hman, hcell, hN, hNW, hlf, hmarker, hcar,
    hCcar, hfinite, fun w => (hQ w).2.1, fun w => (hQ w).2.2.1,
    fun w => (hQ w).2.2.2.1, fun w => (hQ w).2.2.2.2.1,
    fun w => (hQ w).2.2.2.2.2, htorus⟩

end DifferentialGeometry.Topology.PiecewiseLinear
