/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BufferedGraphSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphRefinementControl
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphRegularNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [T2Space M₁] {M₂ : Type v} [PseudoMetricSpace M₂] {U W : Set M₁} {h : M₁ → M₂}

theorem exists_section34_controlled_graph_core
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h𝒦 : IsCombinatorialManifold 3 𝒦.complex) (hW : IsOpen W)
    (hΓW : graphSkeletonSpace 𝒦 ⊆ W) (hh : ContinuousOn h U)
    (B : Section34SimplexIndex 𝒦 3 → Set M₁) (hB : ∀ s, IsOpen (B s))
    (hrim : ∀ s, simplexRim 𝒦 s.1 ⊆ B s)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea),
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
      (∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦' w.1) ∧
      (∀ w, car w ∈ 𝒦.complex.faces) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ simplexBody 𝒦 (car w)) ∧
      (∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
      (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
      (∀ w t, t ∈ 𝒦.complex.faces →
        ((section34GraphVertexCell 𝒦 𝒦' w ∩ simplexBody 𝒦 t).Nonempty ↔
          Section34Incident w.1 t)) ∧
      (∀ w t, t ∈ 𝒦.complex.faces → Section34Incident w.1 t →
        section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦 t) ∧
      (∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
        Section34Incident w.1 s.1 → section34GraphVertexCell 𝒦 𝒦' w ⊆ B s) ∧
      ∀ w, ∀ x ∈ section34GraphVertexCell 𝒦 𝒦' w,
        ∀ y ∈ section34GraphVertexCell 𝒦 𝒦' w, ∀ z ∈ section34GraphVertexCell 𝒦 𝒦' w,
          dist (h y) (h z) < ψ x := by
  classical
  obtain ⟨𝒦₀, _, hsub₀, hmap₀, hman₀, _, _, _, _, hW₀, hB₀, hsmall₀⟩ :=
    exists_graph_subdivision_with_image_diameter_and_buffer_control hU 𝒦 h𝒦 hW hΓW hh
      B hB hrim ψ hψc hψpos
  let 𝒦' := 𝒦₀.subdivide (secondDerived 𝒦₀.complex)
    (secondDerived_isSubdivision 𝒦₀.complex) 𝒦₀.locallyFinite_secondDerived
  have hsub' : IsSubdivision 𝒦'.complex 𝒦₀.complex :=
    secondDerived_isSubdivision 𝒦₀.complex
  have hsub : IsSubdivision 𝒦'.complex 𝒦.complex := hsub'.trans hsub₀
  have hmap : 𝒦'.map = 𝒦.map := hmap₀
  have hman := isCombinatorialManifold_of_locallyFinitePLPieceIn hU 𝒦'
  obtain ⟨a, hasupport, haincident⟩ :=
    exists_section34_graph_refinement_control hsub₀ hmap₀ hsub' rfl
  obtain ⟨carF, hcarF, hcontain, hsupp, hfinite⟩ :=
    exists_finite_subdivision_carrier_assignment hsub hmap
  let f : Section34VertexIndex 𝒦 𝒦' → 𝒦'.complex.faces := fun w => ⟨w.1, w.2.1⟩
  have hf : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    exact congrArg (fun s : 𝒦'.complex.faces => s.1) hwz
  let car := carF ∘ f
  have hcell := isPLCellOn_section34GraphVertexCell hsub hmap
    hman.isCombinatorialManifoldWithBoundary
  have hCsupp : ∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦' w.1 :=
    section34GraphVertexCell_subset_carrierSupport
  have hCcoarse : ∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆
      Section34CarrierSupport 𝒦₀ (a w).1 := fun w => (hCsupp w).trans (hasupport w)
  refine ⟨𝒦', car, hsub, hmap, hman, hcell,
    isLocallyFiniteRegularNeighborhoodOf_section34GraphVertexCells hU
      hman₀.isCombinatorialManifoldWithBoundary hsub hmap rfl rfl,
    iUnion_subset (fun w => (hCcoarse w).trans (hW₀ (a w))),
    locallyFinite_section34GraphVertexCell 𝒦 𝒦', simplexBody_subset_section34GraphVertexCell,
    hCsupp, fun w => hcarF (f w), ?_, fun w => (hCsupp w).trans (hsupp (f w)),
    fun t => (hfinite t).preimage hf.injOn, ?_, ?_, ?_, ?_⟩
  · intro w
    change 𝒦'.map '' convexHull ℝ (w.1 : Set Ea) ⊆
      𝒦.map '' convexHull ℝ (car w : Set Ea)
    rw [hmap]
    exact image_mono (hcontain (f w))
  · exact fun w t ht => section34GraphVertexCell_inter_simplexBody_nonempty_iff hsub hmap w ht
  · exact fun w t ht => section34GraphVertexCell_subset_incident_carrierSupport hsub hmap w ht
  · intro w s hws
    exact (hCcoarse w).trans (hB₀ (a w) s (haincident w s.1 s.2.1 hws))
  · intro w x hx y hy z hz
    exact hsmall₀ (a w).1 (a w).2.1 x (hCcoarse w hx) y (hCcoarse w hy)
      z (hCcoarse w hz)

end DifferentialGeometry.Topology.PiecewiseLinear
