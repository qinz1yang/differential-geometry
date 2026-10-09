/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphNeighborhoodSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [T2Space M₁] {M₂ : Type v} [PseudoMetricSpace M₂] {U W : Set M₁} {h : M₁ → M₂}

theorem exists_graph_subdivision_with_image_diameter_control
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h𝒦 : IsCombinatorialManifold 3 𝒦.complex) (hW : IsOpen W)
    (hΓW : graphSkeletonSpace 𝒦 ⊆ W) (hh : ContinuousOn h U)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
      IsCombinatorialManifold 3 𝒦'.complex ∧
      (∀ w, car w ∈ 𝒦.complex.faces) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ simplexBody 𝒦 (car w)) ∧
      (∀ w, Section34CarrierSupport 𝒦' w.1 ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
      (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
      (∀ w : Section34VertexIndex 𝒦 𝒦', Section34CarrierSupport 𝒦' w.1 ⊆ W) ∧
      ∀ s ∈ 𝒦'.complex.faces, ∀ x ∈ Section34CarrierSupport 𝒦' s,
        ∀ y ∈ Section34CarrierSupport 𝒦' s, ∀ z ∈ Section34CarrierSupport 𝒦' s,
          dist (h y) (h z) < ψ x := by
  let O : U → Set M₁ := fun p =>
    (U ∩ h ⁻¹' Metric.ball (h p) (ψ p / 8)) ∩ (U ∩ ψ ⁻¹' Ioi (ψ p / 2))
  have hO : ∀ p, IsOpen (O p) := fun p =>
    (hh.isOpen_inter_preimage hU Metric.isOpen_ball).inter
      (hψc.isOpen_inter_preimage hU isOpen_Ioi)
  have hcover : U ⊆ ⋃ p, O p := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ⟨hx, ?_⟩, hx, ?_⟩
    · change dist (h x) (h x) < ψ x / 8
      rw [dist_self]
      exact div_pos (hψpos x hx) (by norm_num)
    · change ψ x / 2 < ψ x
      linarith [hψpos x hx]
  obtain ⟨𝒦', car, hsub, hmap, hman, hsmall, hcar, hbody, hsupport, hfinite, hsupportW⟩ :=
    exists_graph_subdivision_with_finite_carrier_assignment hU 𝒦 h𝒦 hW hΓW O hO hcover
  refine ⟨𝒦', car, hsub, hmap, hman, hcar, hbody, hsupport, hfinite, hsupportW, ?_⟩
  intro s hs x hx y hy z hz
  obtain ⟨p, hp⟩ := hsmall s hs
  have hyball : dist (h y) (h p) < ψ p / 8 := (hp hy).1.2
  have hzball : dist (h z) (h p) < ψ p / 8 := (hp hz).1.2
  have hxscale : ψ p / 2 < ψ x := (hp hx).2.2
  have hpos : 0 < ψ p := hψpos p p.2
  calc
    dist (h y) (h z) ≤ dist (h y) (h p) + dist (h z) (h p) := by
      simpa only [dist_comm (h p) (h z)] using dist_triangle (h y) (h p) (h z)
    _ < ψ x := by linarith

end DifferentialGeometry.Topology.PiecewiseLinear
