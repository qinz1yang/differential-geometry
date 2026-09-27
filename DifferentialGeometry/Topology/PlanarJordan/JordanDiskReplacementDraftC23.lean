/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.BoundaryGermExtension
import DifferentialGeometry.Topology.PlanarJordan.Transport
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.RelativeDiffeomorphPasting

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem exists_homeomorph_smoothing_jordan_disk
    (h : Plane ≃ₜ Plane) {γ₀ γ₁ : AddCircle (1 : ℝ) → Plane}
    (hγ₀ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ₀)
    (hγ₁ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ₁)
    (hboundary : h '' range γ₀ = range γ₁) {U : Set Plane}
    (hU : IsOpen U) (hcurve : range γ₀ ⊆ U)
    (hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h U) :
    ∃ g : Plane ≃ₜ Plane,
      EqOn g h (interior (closure (Schoenflies.inside (range γ₀))))ᶜ ∧
      g '' closure (Schoenflies.inside (range γ₀)) =
        h '' closure (Schoenflies.inside (range γ₀)) ∧
      (∀ x, IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x) ∧
      ∃ V : Set Plane, IsOpen V ∧ range γ₀ ⊆ V ∧ EqOn g h V ∧
        ∃ W : Set Plane, IsOpen W ∧ closure (Schoenflies.inside (range γ₀)) ⊆ W ∧
          IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g W := by
  obtain ⟨c, hcs, -, hceq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
      hU hlocal h.injective.injOn
  have himage : h '' closure (Schoenflies.inside (range γ₀)) =
      closure (Schoenflies.inside (range γ₁)) := by
    rw [h.image_closure, image_inside, hboundary]
  have hc : c.toOpenPartialHomeomorph.IsImage
      (closure (Schoenflies.inside (range γ₀)))
      (closure (Schoenflies.inside (range γ₁))) := by
    intro x _
    change c x ∈ closure (Schoenflies.inside (range γ₁)) ↔
      x ∈ closure (Schoenflies.inside (range γ₀))
    rw [congrFun hceq x, ← himage]
    exact h.injective.mem_set_image
  have hsource : range γ₀ ⊆ c.source := by rw [hcs]; exact hcurve
  obtain ⟨Q, -, hQimage, V, hV, hcurveV, -, hQV⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_jordan_curve hγ₀ hγ₁ c hc hsource
  have hQh : EqOn Q h V := fun x hx => (hQV hx).trans (congrFun hceq x)
  obtain ⟨D, hDsphere, -, hDball⟩ := smooth_schoenflies hγ₀
  have hclosed : IsClosed (closure (Schoenflies.inside (range γ₀))) := isClosed_closure
  have hfrontier : frontier (closure (Schoenflies.inside (range γ₀))) = range γ₀ := by
    rw [← hDball]
    change frontier (D.toHomeomorph '' closedBall (0 : Plane) 1) = range γ₀
    rw [← D.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
    exact hDsphere
  obtain ⟨g, -, hgout, hgV, hgimage, hgpreserve, W, hW, hKW, -, -, hgW⟩ :=
    h.exists_pasting_of_partialDiffeomorph Q.toPartialDiffeomorph hclosed (subset_univ _)
      (hQimage.trans himage.symm) hV (by rw [hfrontier]; exact hcurveV) hQh
  exact ⟨g, hgout, hgimage, hgpreserve, V, hV, hcurveV, hgV, W, hW, hKW, hgW⟩

end DifferentialGeometry.Topology.PlanarJordan
