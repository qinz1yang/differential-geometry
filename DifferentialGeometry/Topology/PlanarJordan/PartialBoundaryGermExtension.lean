/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.BoundaryGermExtension
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import DifferentialGeometry.Topology.Homeomorph.SubsetImage
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn
    (e : OpenPartialHomeomorph Plane Plane)
    {γ : AddCircle (1 : ℝ) → Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ)
    (hsource : closure (Schoenflies.inside (range γ)) ⊆ e.source)
    {U : Set Plane} (hU : IsOpen U) (hcurve : range γ ⊆ U) (hUs : U ⊆ e.source)
    (hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e U) :
    ∃ Q : Plane ≃ₘ[ℝ] Plane,
      Q '' closure (Schoenflies.inside (range γ)) =
        e '' closure (Schoenflies.inside (range γ)) ∧
      ∃ V : Set Plane, IsOpen V ∧ range γ ⊆ V ∧ V ⊆ U ∧ EqOn Q e V := by
  obtain ⟨c, hcs, -, hceq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
      hU hlocal (e.injOn.mono hUs)
  have hγc : range γ ⊆ c.source := by rw [hcs]; exact hcurve
  let δ : AddCircle (1 : ℝ) → Plane := c ∘ γ
  have hδ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ δ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph c hγ hγc
  let C := closure (Schoenflies.inside (range γ))
  obtain ⟨D, hDsphere, -, hDball⟩ := smooth_schoenflies hγ
  have hC : IsCompact C := by
    rw [show C = D '' closedBall (0 : Plane) 1 from hDball.symm]
    exact (isCompact_closedBall (0 : Plane) 1).image D.continuous
  have hfr : frontier C = range γ := by
    rw [show C = D '' closedBall (0 : Plane) 1 from hDball.symm]
    change frontier (D.toHomeomorph '' closedBall (0 : Plane) 1) = range γ
    rw [← D.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
    exact hDsphere
  have hne : (interior C).Nonempty := by
    rw [show C = D '' closedBall (0 : Plane) 1 from hDball.symm]
    change (interior (D.toHomeomorph '' closedBall (0 : Plane) 1)).Nonempty
    rw [← D.toHomeomorph.image_interior, interior_closedBall _ one_ne_zero]
    exact (nonempty_ball.mpr one_pos).image D
  have hδrange : range δ = e '' range γ := by
    rw [show δ = (c : Plane → Plane) ∘ γ from rfl, range_comp]
    exact image_congr (fun x _ => congrFun hceq x)
  have htargetfr : frontier (e '' C) = range δ := by
    rw [← e.image_frontier_of_isCompact hC hsource, hfr, hδrange]
  have htargetC : IsCompact (e '' C) :=
    hC.image_of_continuousOn (e.continuousOn.mono hsource)
  have htargetne : (interior (e '' C)).Nonempty := by
    rw [← e.image_interior_of_subset_source hsource]
    exact hne.image e
  have htargetJ : Schoenflies.IsJordanCurve (frontier (e '' C)) := by
    rw [htargetfr]
    exact isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hδ.isEmbedding
  have htarget : closure (Schoenflies.inside (range δ)) = e '' C := by
    rw [← htargetfr]
    exact closure_inside_frontier_eq_of_isCompact htargetC htargetJ htargetne
  have hc : c.toOpenPartialHomeomorph.IsImage C
      (closure (Schoenflies.inside (range δ))) := by
    intro x hx
    change c x ∈ closure (Schoenflies.inside (range δ)) ↔ x ∈ C
    rw [htarget, congrFun hceq x]
    exact e.isImage_image_of_subset_source hsource (hUs (hcs ▸ hx))
  obtain ⟨Q, -, hQ, V, hV, hγV, hVc, hQV⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_jordan_curve hγ hδ c hc hγc
  exact ⟨Q, hQ.trans htarget, V, hV, hγV,
    fun x hx => hcs ▸ hVc hx, fun x hx => (hQV hx).trans (congrFun hceq x)⟩

end DifferentialGeometry.Topology.PlanarJordan
