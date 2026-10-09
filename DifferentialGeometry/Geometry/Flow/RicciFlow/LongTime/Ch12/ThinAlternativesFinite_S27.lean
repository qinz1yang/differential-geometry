import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringG2_S16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

/-!
# CH12-S27: `finite_scales` for the thin alternative (C4 G3, part 1)

On a connected block, `curvatureRadius g p = ⊤ ↔ SectionalBoundedBelow g 0`
(`curvatureRadius_eq_top_iff`).  Hence finiteness of every curvature scale follows from one
negative plane:
* a block with `NearlyCuspidalBoundary (1/10000)`: a collar point of positive height;
* a closed block that is not sectionally nonnegative: by definition;
* early indices: `thin := False`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology GC.Endpoint GC.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A nearly cuspidal boundary (accuracy `1/10000`) forces a plane of sectional curvature
below `-1/81`, at a collar point of positive height. -/
theorem exists_negative_plane_of_nearlyCuspidal_S27 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    (B : NearlyCuspidalBoundary W g (K + 4) (1 / 10000)) :
    ∃ q, ¬ SectionalBoundedBelowAt g q (-(1 / 81 : ℝ)) := by
  let e := B.collar ⟨0, B.count_pos⟩
  let t : Torus := (1, 1)
  have hz : ((t, halfPoint 1 zero_le_one) : CuspHalfSpace) ∈ cuspDomain := by
    change (1 : ℝ) < cuspDepth
    norm_num [cuspDepth]
  exact ⟨_, not_sectionalBoundedBelowAt_collar_S16 e (by omega) le_rfl _ hz
    (by change (0 : ℝ) < 1; norm_num)⟩

theorem curvatureRadius_ne_top_of_not_nonneg_S27 {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
    (h : ¬ SectionalBoundedBelow g 0) (p : W.Carrier) : curvatureRadius g p ≠ ⊤ :=
  fun htop => h ((curvatureRadius_eq_top_iff p).mp htop)

/-- Thin block with boundary: every curvature scale is finite. -/
theorem curvatureRadius_ne_top_of_nearlyCuspidal_S27 {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    (B : NearlyCuspidalBoundary W g (K + 4) (1 / 10000)) (p : W.Carrier) :
    curvatureRadius g p ≠ ⊤ := by
  obtain ⟨q, hq⟩ := exists_negative_plane_of_nearlyCuspidal_S27 B
  refine curvatureRadius_ne_top_of_not_nonneg_S27 (fun h => hq ?_) p
  exact (h q).mono (by norm_num)

/-- Components of a torus decomposition are connected. -/
theorem _root_.GC.Topology.TorusDecomposition.component_connected_S27
    {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)
    (i : Fin D.components.count) : ConnectedSpace (D.component i).Carrier :=
  D.components.connected i

/-- The `finite_scales` field of `LateCutFamily`, for one decomposition: a thin block is either
nearly cuspidal at `1/10000` or not sectionally nonnegative. -/
theorem finite_scales_field_S27 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (K : ℕ)
    (metric : (i : Fin D.components.count) →
      SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop)
    (hcases : ∀ i, thin i →
      Nonempty (NearlyCuspidalBoundary (D.component i) (metric i) (K + 4) (1 / 10000)) ∨
        ¬ SectionalBoundedBelow (metric i) 0) :
    ∀ i, thin i → ∀ p, curvatureRadius (metric i) p ≠ ⊤ := by
  intro i hi p
  have := D.component_connected_S27 i
  rcases hcases i hi with hB | h
  · obtain ⟨B⟩ := hB
    exact curvatureRadius_ne_top_of_nearlyCuspidal_S27 B p
  · exact curvatureRadius_ne_top_of_not_nonneg_S27 h p

/-- Early indices: `thin := False` makes `finite_scales` vacuous. -/
theorem finite_scales_of_early_false_S27 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M)
    (metric : (i : Fin D.components.count) →
      SmoothRiemannianMetric (D.component i).model (D.component i).Carrier) :
    ∀ i, (fun _ : Fin D.components.count => False) i → ∀ p, curvatureRadius (metric i) p ≠ ⊤ :=
  fun _ h => h.elim

end GC.LongTime.Ch12
