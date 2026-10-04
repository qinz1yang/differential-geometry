import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightDifferential
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightOnePoint

/-!
# Consumers of G-dζ and G-R (statement G, BSA01.a `|dz|` part and BSA01.c)

* `CuspEmbedding.mfderiv_height_invFunOn_ne_zero`: the actual collar height `ζ = z ∘ e⁻¹` has no
  critical point on the open collar `e(T² × [0, 100))`, boundary included (the normalisation
  `dζ / ‖dζ‖` of the second-fundamental-form clause is defined there);
* `NearlyCuspidalBoundary.boundary_clause_of_negative_height_one`: the second clause of the
  frozen interface `G_consumer_clauses` (`d(p, ∂W) < ∞` and `R_p ≤ d(p, ∂W) + 3` on a connected
  carrier), with the sectional input at the height-one collar points explicit (lane FT-C).
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- The actual collar height has nonzero differential at every point of the open collar. -/
theorem CuspEmbedding.mfderiv_height_invFunOn_ne_zero (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) ≠ 0 := by
  intro h
  obtain ⟨u, hu, -⟩ := e.exists_mfderiv_height_invFunOn_eq_one hp
  rw [h] at hu
  have hu' : (0 : ℝ) = 1 := hu
  exact absurd hu' (by norm_num)

/-- **BSA01.c, the consumer clause.** With every plane at every height-one collar point of
sectional curvature `≤ -1/8` (`δ ≤ 1/100`), on a connected carrier every point has finite distance
to `∂W` and curvature scale `R_p ≤ d(p, ∂W) + 3`: the second clause of `G_consumer_clauses`. -/
theorem NearlyCuspidalBoundary.boundary_clause_of_negative_height_one
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100)
    (hneg : ∀ (i : Fin B.count) (x : Torus)
      (u w : TangentSpace W.model ((B.collar i).toFun (x, halfSpaceOneLift 1))),
      metricRm04StandardAt g ((B.collar i).toFun (x, halfSpaceOneLift 1)) u w w u ≤
        -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2)) :
    ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
      curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3 := fun _ p =>
  ⟨B.distanceToBoundary_lt_top p, B.curvatureRadius_le_distanceToBoundary_add_three hδ hneg p⟩

end DifferentialGeometry.Geometry.Collapse
