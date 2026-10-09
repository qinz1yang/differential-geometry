import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutOrientSign
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSum
import DifferentialGeometry.Topology.Manifold.BallChartOrientation

/-!
# Consumer of A6-b: oriented shell ball charts of the closed component models

`SphereCutCapped.exists_orientedComponentBallChart`: for the cut sphere `j` and a linear isometry
`A` equal to `id` or `-id`, the shell chart of `j` precomposed with `A`, as a ball chart of the
closed model of the component of `j`, is an oriented ball chart either for the model or for its
opposite (`BallChart.exists_oriented`; the reflected chart is `BallChart.reflect`). These are the
charts of the closed comparison A6-c: the left factor uses `A = id`, the right factor `A = -id`, so
that the fixed antipodal attachment of `connectedSum` matches the two shells.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Oriented shell ball charts of the closed component models.** -/
theorem SphereCutCapped.exists_orientedComponentBallChart {W : CompactCarrier.{u}}
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E)
    (DQ : X.Q.Components)
    (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
      (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅) (j : Fin 2)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hA : A = LinearIsometryEquiv.refl ℝ _ ∨ A = LinearIsometryEquiv.neg ℝ) :
    (∃ c : OrientedBallChart
        (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        (Subtype.val (c.chart x) : X.Q.Carrier) = X.shellChart j (A x)) ∨
    (∃ c : OrientedBallChart
        (componentModel X.Q DQ hQ
          (X.spherePiece DQ (Fin.cast X.h2.symm j))).opposite.toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        (Subtype.val (c.chart x) : X.Q.Carrier) = X.shellChart j (A x)) := by
  let b := X.componentBallChart DQ hQ j
  obtain ⟨β, hβ⟩ : ∃ β : BallChart 3 (𝓡 3)
      (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        (Subtype.val (β.chart x) : X.Q.Carrier) = X.shellChart j (A x) := by
    rcases hA with rfl | rfl
    · exact ⟨b, fun x hx => X.componentBallChart_val DQ hQ j hx⟩
    · refine ⟨b.reflect, fun x hx => ?_⟩
      rw [BallChart.reflect_apply]
      exact X.componentBallChart_val DQ hQ j (by simpa using hx)
  rcases BallChart.exists_oriented β with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨c, fun x hx => (congrArg Subtype.val (hc x)).trans (hβ x hx)⟩
  · exact Or.inr ⟨c, fun x hx => (congrArg Subtype.val (hc x)).trans (hβ x hx)⟩

end GC.GraphManifold.Assembly
