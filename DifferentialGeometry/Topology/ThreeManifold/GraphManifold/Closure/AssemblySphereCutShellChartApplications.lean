import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutShellChart

/-!
# Consumer of the shell ball chart: the two cut spheres of a sphere-cut-capped carrier

`SphereCutCapped.exists_shellBallChart`: for the cut of a carrier `W` along an interior sphere seam
`S`, each of the two cut spheres has a shell ball chart in the capped carrier whose shell is
carried by the core and the fold onto the signed sphere collar of `S` at heights
`± (s₀ + μ (r - 1))` (the sign is the side of the cut). This is the form in which the closed
comparison (A6) and the relative comparison (A4) use A6-a.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Shell ball charts of the two cut spheres.** -/
theorem SphereCutCapped.exists_shellBallChart {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ}
    {E : BoundaryTori W n} (X : SphereCutCapped W S E) (j : Fin 2) :
    ∃ (c : PartialDiffeomorph (𝓡 3) X.Q.model (EuclideanSpace ℝ (Fin 3)) X.Q.Carrier ∞)
      (s₀ μ : ℝ), 0 < s₀ ∧ 0 < μ ∧ s₀ + μ < 1 ∧
      Metric.closedBall 0 2 ⊆ c.source ∧ c.target ⊆ X.Q.interior ∧
      ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (r : ℝ), 1 ≤ r → r ≤ 2 →
        ∃ y : X.C.Carrier, X.capping.core y = c (r • (z : EuclideanSpace ℝ (Fin 3))) ∧
          X.fold y = S.collar (ULift.up z,
            if j.val = 0 then s₀ + μ * (r - 1) else -(s₀ + μ * (r - 1))) := by
  obtain ⟨c, s₀, μ, hs₀, hμ, hsum, hsrc, htgt, hshell, -⟩ :=
    RelativeSphereCapping.exists_shellBallChart X.capping (Fin.cast X.h2.symm j)
  refine ⟨c, s₀, μ, hs₀, hμ, hsum, hsrc, htgt, fun z r hr hr2 => ?_⟩
  refine ⟨X.B.sphere (Fin.cast X.h2.symm j) (ULift.up z, halfPoint (s₀ + μ * (r - 1))
    (add_nonneg hs₀.le (mul_nonneg hμ.le (sub_nonneg.mpr hr)))), (hshell z r hr hr2).symm, ?_⟩
  exact X.spheres j (ULift.up z) _ _ (by nlinarith)

end GC.GraphManifold.Assembly
