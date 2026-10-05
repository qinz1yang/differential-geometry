import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus

/-!
# Chapter-14 assembly, item L1, group G3: the model cycle normal form

The model of G3a is a `CycleNormalForm` of the standard solid torus `solidTorusSet ⊆ S³` whose balls
and handles are restrictions of partial diffeomorphisms of open sets of `ℝ³` and `ℝ² × ℝ` into `S³`
(`ModelCycleNormalForm`). The charts make the local inverses of the model pieces smooth in the
gluing G3c; the actual normal form (G3b) needs no charts.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The model cycle normal form: a cycle normal form of the standard solid torus of `S³` whose balls
and handles extend to partial diffeomorphisms of open sets of `ℝ³` and of `ℝ² × ℝ`. -/
structure ModelCycleNormalForm (len : ℕ) (ε : ℝ) extends
    CycleNormalForm (𝓡 3) SphereCarrier.{u} len ε solidTorusSet.{u} where
  ballChart : Fin len →
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) SphereCarrier.{u} ∞
  ballChart_source : ∀ k, closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ (ballChart k).source
  ballChart_eq : ∀ k x, ball k x = ballChart k (x : EuclideanSpace ℝ (Fin 3))
  handleChart : Fin len → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3)
    (EuclideanSpace ℝ (Fin 2) × ℝ) SphereCarrier.{u} ∞
  handleChart_source : ∀ k, {q : EuclideanSpace ℝ (Fin 2) × ℝ | ‖q.1‖ ≤ 1 ∧ q.2 ∈ Icc (0 : ℝ) 1} ⊆
    (handleChart k).source
  handleChart_eq : ∀ k (q : ClosedCell 2 × Icc (0 : ℝ) 1),
    handle k q = handleChart k ((q.1 : EuclideanSpace ℝ (Fin 2)), (q.2 : ℝ))

end GC.GraphManifold.Assembly
