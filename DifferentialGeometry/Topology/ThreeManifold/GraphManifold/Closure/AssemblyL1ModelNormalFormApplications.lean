import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelNormalForm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1GluingSmoothApplications

/-!
# Chapter-14 assembly, item L1, group G3a: consumers of the model cycle normal form

* `CycleNormalForm.exists_solidTorus_map`: every cycle normal form (of positive length) has a union
  parametrized by the standard solid torus through a smooth injective immersion (G3a + G3c);
* `BallHandleCycle.nonempty_diffeomorph_of_cycleNormalForm`: L1 for a ball–handle cycle from a
  single normal form of the cycle (the model normal form is supplied by G3a).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

/-- A cycle normal form of positive length is parametrized by the standard solid torus. -/
theorem CycleNormalForm.exists_solidTorus_map {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U : Set X}
    (N : CycleNormalForm I X len ε U) (hlen : 0 < len) :
    ∃ F : solidTorusSet.{u} → X, ContMDiff (𝓡∂ 3) I ∞ F ∧ Injective F ∧
      (∀ p, Injective (mfderiv (𝓡∂ 3) I F p)) ∧ range F = U :=
  exists_map_of_cycleNormalForms N (modelCycleNormalForm.{u} hlen N.ε_pos N.ε_le)

/-- **L1 from one normal form.** A normal form of a ball–handle cycle with the union of the cycle
as its union gives a diffeomorphism of the standard solid torus onto the union piece. -/
theorem BallHandleCycle.nonempty_diffeomorph_of_cycleNormalForm {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) {ε : ℝ}
    (N : CycleNormalForm W.model W.Carrier C.len ε (range C.union.map)) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
      C.union.Piece) :=
  C.nonempty_diffeomorph_of_cycleNormalForms N (modelCycleNormalForm.{u} C.len_pos N.ε_pos N.ε_le)

end GC.GraphManifold.Assembly
