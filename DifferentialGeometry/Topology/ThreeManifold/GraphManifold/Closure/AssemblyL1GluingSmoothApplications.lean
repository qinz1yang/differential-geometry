import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1GluingSmooth

/-!
# Chapter-14 assembly, item L1, group G3c: consumers of the smooth gluing

* `gluedMap_comp_ball`, `gluedMap_comp_handle`: the glued map carries the model balls and handles
  to the balls and handles of the target normal form;
* `BallHandleCycle.nonempty_diffeomorph_of_cycleNormalForms`: L1 for a ball–handle cycle from a
  normal form of the cycle and a model normal form at the same combinatorics and scale (the final
  theorem of L1 only adds the existence of the two normal forms, G3a and G3b).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Glued

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U : Set X}
  (N : CycleNormalForm I X len ε U) (N₀ : ModelCycleNormalForm.{u} len ε)

/-- The glued map carries the model ball `k` to the ball `k`. -/
theorem gluedMap_comp_ball (k : Fin len) :
    (gluedMap N N₀ ∘ fun x : ClosedCell 3 => (⟨N₀.ball k x, N₀.ball_mem k x⟩ :
      solidTorusSet.{u})) = N.ball k :=
  funext fun x => transfer_ball N₀.toCycleNormalForm N k x (N₀.ball_mem k x)

/-- The glued map carries the model handle `k` to the handle `k`. -/
theorem gluedMap_comp_handle (k : Fin len) :
    (gluedMap N N₀ ∘ fun q : ClosedCell 2 × Icc (0 : ℝ) 1 => (⟨N₀.handle k q, N₀.handle_mem k q⟩ :
      solidTorusSet.{u})) = N.handle k :=
  funext fun q => transfer_handle N₀.toCycleNormalForm N k q (N₀.handle_mem k q)

end Glued

/-- **L1 from two normal forms.** A normal form of a ball–handle cycle, with the union of the cycle
as its union, and the model normal form at the same combinatorics and scale give a diffeomorphism
of the standard solid torus onto the union piece. -/
theorem BallHandleCycle.nonempty_diffeomorph_of_cycleNormalForms {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) {ε : ℝ}
    (N : CycleNormalForm W.model W.Carrier C.len ε (range C.union.map))
    (N₀ : ModelCycleNormalForm.{u} C.len ε) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
      C.union.Piece) := by
  obtain ⟨F, hF, hinj, hd, hrange⟩ := exists_map_of_cycleNormalForms N N₀
  exact C.nonempty_diffeomorph_of_range_eq F hF hinj hd hrange

end GC.GraphManifold.Assembly
