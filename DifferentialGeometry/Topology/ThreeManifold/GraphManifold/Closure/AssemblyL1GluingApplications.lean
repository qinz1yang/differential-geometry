import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Gluing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelForm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Factorization

/-!
# Chapter-14 assembly, item L1, group G3: consumers of the set-level gluing and the factorization

* `transferEquiv N₀ N`: the transfer between two cycle normal forms with the same combinatorics and
  scale is a bijection of their unions;
* `ModelCycleNormalForm.solidTorusEquiv N₀ N`: the model normal form identifies the solid torus with
  the union of any cycle normal form, as sets;
* `BallHandleCycle.nonempty_diffeomorph_of_range_eq`: the final step of L1 for a ball–handle cycle
  (a smooth injective immersion of the solid torus onto the union is a diffeomorphism onto the union
  piece).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Transfer

variable {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₀}
  {X₀ : Type*} [TopologicalSpace X₀] [ChartedSpace H₀ X₀]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U₀ : Set X₀} {U : Set X}

/-- The transfer between two cycle normal forms is a bijection of their unions. -/
def transferEquiv (N₀ : CycleNormalForm I₀ X₀ len ε U₀) (N : CycleNormalForm I X len ε U) :
    U₀ ≃ U where
  toFun p := ⟨transfer N₀ N p.1 p.2, transfer_mem N₀ N p.1 p.2⟩
  invFun y := ⟨transfer N N₀ y.1 y.2, transfer_mem N N₀ y.1 y.2⟩
  left_inv p := Subtype.ext (transfer_transfer N₀ N p.1 p.2)
  right_inv y := Subtype.ext (transfer_transfer N N₀ y.1 y.2)

theorem transferEquiv_apply (N₀ : CycleNormalForm I₀ X₀ len ε U₀)
    (N : CycleNormalForm I X len ε U) (p : U₀) :
    (transferEquiv N₀ N p : X) = transfer N₀ N p.1 p.2 :=
  rfl

end Transfer

/-- The model normal form identifies the solid torus with the union of a cycle normal form. -/
def ModelCycleNormalForm.solidTorusEquiv {len : ℕ} {ε : ℝ} (N₀ : ModelCycleNormalForm.{u} len ε)
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {U : Set X}
    (N : CycleNormalForm I X len ε U) : solidTorusSet.{u} ≃ U :=
  transferEquiv N₀.toCycleNormalForm N

/-- **The final step of L1 for a ball–handle cycle.** A smooth injective immersion of the solid
torus onto the union of a ball–handle cycle is a diffeomorphism onto the union piece. -/
theorem BallHandleCycle.nonempty_diffeomorph_of_range_eq {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (F : solidTorusSet.{u} → W.Carrier)
    (hF : ContMDiff (𝓡∂ 3) W.model ∞ F) (hinj : Injective F)
    (hd : ∀ p, Injective (mfderiv (𝓡∂ 3) W.model F p)) (hrange : range F = range C.union.map) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
      C.union.Piece) :=
  Assembly.nonempty_diffeomorph_of_range_eq C.union F hF hinj hd hrange

end GC.GraphManifold.Assembly
