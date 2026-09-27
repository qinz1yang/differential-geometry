import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.LinearAlgebra.Orientation

open Set Bundle
open scoped Topology
set_option autoImplicit false

namespace DifferentialGeometry.VectorBundle

variable {m : ℕ} {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def IsCompatibleOrientation (o : ∀ x, Orientation ℝ (V x) (Fin m)) : Prop :=
  ∀ x : B, ∃ t : Trivialization F (π F V), ∃ _ht : MemTrivializationAtlas t,
    ∃ U ∈ 𝓝 x, ∃ hU : U ⊆ t.baseSet, ∃ p : Orientation ℝ F (Fin m),
      ∀ y (hy : y ∈ U),
        Orientation.map (Fin m) (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv (o y) = p

theorem IsCompatibleOrientation.neg {o : ∀ x, Orientation ℝ (V x) (Fin m)}
    (ho : IsCompatibleOrientation (F := F) V o) :
    IsCompatibleOrientation (F := F) V (fun x => -o x) := by
  intro x
  obtain ⟨t, ht, U, hUx, hU, p, hp⟩ := ho x
  refine ⟨t, ht, U, hUx, hU, -p, ?_⟩
  intro y hy
  rw [Orientation.map_neg, hp y hy]

theorem isCompatibleOrientation_trivial (B : Type*) [TopologicalSpace B]
    (p : Orientation ℝ F (Fin m)) :
    IsCompatibleOrientation (F := F) (Bundle.Trivial B F) (fun _ => p) := by
  intro x
  refine ⟨Bundle.Trivial.trivialization B F, ⟨mem_singleton _⟩, univ, Filter.univ_mem,
    (fun _ _ => mem_univ _), p, ?_⟩
  intro y hy
  rw [Bundle.Trivial.continuousLinearEquivAt_trivialization]
  exact congrArg (fun q => q p) (Orientation.map_refl (Fin m))

end DifferentialGeometry.VectorBundle
