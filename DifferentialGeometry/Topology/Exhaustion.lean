import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

structure ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop where
  isOpen : forall k : Nat, IsOpen (U k)
  mono_step : forall k : Nat, U k ⊆ U (k + 1)
  subset :
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k

namespace ExhaustsByOpen

theorem monotone {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) :
    Monotone U := by
  intro i j hij
  induction hij with
  | refl => intro x hx; exact hx
  | step hle ih =>
      exact Set.Subset.trans ih (hU.mono_step _)

theorem subset_of_le {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) {i j : Nat} (hij : i <= j) :
    U i ⊆ U j :=
  hU.monotone hij

theorem comp_subseq {M : Type*} [TopologicalSpace M]
    {U : Nat -> Set M} (hU : ExhaustsByOpen U)
    {φ : Nat -> Nat} (hφ : StrictMono φ) :
    ExhaustsByOpen (fun k => U (φ k)) := by
  refine ⟨fun k => hU.isOpen (φ k),
    fun k => hU.subset_of_le (hφ.monotone (Nat.le_succ k)), ?_⟩
  intro K hK
  obtain ⟨k0, hk0⟩ := hU.subset K hK
  exact ⟨k0, fun k hk => hk0 (φ k) (le_trans hk (hφ.id_le k))⟩

end ExhaustsByOpen

end CheegerGromovCompactness
end DifferentialGeometry
