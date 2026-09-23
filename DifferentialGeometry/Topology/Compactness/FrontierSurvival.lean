import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.Topology

theorem frontier_nonempty_of_compact_nonempty
    {M : Type*} [TopologicalSpace M] [PreconnectedSpace M] [NoncompactSpace M]
    {W : Set M} (hW : IsCompact W) (hne : W.Nonempty) : (frontier W).Nonempty := by
  by_contra h
  have hfront : frontier W = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hfull : W = univ := (isClopen_iff_frontier_eq_empty.mpr hfront).eq_univ hne
  exact noncompact_univ (X := M) (by simpa only [hfull] using hW)

theorem exists_stable_nonempty_frontier_labels
    {M ι : Type*} [TopologicalSpace M] [PreconnectedSpace M] [NoncompactSpace M]
    (W : ℕ → Set M) (alive : ℕ → Set ι) (sphere : ℕ → ι → Set M)
    (hW : ∀ n, IsCompact (W n)) (hne : ∀ n, (W n).Nonempty)
    (hfront : ∀ n, frontier (W n) ⊆ ⋃ i ∈ alive n, sphere n i)
    (hfinite : (alive 0).Finite) (halive : Antitone alive) :
    ∃ N : ℕ, (alive N).Nonempty ∧ ∀ n, N ≤ n → alive n = alive N := by
  let A (n : ℕ) : {S : Set ι // S.Finite} :=
    ⟨alive n, hfinite.subset (halive (Nat.zero_le n))⟩
  have hA : Antitone A := fun m n hmn => halive hmn
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hA
  have hnonempty : (alive N).Nonempty := by
    obtain ⟨x, hx⟩ := frontier_nonempty_of_compact_nonempty (hW N) (hne N)
    have hx' := hfront N hx
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp hx'
    exact ⟨i, hi⟩
  refine ⟨N, hnonempty, ?_⟩
  intro n hn
  exact (congrArg Subtype.val (hN n hn)).symm

end DifferentialGeometry.Topology
