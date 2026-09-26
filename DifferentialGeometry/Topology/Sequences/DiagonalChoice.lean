import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set
open scoped Topology

namespace Filter

theorem exists_seq_forall_of_eventually {α : Type*} {F : ℕ → Filter α} [∀ n, (F n).NeBot]
    {ι : ℕ → Type*} [∀ n, Finite (ι n)] {p : ∀ n, ι n → α → Prop}
    (h : ∀ n i, ∀ᶠ a in F n, p n i a) : ∃ a : ℕ → α, ∀ n i, p n i (a n) := by
  choose a ha using fun n => (eventually_all.2 (h n)).exists
  exact ⟨a, ha⟩

theorem exists_seq_mem_Ioo_forall_of_eventually_nhdsLT {s b : ℕ → ℝ} (hb : ∀ n, b n < s n)
    {ι : ℕ → Type*} [∀ n, Finite (ι n)] {p : ∀ n, ι n → ℝ → Prop}
    (h : ∀ n i, ∀ᶠ τ in 𝓝[<] s n, p n i τ) :
    ∃ τ : ℕ → ℝ, (∀ n, τ n ∈ Ioo (b n) (s n)) ∧ ∀ n i, p n i (τ n) := by
  choose τ hτ using fun n => (Eventually.and (Ioo_mem_nhdsLT (hb n))
    (eventually_all.2 (h n))).exists
  exact ⟨τ, fun n => (hτ n).1, fun n => (hτ n).2⟩

end Filter
