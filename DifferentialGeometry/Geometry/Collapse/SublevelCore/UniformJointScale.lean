import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Sequences

/-!
# Uniform bounded scales from sequential eventual witnesses (kernel of LC58)

Frozen blueprint master207A, theorem `thm:collapse-uniform-joint-scale` (LC58, lines 23194–23234).
The blueprint proves the uniform joint scale interval by negating the JOINT conclusion: if for
every `V` some late index `α` and point `p` admit no scale `s ∈ [T, V]` with all witnesses, choose
such bad `(α_i, p_i)` with `V = T + i`; the hypothesis (LC56 extraction followed by LC57) gives a
subsequence, ONE fixed `R ≥ T` and a tail on which `R` works, contradicting badness once
`T + φ j ≥ R`.

The kernel below is that argument for an arbitrary predicate `Good α p s` ("all LC57 conclusions
hold at scale `s ρ_α(p)` for the point `p` of the `α`-th manifold"). Its hypothesis `hseq` is the
sequential statement produced by LC56 + LC57; the conclusion is the uniform interval. No rate and no
continuous choice of scales is produced.
-/

set_option autoImplicit false

open Filter Set

namespace DifferentialGeometry.Geometry.Collapse

/-- **Kernel of LC58.** If along every sequence of indices tending to infinity and every choice
of points some subsequence has ONE scale `R ≥ T` that eventually works, then there are `V ≥ T` and
`α₀` such that for every `α > α₀` and every point `p` some scale `s ∈ [T, V]` works. -/
theorem exists_uniform_scale_interval_of_eventual_witnesses {X : ℕ → Type*}
    (Good : ∀ α, X α → ℝ → Prop) (T : ℝ)
    (hseq : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ p : ∀ i, X (a i),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ R : ℝ, T ≤ R ∧ ∀ᶠ j in atTop, Good (a (φ j)) (p (φ j)) R) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α, α₀ < α → ∀ p : X α, ∃ s ∈ Icc T V, Good α p s := by
  by_contra hfail
  push Not at hfail
  have hbad : ∀ i : ℕ, ∃ α, i < α ∧ ∃ p : X α, ∀ s ∈ Icc T (T + i), ¬ Good α p s := by
    intro i
    obtain ⟨α, hα, p, hp⟩ := hfail (T + i) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) i
    exact ⟨α, hα, p, hp⟩
  choose a ha p hp using hbad
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_mono (fun i => (ha i).le) tendsto_id
  obtain ⟨φ, hφ, R, hTR, hgood⟩ := hseq a hatop p
  obtain ⟨N, hN⟩ := exists_nat_ge (R - T)
  obtain ⟨j, hj, hjN⟩ := (hgood.and (eventually_ge_atTop N)).exists
  have hφj : (N : ℝ) ≤ φ j := by exact_mod_cast hjN.trans (hφ.id_le j)
  exact hp (φ j) R ⟨hTR, by linarith⟩ hj

end DifferentialGeometry.Geometry.Collapse
