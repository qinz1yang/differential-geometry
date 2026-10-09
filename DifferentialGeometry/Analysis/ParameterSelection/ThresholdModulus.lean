import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.LeftRightNhds

/-!
# A modulus from a sequence of accuracy thresholds (CFS15 / B:10979 quantifier argument)

Blueprint `master207B.tex`: the proofs of CFS15 (`cor:fibration-cloud-marker-modulus`,
lines 2711–2745) and of the uncoded lemma "A smoothing modulus in the source's choice order"
(`lem:fibration-smoothing-modulus-selection`, lines 10979–11010) use one quantifier argument:
thresholds `d_m > 0` for the accuracies `ε_m` give `θ₁ > 0` and a modulus `Ξ(Γ) → 0`
(`Γ ↓ 0`) such that quality `Γ < θ₁` is below the threshold of the accuracy `Ξ(Γ)`.

* `exists_modulus_of_thresholds`: for any predicate `P ε Γ` ("quality-`Γ` data have the
  accuracy-`ε` conclusions") with, for every `m`, a threshold `d > 0` such that `P ε_m Γ` for all
  `0 < Γ ≤ d`, where `ε_m = (1/2)^(m+4)`, there are `θ₁ > 0` and `Ξ` with `Ξ(Γ) → 0` as `Γ ↓ 0`
  and, for `0 < Γ < θ₁`, `Ξ(Γ) = ε_m` for some `m` and `P (Ξ Γ) Γ`.
-/

set_option autoImplicit false

open Filter Topology

namespace DifferentialGeometry.Analysis.ParameterSelection

/-- The modulus argument of CFS15 / B:10979 for an arbitrary threshold predicate. -/
theorem exists_modulus_of_thresholds {P : ℝ → ℝ → Prop}
    (hP : ∀ m : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ Γ, 0 < Γ → Γ ≤ d → P ((1 / 2 : ℝ) ^ (m + 4)) Γ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧ P (Ξ Γ) Γ := by
  classical
  choose d hdpos hd using hP
  -- `θ m = min (1/2)^m (min_{j ≤ m} d j / 2)`: positive and antitone
  let θ : ℕ → ℝ := fun m =>
    min ((1 / 2 : ℝ) ^ m) ((Finset.range (m + 1)).inf' Finset.nonempty_range_add_one
      (fun j => d j / 2))
  have hθpos : ∀ m, 0 < θ m := fun m => lt_min (by positivity)
    ((Finset.lt_inf'_iff _).mpr fun j _ => half_pos (hdpos j))
  have hθd : ∀ m, θ m < d m := fun m =>
    ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.self_mem_range_succ m))).trans_lt
      (half_lt_self (hdpos m))
  have hθpow : ∀ m, θ m ≤ (1 / 2 : ℝ) ^ m := fun m => min_le_left _ _
  have hθanti : Antitone θ := by
    intro a b hab
    refine min_le_min (pow_le_pow_of_le_one (by norm_num) (by norm_num) hab) ?_
    exact Finset.le_inf' _ _ fun j hj =>
      Finset.inf'_le _ (Finset.range_subset_range.mpr (by omega) hj)
  -- a bound `N Γ` with `(1/2)^(N Γ) < Γ`
  have hN : ∀ Γ : ℝ, 0 < Γ → ∃ n : ℕ, (1 / 2 : ℝ) ^ n < Γ := fun Γ hΓ =>
    exists_pow_lt_of_lt_one hΓ (by norm_num)
  let N : ℝ → ℕ := fun Γ => if h : 0 < Γ then Classical.choose (hN Γ h) else 0
  have hNspec : ∀ Γ, 0 < Γ → (1 / 2 : ℝ) ^ N Γ < Γ := fun Γ hΓ => by
    simp only [N, dite_eq_left hΓ]
    exact Classical.choose_spec (hN Γ hΓ)
  -- every `m` with `Γ < θ m` is below `N Γ`
  have hbelow : ∀ Γ m, 0 < Γ → Γ < θ m → m ≤ N Γ := by
    intro Γ m hΓ hm
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N Γ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt.le
    linarith [hθpow m, hNspec Γ hΓ]
  let mΓ : ℝ → ℕ := fun Γ => Nat.findGreatest (fun m => Γ < θ m) (N Γ)
  let Ξ : ℝ → ℝ := fun Γ => (1 / 2 : ℝ) ^ (mΓ Γ + 4)
  have hspec : ∀ Γ, 0 < Γ → Γ < θ 0 → Γ < θ (mΓ Γ) := fun Γ _ h0 =>
    Nat.findGreatest_spec (P := fun m => Γ < θ m) (Nat.zero_le _) h0
  have hge : ∀ Γ M, 0 < Γ → Γ < θ M → M ≤ mΓ Γ := fun Γ M hΓ hM =>
    Nat.le_findGreatest (hbelow Γ M hΓ hM) hM
  refine ⟨θ 0, hθpos 0, Ξ, ?_, fun Γ hΓ hΓθ => ⟨⟨mΓ Γ, rfl⟩, ?_⟩⟩
  · -- `Ξ Γ → 0`
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨θ M, hθpos M, fun Γ hΓ hdist => ?_⟩
    have hΓpos : 0 < Γ := hΓ
    rw [Real.dist_eq, sub_zero, abs_of_pos hΓpos] at hdist
    have hMle := hge Γ M hΓpos hdist
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    calc Ξ Γ = (1 / 2 : ℝ) ^ (mΓ Γ + 4) := rfl
      _ ≤ (1 / 2 : ℝ) ^ M := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ < η := hM
  · exact hd (mΓ Γ) Γ hΓ ((hspec Γ hΓ hΓθ).le.trans (hθd _).le)

end DifferentialGeometry.Analysis.ParameterSelection
