import DifferentialGeometry.Analysis.Calculus.Inverse.GraphQuantitativeSuccessor

set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis
universe u v

theorem exists_bound_normal_graph_jets (m : ℕ) (C : ℝ) (hC0 : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (N : Type u) (E : Type v)
        [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        (e : N × E → N) (g : E → N) (x : E),
        ContDiffAt ℝ (max m 1 : ℕ) e (g x, x) →
        ContDiffAt ℝ (max m 1 : ℕ) g x →
        (∀ᶠ y in 𝓝 x, g y + e (g y, y) = 0) →
        ‖fderiv ℝ (fun n : N => e (n, x)) (g x)‖ ≤ 1 / 2 →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        (∀ i, i ≤ m → ‖iteratedFDeriv ℝ i e (g x, x)‖ ≤ C * δ) →
        ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B * δ := by
  induction m with
  | zero =>
    refine ⟨C, hC0, ?_⟩
    intro N E _ _ _ _ _ e g x _he _hg hrel _hsmall δ _hδ0 _hδ1 herror j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    have hvalue : g x = -e (g x, x) := eq_neg_of_add_eq_zero_left hrel.self_of_nhds
    calc
      ‖g x‖ = ‖e (g x, x)‖ := (congrArg norm hvalue).trans (norm_neg _)
      _ ≤ C * δ := by simpa only [norm_iteratedFDeriv_zero] using herror 0 le_rfl
  | succ m ih =>
    obtain ⟨B, hB0, hbound⟩ := ih
    let D : ℝ := max B 1
    let K : ℝ := (m.factorial : ℝ) * C * D ^ m
    let F : ℝ := (2 : ℝ) ^ m * ((m.factorial : ℝ) *
      ((m.factorial : ℝ) * (2 : ℝ) ^ (m + 1)) * (max K 1) ^ m) * K
    have hD1 : 1 ≤ D := le_max_right _ _
    have hD0 : 0 ≤ D := zero_le_one.trans hD1
    have hK0 : 0 ≤ K := by dsimp [K]; positivity
    have hF0 : 0 ≤ F := by dsimp [F]; positivity
    refine ⟨max B F, hF0.trans (le_max_right _ _), ?_⟩
    intro N E _ _ _ _ _ e g x he hg hrel hsmall δ hδ0 hδ1 herror
    have horder : max m 1 ≤ max (m + 1) 1 := by omega
    have hprior : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B * δ :=
      hbound N E e g x
        (he.of_le (by exact_mod_cast horder))
        (hg.of_le (by exact_mod_cast horder)) hrel hsmall δ hδ0 hδ1
        (fun i hi => herror i (hi.trans (Nat.le_succ m)))
    have hgraph (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
        ‖iteratedFDeriv ℝ i g x‖ ≤ D ^ i := by
      calc
        ‖iteratedFDeriv ℝ i g x‖ ≤ B * δ := hprior i him
        _ ≤ B := (mul_le_mul_of_nonneg_left hδ1 hB0).trans_eq (mul_one B)
        _ ≤ D := le_max_left _ _
        _ = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi
    have he' : ContDiffAt ℝ (m + 1 : ℕ) e (g x, x) :=
      he.of_le (by exact_mod_cast (le_max_left (m + 1) 1))
    have hg' : ContDiffAt ℝ (m + 1 : ℕ) g x :=
      hg.of_le (by exact_mod_cast (le_max_left (m + 1) 1))
    have hnext : ‖iteratedFDeriv ℝ (m + 1) g x‖ ≤ F * δ := by
      exact norm_iteratedFDeriv_normal_graph_succ_le e g x m he' hg' hrel hsmall
        C D δ hC0 hD1 hδ0 hδ1 (fun i _ hi => herror i hi) hgraph
    intro j hj
    by_cases hjm : j ≤ m
    · exact (hprior j hjm).trans (mul_le_mul_of_nonneg_right (le_max_left B F) hδ0)
    · have hjtop : j = m + 1 := by omega
      subst j
      exact hnext.trans (mul_le_mul_of_nonneg_right (le_max_right B F) hδ0)

end DifferentialGeometry.Analysis
