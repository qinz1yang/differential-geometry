import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Two-sided Grönwall estimate on a closed interval

Mathlib's `dist_le_of_approx_trajectories_ODE_of_mem` compares approximate solutions forward in time
from the left endpoint. For local flows (CM4.b, lane CM-L) the initial time `t₀` sits inside
`[a, b]` and derivatives are one-sided at the endpoints (`HasDerivWithinAt … (Icc a b)`):

* `dist_le_gronwallBound_of_approx_trajectories_Icc`: two approximate solutions of a `K`-Lipschitz field
  satisfy `dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) |t - t₀|` on `[a, b]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Forward half: from `t₀` to the right endpoint. -/
theorem dist_le_gronwallBound_forward_Icc {v : ℝ → X → X} {S : Set X} {K : ℝ≥0}
    (hv : ∀ t, LipschitzOnWith K (v t) S) {f g f' g' : ℝ → X} {a b t₀ εf εg δ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t)
    (f_bound : ∀ t ∈ Icc a b, dist (f' t) (v t (f t)) ≤ εf)
    (g_bound : ∀ t ∈ Icc a b, dist (g' t) (v t (g t)) ≤ εg)
    (hfS : ∀ t ∈ Icc a b, f t ∈ S) (hgS : ∀ t ∈ Icc a b, g t ∈ S)
    (h0 : dist (f t₀) (g t₀) ≤ δ) :
    ∀ t ∈ Icc t₀ b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - t₀) := by
  have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  have hsubIco : ∀ s ∈ Ico t₀ b, s ∈ Ico a b := fun s hs => ⟨ht₀.1.trans hs.1, hs.2⟩
  exact dist_le_of_approx_trajectories_ODE_of_mem (v := v) (s := fun _ => S) (K := K)
    (fun s _ => hv s) (fun s hs => (hf s (hsub hs)).continuousWithinAt.mono hsub)
    (fun s hs => (hf s (Ico_subset_Icc_self (hsubIco s hs))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (hsubIco s hs)))
    (fun s hs => f_bound s (Ico_subset_Icc_self (hsubIco s hs)))
    (fun s hs => hfS s (Ico_subset_Icc_self (hsubIco s hs)))
    (fun s hs => (hg s (hsub hs)).continuousWithinAt.mono hsub)
    (fun s hs => (hg s (Ico_subset_Icc_self (hsubIco s hs))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (hsubIco s hs)))
    (fun s hs => g_bound s (Ico_subset_Icc_self (hsubIco s hs)))
    (fun s hs => hgS s (Ico_subset_Icc_self (hsubIco s hs))) h0

/-- **Two-sided Grönwall on `[a, b]`** with the initial time `t₀ ∈ [a, b]`. -/
theorem dist_le_gronwallBound_of_approx_trajectories_Icc {v : ℝ → X → X} {S : Set X} {K : ℝ≥0}
    (hv : ∀ t, LipschitzOnWith K (v t) S) {f g f' g' : ℝ → X} {a b t₀ εf εg δ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t)
    (f_bound : ∀ t ∈ Icc a b, dist (f' t) (v t (f t)) ≤ εf)
    (g_bound : ∀ t ∈ Icc a b, dist (g' t) (v t (g t)) ≤ εg)
    (hfS : ∀ t ∈ Icc a b, f t ∈ S) (hgS : ∀ t ∈ Icc a b, g t ∈ S)
    (h0 : dist (f t₀) (g t₀) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) |t - t₀| := by
  intro t ht
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact dist_le_gronwallBound_forward_Icc hv ht₀ hf hg f_bound g_bound hfS hgS h0 t ⟨h, ht.2⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    -- reverse time: `s ↦ f (-s)` on `[-b, -a]` solves the field `-v (-s)`
    have hneg : ∀ {φ φ' : ℝ → X}, (∀ s ∈ Icc a b, HasDerivWithinAt φ (φ' s) (Icc a b) s) →
        ∀ s ∈ Icc (-b) (-a), HasDerivWithinAt (fun u => φ (-u)) (-φ' (-s)) (Icc (-b) (-a)) s := by
      intro φ φ' hφ s hs
      have hs' : -s ∈ Icc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hmaps : MapsTo (fun u : ℝ => -u) (Icc (-b) (-a)) (Icc a b) :=
        fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have h1 := (hφ (-s) hs').scomp s ((hasDerivAt_neg s).hasDerivWithinAt) hmaps
      simp only [neg_one_smul] at h1
      exact h1
    have hvneg : ∀ t, LipschitzOnWith K (fun z => -v (-t) z) S := fun t =>
      LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
        rw [dist_neg_neg]; exact (hv (-t)).dist_le_mul x hx y hy
    have hmem : ∀ s ∈ Icc (-b) (-a), -s ∈ Icc a b :=
      fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hres := dist_le_gronwallBound_forward_Icc (v := fun s z => -v (-s) z) (S := S) (K := K)
      (f := fun u => f (-u)) (g := fun u => g (-u))
      (f' := fun s => -f' (-s)) (g' := fun s => -g' (-s))
      (a := -b) (b := -a) (t₀ := -t₀) hvneg ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩
      (hneg hf) (hneg hg)
      (fun s hs => by rw [dist_neg_neg]; exact f_bound _ (hmem s hs))
      (fun s hs => by rw [dist_neg_neg]; exact g_bound _ (hmem s hs))
      (fun s hs => hfS _ (hmem s hs)) (fun s hs => hgS _ (hmem s hs))
      (by simpa using h0) (-t) ⟨by linarith, by linarith [ht.1]⟩
    simpa [sub_eq_add_neg, add_comm] using hres

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
