import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Translations of a metric quotient of a strictly convex plane

Let `Ψ : V → M` be a surjection from a strictly convex real normed space onto a metric space
whose fibres are exactly the orbits of an additive subgroup `Λ`, which is `1`-Lipschitz and
realises every distance by some lift (`dist (Ψ w) (Ψ w') = dist w w''` for some `w''` over
`Ψ w'`). This is what the developing map of a flat torus provides
(`FlatTorusDistance.lean`). Then

* every translation `w ↦ w + c` descends to an isometry `τ : M ≃ᵢ M`;
* for a segment `γ` of length `2s` in `M` there is such a `τ` with `τ (γ 0) = γ s` and
  `τ (γ s) = γ (2s)` (realising lifts of `γ 0, γ s, γ (2s)` are collinear by strict convexity).

The second item is the `τ`-producer consumed by W4-F7c's `false_of_translation_of_lt`
(LFR23's torus exclusion, route (ii)).
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.Analysis

variable {V M : Type*} [NormedAddCommGroup V] [MetricSpace M]
  {Ψ : V → M} {Λ : AddSubgroup V}

omit [MetricSpace M] in
private theorem apply_eq_of_apply_eq (hinv : ∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w)
    (hfib : ∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ) {w w' : V} (h : Ψ w = Ψ w') (c : V) :
    Ψ (w + c) = Ψ (w' + c) := by
  have := hinv (w + c) (w' - w) (hfib w w' h)
  rw [show w + c + (w' - w) = w' + c by abel] at this
  exact this.symm

private theorem dist_translate_le (hinv : ∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w)
    (hfib : ∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ) (hle : ∀ w w', dist (Ψ w) (Ψ w') ≤ dist w w')
    (hreal : ∀ w w', ∃ w'', Ψ w'' = Ψ w' ∧ dist (Ψ w) (Ψ w') = dist w w'') (c w w' : V) :
    dist (Ψ (w + c)) (Ψ (w' + c)) ≤ dist (Ψ w) (Ψ w') := by
  obtain ⟨w'', hw'', hd⟩ := hreal w w'
  rw [← apply_eq_of_apply_eq hinv hfib hw'' c, hd]
  exact (hle _ _).trans_eq (dist_add_right _ _ _)

/-- **Translations descend.** -/
theorem exists_isometryEquiv_translate (hsurj : Surjective Ψ)
    (hinv : ∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w) (hfib : ∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ)
    (hle : ∀ w w', dist (Ψ w) (Ψ w') ≤ dist w w')
    (hreal : ∀ w w', ∃ w'', Ψ w'' = Ψ w' ∧ dist (Ψ w) (Ψ w') = dist w w'') (c : V) :
    ∃ τ : M ≃ᵢ M, ∀ w, τ (Ψ w) = Ψ (w + c) := by
  let T : V → M → M := fun c x => Ψ (surjInv hsurj x + c)
  have hT : ∀ c w, T c (Ψ w) = Ψ (w + c) := fun c w =>
    apply_eq_of_apply_eq hinv hfib (surjInv_eq hsurj (Ψ w)) c
  have hTT : ∀ c x, T (-c) (T c x) = x := by
    intro c x
    obtain ⟨w, rfl⟩ := hsurj x
    rw [hT c w, hT (-c) (w + c), add_neg_cancel_right]
  have hdist : ∀ x x', dist (T c x) (T c x') = dist x x' := by
    intro x x'
    obtain ⟨w, rfl⟩ := hsurj x
    obtain ⟨w', rfl⟩ := hsurj x'
    rw [hT c w, hT c w']
    refine le_antisymm (dist_translate_le hinv hfib hle hreal c w w') ?_
    have := dist_translate_le hinv hfib hle hreal (-c) (w + c) (w' + c)
    rwa [add_neg_cancel_right, add_neg_cancel_right] at this
  let e : M ≃ M :=
    { toFun := T c
      invFun := T (-c)
      left_inv := hTT c
      right_inv := fun x => by simpa using hTT (-c) x }
  exact ⟨⟨e, Isometry.of_dist_eq hdist⟩, hT c⟩

/-- **Shift-segment producer.** A segment of length `2s` in the quotient is shifted along itself
by the descent of a translation. -/
theorem exists_isometryEquiv_shift_segment_of_quotient [NormedSpace ℝ V]
    [StrictConvexSpace ℝ V]
    (hsurj : Surjective Ψ) (hinv : ∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w)
    (hfib : ∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ) (hle : ∀ w w', dist (Ψ w) (Ψ w') ≤ dist w w')
    (hreal : ∀ w w', ∃ w'', Ψ w'' = Ψ w' ∧ dist (Ψ w) (Ψ w') = dist w w'')
    {γ : ℝ → M} {s : ℝ} (hs : 0 ≤ s)
    (hγ : ∀ t ∈ Icc 0 (2 * s), ∀ t' ∈ Icc 0 (2 * s), dist (γ t) (γ t') = |t - t'|) :
    ∃ τ : M ≃ᵢ M, τ (γ 0) = γ s ∧ τ (γ s) = γ (2 * s) := by
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * s) := ⟨le_rfl, by linarith⟩
  have h1 : s ∈ Icc 0 (2 * s) := ⟨hs, by linarith⟩
  have h2 : 2 * s ∈ Icc 0 (2 * s) := ⟨by linarith, le_rfl⟩
  have d01 : dist (γ 0) (γ s) = s := by rw [hγ 0 h0 s h1]; simp [abs_of_nonneg hs]
  have d12 : dist (γ s) (γ (2 * s)) = s := by
    rw [hγ s h1 (2 * s) h2, show s - 2 * s = -s by ring, abs_neg, abs_of_nonneg hs]
  have d02 : dist (γ 0) (γ (2 * s)) = 2 * s := by
    rw [hγ 0 h0 (2 * s) h2, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  obtain ⟨w₀, hw₀⟩ := hsurj (γ 0)
  obtain ⟨w₁', hw₁'⟩ := hsurj (γ s)
  obtain ⟨w₂', hw₂'⟩ := hsurj (γ (2 * s))
  obtain ⟨w₁, hw₁, hd₁⟩ := hreal w₀ w₁'
  obtain ⟨w₂, hw₂, hd₂⟩ := hreal w₁ w₂'
  rw [hw₁'] at hw₁
  rw [hw₂'] at hw₂
  rw [hw₀, hw₁'] at hd₁
  rw [hw₁, hw₂'] at hd₂
  have hle02 := hle w₀ w₂
  rw [hw₀, hw₂, d02] at hle02
  set a := w₁ - w₀
  set c := w₂ - w₁
  have ha : ‖a‖ = s := by rw [← dist_eq_norm, dist_comm, ← hd₁, d01]
  have hc : ‖c‖ = s := by rw [← dist_eq_norm, dist_comm, ← hd₂, d12]
  have hac : ‖a + c‖ = ‖a‖ + ‖c‖ := by
    refine le_antisymm (norm_add_le _ _) ?_
    rw [ha, hc, show a + c = w₂ - w₀ by simp [a, c], ← dist_eq_norm, dist_comm]
    linarith
  have heq : a = c := eq_of_norm_eq_of_norm_add_eq (ha.trans hc.symm) hac
  obtain ⟨τ, hτ⟩ := exists_isometryEquiv_translate hsurj hinv hfib hle hreal a
  refine ⟨τ, ?_, ?_⟩
  · rw [← hw₀, hτ, show w₀ + a = w₁ by simp [a], hw₁]
  · rw [← hw₁, hτ, heq, show w₁ + c = w₂ by simp [c], hw₂]

end DifferentialGeometry.Analysis
