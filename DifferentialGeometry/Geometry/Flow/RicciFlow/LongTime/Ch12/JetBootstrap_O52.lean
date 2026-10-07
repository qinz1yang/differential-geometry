import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# CH12-O52 G1a: jet bounds for compositions and the first-order bootstrap

Pure calculus input of the single-model core `L1` (`[FROZEN] CH12-O26`, step b2):

* `comp_jet_bound_O52`: Faà di Bruno on a compact value set — if `g` is smooth on an open `t`
  and `f` takes values in a compact `K ⊆ t` with jets `≤ B` (orders `1 … n`), then
  `‖D^n (g ∘ f)‖ ≤ C` with `C` depending only on `(g, t, K, n, B)`.
* `bootstrap_jet_bound_O52`: if `Dw = Φ (γ, w)` on an open set, `(γ, w)` stays in a compact
  `K` inside the smoothness domain of `Φ`, and the jets of `γ` of order `≤ n` are `≤ B`, then the
  jets of `w` of order `≤ n + 1` are bounded uniformly in `(γ, w)`.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Nat Topology

namespace GC.LongTime.Ch12

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Faà di Bruno on a compact value set.** -/
theorem comp_jet_bound_O52 {g : F → G} {t : Set F} (ht : IsOpen t) (hg : ContDiffOn ℝ ∞ g t)
    {K : Set F} (hK : IsCompact K) (hKt : K ⊆ t) (n : ℕ) (B : ℝ) :
    ∃ C : ℝ, ∀ (f : E → F) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ f V → MapsTo f V K →
      (∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ y ∈ V, ‖iteratedFDeriv ℝ i f y‖ ≤ B) →
      ∀ y ∈ V, ‖iteratedFDeriv ℝ n (g ∘ f) y‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ Ci : ℝ, ∀ z ∈ K, ‖iteratedFDerivWithin ℝ i g t z‖ ≤ Ci := by
    intro i
    have hc : ContinuousOn (iteratedFDerivWithin ℝ i g t) t :=
      hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) ht.uniqueDiffOn
    exact hK.exists_bound_of_continuousOn (hc.mono hKt)
  choose Cg hCg using hb
  set Cm : ℝ := ∑ i ∈ Finset.range (n + 1), |Cg i| with hCm_def
  set D : ℝ := max B 1 with hD_def
  refine ⟨n ! * Cm * D ^ n, ?_⟩
  intro f V hV hf hfK hfB y hy
  have hCm : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g t (f y)‖ ≤ Cm := by
    intro i hi
    calc ‖iteratedFDerivWithin ℝ i g t (f y)‖ ≤ Cg i := hCg i (f y) (hfK hy)
      _ ≤ |Cg i| := le_abs_self _
      _ ≤ Cm := Finset.single_le_sum (f := fun i => |Cg i|) (fun j _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i f V y‖ ≤ D ^ i := by
    intro i h1 hi
    rw [iteratedFDerivWithin_of_isOpen i hV hy]
    calc ‖iteratedFDeriv ℝ i f y‖ ≤ B := hfB i h1 hi y hy
      _ ≤ D := le_max_left _ _
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ (le_max_right _ _) h1
  have h := norm_iteratedFDerivWithin_comp_le hg hf (by exact_mod_cast le_top) ht.uniqueDiffOn
    hV.uniqueDiffOn (fun z hz => hKt (hfK hz)) hy hCm hD
  rwa [iteratedFDerivWithin_of_isOpen n hV hy] at h

/-- **First-order bootstrap.** `Dw = Φ (γ, w)` with `(γ, w)` in a compact subset of the
smoothness domain of `Φ`: jets of `γ` up to order `n` bounded ⇒ jets of `w` up to order `n + 1`
bounded, uniformly in `(γ, w, V)`. -/
theorem bootstrap_jet_bound_O52 {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : P × W → (E →L[ℝ] W)} {t : Set (P × W)} (ht : IsOpen t) (hΦ : ContDiffOn ℝ ∞ Φ t)
    {K : Set (P × W)} (hK : IsCompact K) (hKt : K ⊆ t) (B : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ (γ : E → P) (w : E → W) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ γ V →
      ContDiffOn ℝ ∞ w V → (∀ y ∈ V, (γ y, w y) ∈ K) →
      (∀ y ∈ V, fderiv ℝ w y = Φ (γ y, w y)) →
      (∀ i : ℕ, i ≤ n → ∀ y ∈ V, ‖iteratedFDeriv ℝ i γ y‖ ≤ B) →
      ∀ i : ℕ, i ≤ n + 1 → ∀ y ∈ V, ‖iteratedFDeriv ℝ i w y‖ ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C0, hC0⟩ := (hK.image continuous_snd).isBounded.exists_norm_le
    obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn (hΦ.continuousOn.mono hKt)
    refine ⟨max C0 C1, fun γ w V _ _ _ hKV hODE _ i hi y hy => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · rw [norm_iteratedFDeriv_zero]
      exact (hC0 _ ⟨_, hKV y hy, rfl⟩).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one, hODE y hy]
      exact (hC1 _ (hKV y hy)).trans (le_max_right _ _)
  | succ n ih =>
    obtain ⟨Cn, hCn⟩ := ih
    obtain ⟨Cc, hCc⟩ := comp_jet_bound_O52 (E := E) ht hΦ hK hKt (n + 1) (B + Cn)
    refine ⟨max Cn Cc, ?_⟩
    intro γ w V hV hγ hw hKV hODE hγB i hi y hy
    have hlow := hCn γ w V hV hγ hw hKV hODE (fun i hi => hγB i (by omega))
    rcases Nat.lt_or_ge i (n + 2) with h | h
    · exact (hlow i (by omega) y hy).trans (le_max_left _ _)
    · obtain rfl : i = n + 2 := by omega
      rw [← norm_iteratedFDeriv_fderiv]
      have heq : fderiv ℝ w =ᶠ[𝓝 y] (Φ ∘ fun x => (γ x, w x)) := by
        filter_upwards [hV.mem_nhds hy] with x hx using hODE x hx
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) (n + 1)).eq_of_nhds]
      refine (hCc (fun x => (γ x, w x)) V hV (hγ.prodMk hw) (fun x hx => hKV x hx) ?_ y hy).trans
        (le_max_right _ _)
      intro l _ hl x hx
      have hγa : ContDiffAt ℝ ∞ γ x := hγ.contDiffAt (hV.mem_nhds hx)
      have hwa : ContDiffAt ℝ ∞ w x := hw.contDiffAt (hV.mem_nhds hx)
      rw [iteratedFDeriv_prodMk hγa hwa (by exact_mod_cast le_top),
        ContinuousMultilinearMap.opNorm_prod]
      have h1 := hγB l hl x hx
      have h2 := hlow l (by omega) x hx
      have h3 : 0 ≤ ‖iteratedFDeriv ℝ l γ x‖ := norm_nonneg _
      have h4 : 0 ≤ ‖iteratedFDeriv ℝ l w x‖ := norm_nonneg _
      exact max_le (by linarith) (by linarith)

end GC.LongTime.Ch12
