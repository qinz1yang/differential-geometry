import DifferentialGeometry.Analysis.Calculus.Inverse.MonotoneGraph
import DifferentialGeometry.Analysis.Calculus.Cutoff.SmoothTransition
import Mathlib.Topology.Homeomorph.Defs

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Topology.Morse

private theorem exists_contDiffOn_saddle_band_profile_graph
    {β A : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hA : ContDiff ℝ ∞ A)
    {s c a b : ℝ} (hab : a < b) (hAb : A b = 0)
    (hderiv : ∀ t ∈ Ioo a b, deriv A t < 0) :
    let U : Set (ℝ × ℝ) := {z | 0 < β z.1 ∧
      s + c - β z.1 * A a < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 < s + c}
    ∃ g : (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ g U ∧
      (∀ z ∈ U, g z ∈ Ioo a b ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + c - β z.1 * A (g z)) ∧
      ∀ z ∈ U, ∀ t ∈ Icc a b,
        ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + c - β z.1 * A t ↔ t = g z) ∧
        ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + c - β z.1 * A t ↔ g z ≤ t) ∧
        ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 < s + c - β z.1 * A t ↔ g z < t) := by
  let q : ℝ × ℝ → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2
  let U : Set (ℝ × ℝ) := {z | 0 < β z.1 ∧ s + c - β z.1 * A a < q z ∧ q z < s + c}
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (hβ.continuous.comp continuous_fst)).inter
      ((isOpen_lt (by fun_prop) hq.continuous).inter (isOpen_lt hq.continuous continuous_const))
  let F : (ℝ × ℝ) × ℝ → ℝ := fun p => β p.1.1 * A p.2 - (s + c - q p.1)
  have hF : ContDiff ℝ ∞ F := by dsimp [F]; fun_prop
  have hFt (z : ℝ × ℝ) (t : ℝ) :
      HasDerivAt (fun t => F (z, t)) (β z.1 * deriv A t) t := by
    exact (((hA.differentiable (by simp) t).hasDerivAt).const_mul (β z.1)).sub_const (s + c - q z)
  obtain ⟨g, hg, hgeq, hsign⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_implicit_graph_of_deriv_neg
      (by simp : (∞ : ℕ∞ω) ≠ 0) hU hab hF.contDiffOn
      (fun z _ => (hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (fun z hz t ht => by rw [(hFt z t).deriv]; exact mul_neg_of_pos_of_neg hz.1 (hderiv t ht))
      (fun z hz => by dsimp [F]; linarith [hz.2.1])
      (fun z hz => by dsimp [F]; rw [hAb, mul_zero]; linarith [hz.2.2])
  refine ⟨g, hg, ?_, ?_⟩
  · intro z hz
    refine ⟨(hgeq z hz).1, ?_⟩
    have heq := (hgeq z hz).2
    dsimp [F] at heq
    change q z = _
    linarith
  · intro z hz t ht
    obtain ⟨heq, hle, hlt⟩ := hsign z hz t ht
    change (q z = s + c - β z.1 * A t ↔ t = g z) ∧
      (q z ≤ s + c - β z.1 * A t ↔ g z ≤ t) ∧
      (q z < s + c - β z.1 * A t ↔ g z < t)
    refine ⟨?_, ?_, ?_⟩
    · convert heq using 1
      dsimp [F]
      constructor <;> intro h <;> linarith
    · rw [← not_lt, ← not_lt, ← hlt]
      dsimp [F]
      constructor <;> intro h <;> linarith
    · rw [← not_le, ← not_le, ← hle]
      dsimp [F]
      constructor <;> intro h <;> linarith

theorem exists_contDiffOn_saddle_band_cutoff_graph
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {s t₀ a : ℝ} (ht₀ : 0 < t₀) (ha : a < t₀ / 2)
    {θ : ℝ × ℝ → ℝ}
    (hθ : ∀ t u, θ (t, u) =
      1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * β u) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ ∃ g : (ℝ × ℝ) → ℝ,
      ContDiffOn ℝ ∞ g U ∧ (∀ z ∈ U, g z ∈ Ioo a (t₀ / 2)) ∧
      (∀ z ∈ U, 0 < β z.1 ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 =
          s + g z + θ (g z, z.1) * (t₀ - g z)) ∧
      ∀ z : ℝ × ℝ, 0 < β z.1 → ∀ t ∈ Ioo a (t₀ / 2),
        ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t + θ (t, z.1) * (t₀ - t) ↔
          z ∈ U ∧ t = g z) := by
  let A : ℝ → ℝ := fun t =>
    (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * (t₀ - t)
  have hwidth : t₀ / 2 - t₀ / 4 = t₀ / 4 := by ring
  have hab : t₀ / 4 < t₀ / 2 := by linarith
  have hbc : t₀ / 2 ≤ t₀ := by linarith
  have hA : ContDiff ℝ ∞ A := by
    simpa only [hwidth] using Real.smoothTransition.contDiff_one_sub_mul_sub (t₀ / 4) (t₀ / 2) t₀
  have hAb : A (t₀ / 2) = 0 := by
    simpa only [A, hwidth] using Real.smoothTransition.one_sub_mul_sub_eq_zero (c := t₀) hab le_rfl
  have hAanti : StrictAntiOn A (Iio (t₀ / 2)) := by
    simpa only [hwidth] using Real.smoothTransition.strictAntiOn_one_sub_mul_sub hab hbc
  have hAderiv (t : ℝ) (ht : t < t₀ / 2) : deriv A t < 0 := by
    simpa only [hwidth] using Real.smoothTransition.deriv_one_sub_mul_sub_neg hab hbc ht
  have hprofile (t u : ℝ) : t + θ (t, u) * (t₀ - t) = t₀ - β u * A t := by
    rw [hθ]
    dsimp only [A]
    ring
  let q : ℝ × ℝ → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2
  let U : Set (ℝ × ℝ) := {z | 0 < β z.1 ∧ s + t₀ - β z.1 * A a < q z ∧ q z < s + t₀}
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (hβ.continuous.comp continuous_fst)).inter
      ((isOpen_lt (by fun_prop) hq.continuous).inter (isOpen_lt hq.continuous continuous_const))
  obtain ⟨g, hg, hgeq, hsign⟩ := exists_contDiffOn_saddle_band_profile_graph
    hβ hA (s := s) ha hAb (fun t ht => hAderiv t ht.2)
  have hmodel (z : ℝ × ℝ) (t : ℝ) :
      q z = s + t + θ (t, z.1) * (t₀ - t) ↔ q z = s + t₀ - β z.1 * A t := by
    rw [add_assoc, hprofile, add_sub_assoc]
  refine ⟨U, hU, g, hg, (fun z hz => (hgeq z hz).1), ?_, ?_⟩
  · intro z hz
    exact ⟨hz.1, (hmodel z (g z)).mpr (hgeq z hz).2⟩
  · intro z hz t ht
    change q z = _ ↔ _
    rw [hmodel]
    constructor
    · intro heq
      have hAt : 0 < A t := by
        have hχ : 0 < 1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4)) :=
          sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one
            ((div_lt_one (by linarith : 0 < t₀ / 4)).mpr (by linarith [ht.2])))
        exact mul_pos hχ (by linarith [ht.2])
      have hlow := mul_lt_mul_of_pos_left (hAanti ha ht.2 ht.1) hz
      have hzU : z ∈ U := ⟨hz, by linarith, by
        have := mul_pos hz hAt
        linarith⟩
      exact ⟨hzU, ((hsign z hzU t (Ioo_subset_Icc_self ht)).1).mp heq⟩
    · rintro ⟨hzU, rfl⟩
      exact (hgeq z hzU).2

theorem exists_isOpen_inter_eq_graph_of_saddle_band_cutoff
    {E : Type*} [TopologicalSpace E] (B : (ℝ × ℝ) ≃ₜ E)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {s t₀ a ell : ℝ}
    (ht₀ : 0 < t₀) (ha : a < t₀ / 2) {θ : ℝ × ℝ → ℝ}
    (hθ : ∀ t u, θ (t, u) =
      1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * β u)
    {S Z : Set (E × ℝ)} (hZ : IsOpen Z)
    (hmodel : Z ∩ S = Z ∩ {q |
      (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
        s + (q.2 - ell) + θ (q.2 - ell, (B.symm q.1).1) * (t₀ - (q.2 - ell))}) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ ∃ g : (ℝ × ℝ) → ℝ,
      ContDiffOn ℝ ∞ g U ∧ (∀ z ∈ U, g z ∈ Ioo a (t₀ / 2)) ∧
      ∃ W : Set (E × ℝ), IsOpen W ∧ W ⊆ Z ∧
        W ⊆ {q | B.symm q.1 ∈ U ∧ q.2 - ell ∈ Ioo a (t₀ / 2)} ∧
        Z ∩ S ∩ {q | 0 < β (B.symm q.1).1 ∧ q.2 - ell ∈ Ioo a (t₀ / 2)} ⊆ W ∧
        W ∩ S = W ∩ {q | q.2 = ell + g (B.symm q.1)} := by
  obtain ⟨U, hU, g, hg, hgt, hgeq, hgraph⟩ :=
    exists_contDiffOn_saddle_band_cutoff_graph hβ (s := s) ht₀ ha hθ
  let W := Z ∩ {q : E × ℝ | B.symm q.1 ∈ U ∧ q.2 - ell ∈ Ioo a (t₀ / 2)}
  have hW : IsOpen W := hZ.inter
    ((hU.preimage (B.symm.continuous.comp continuous_fst)).inter
      (isOpen_Ioo.preimage (continuous_snd.sub continuous_const)))
  have hUpos (z : ℝ × ℝ) (hz : z ∈ U) : 0 < β z.1 := (hgeq z hz).1
  refine ⟨U, hU, g, hg, hgt, W, hW, inter_subset_left, inter_subset_right, ?_, ?_⟩
  · rintro q ⟨hq, hβq, ht⟩
    have heq := (hmodel.subset hq).2
    exact ⟨hq.1, ((hgraph _ hβq _ ht).mp heq).1, ht⟩
  · ext q
    constructor
    · rintro ⟨hq, hqS⟩
      have heq := (hmodel.subset ⟨hq.1, hqS⟩).2
      have ht := ((hgraph _ (hUpos _ hq.2.1) _ hq.2.2).mp heq).2
      exact ⟨hq, by change q.2 = _; linarith⟩
    · rintro ⟨hq, hqg⟩
      change q.2 = ell + g (B.symm q.1) at hqg
      refine ⟨hq, (hmodel.symm.subset ⟨hq.1, ?_⟩).2⟩
      apply (hgraph _ (hUpos _ hq.2.1) _ hq.2.2).mpr
      exact ⟨hq.2.1, by linarith⟩

end DifferentialGeometry.Topology.Morse
