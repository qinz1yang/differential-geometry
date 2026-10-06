import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

/-!
# CH12-S45 / G1: logarithmic Grönwall comparison on a dyadic window

The order-zero step of the forward window (blueprint LTF04): along a static track the quantity
`φ(s) = (s⁻¹ g(s))(v, v) ≥ 0` has derivative `-s⁻² (g + 2 s Ric)(v, v)`, so a Ricci-defect
bound `|g + 2 s Ric| ≤ η g` gives `|φ'| ≤ (η / s) φ`.  This file proves the elementary
consequence `(t/u)^η φ(t) ≤ φ(u) ≤ (u/t)^η φ(t)`; for `u ≤ 2 t` the factor is at most
`2^η`.  `metric_variation_S45` packages it for the pair `(g_s(v,v), Ric_s(v,v))` of a Ricci flow.
-/

noncomputable section
open Set
namespace GC.LongTime.Ch12

/-- Upper comparison: `φ' ≤ (η/s) φ` on `[t,u]` gives `φ u ≤ (u/t)^η φ t`. -/
theorem gronwall_log_upper_S45 {φ d : ℝ → ℝ} {t u η : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hφ : ∀ s ∈ Icc t u, HasDerivAt φ (d s) s) (hd : ∀ s ∈ Icc t u, d s ≤ η / s * φ s) :
    φ u ≤ (u / t) ^ η * φ t := by
  have hψ : ∀ s ∈ Icc t u, HasDerivAt (fun x => φ x * x ^ (-η))
      (d s * s ^ (-η) + φ s * (-η * s ^ (-η - 1))) s := fun s hs =>
    (hφ s hs).mul (Real.hasDerivAt_rpow_const (Or.inl (ht.trans_le hs.1).ne'))
  have hanti : AntitoneOn (fun x => φ x * x ^ (-η)) (Icc t u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t u)
    · exact fun s hs => (hψ s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hψ s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hspos : 0 < s := ht.trans_le hs'.1
      rw [(hψ s hs').deriv]
      have h1 : s ^ (-η - 1) = s ^ (-η) / s := by
        rw [Real.rpow_sub hspos, Real.rpow_one]
      have h2 := hd s hs'
      have h3 : 0 < s ^ (-η) := Real.rpow_pos_of_pos hspos _
      rw [h1]
      have : d s * s ^ (-η) + φ s * (-η * (s ^ (-η) / s)) =
          (d s - η / s * φ s) * s ^ (-η) := by ring
      rw [this]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h3.le
  have key := hanti ⟨le_rfl, htu⟩ ⟨htu, le_rfl⟩ htu
  have hupos : 0 < u := ht.trans_le htu
  have hp1 : 0 < u ^ η := Real.rpow_pos_of_pos hupos _
  have hp2 : 0 < t ^ η := Real.rpow_pos_of_pos ht _
  simp only [Real.rpow_neg hupos.le, Real.rpow_neg ht.le, ← div_eq_mul_inv] at key
  rw [div_le_div_iff₀ hp1 hp2] at key
  rw [Real.div_rpow hupos.le ht.le, div_mul_eq_mul_div, le_div_iff₀ hp2]
  linarith [key]

/-- Lower comparison: `φ' ≥ -(η/s) φ` on `[t,u]` gives `φ t ≤ (u/t)^η φ u`. -/
theorem gronwall_log_lower_S45 {φ d : ℝ → ℝ} {t u η : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hφ : ∀ s ∈ Icc t u, HasDerivAt φ (d s) s) (hd : ∀ s ∈ Icc t u, -(η / s * φ s) ≤ d s) :
    φ t ≤ (u / t) ^ η * φ u := by
  have hψ : ∀ s ∈ Icc t u, HasDerivAt (fun x => φ x * x ^ η)
      (d s * s ^ η + φ s * (η * s ^ (η - 1))) s := fun s hs =>
    (hφ s hs).mul (Real.hasDerivAt_rpow_const (Or.inl (ht.trans_le hs.1).ne'))
  have hmono : MonotoneOn (fun x => φ x * x ^ η) (Icc t u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t u)
    · exact fun s hs => (hψ s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hψ s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hspos : 0 < s := ht.trans_le hs'.1
      rw [(hψ s hs').deriv]
      have h1 : s ^ (η - 1) = s ^ η / s := by
        rw [Real.rpow_sub hspos, Real.rpow_one]
      have h2 := hd s hs'
      have h3 : 0 < s ^ η := Real.rpow_pos_of_pos hspos _
      rw [h1]
      have : d s * s ^ η + φ s * (η * (s ^ η / s)) =
          (d s + η / s * φ s) * s ^ η := by ring
      rw [this]
      exact mul_nonneg (by linarith) h3.le
  have key := hmono ⟨le_rfl, htu⟩ ⟨htu, le_rfl⟩ htu
  have hupos : 0 < u := ht.trans_le htu
  have hp1 : 0 < u ^ η := Real.rpow_pos_of_pos hupos _
  have hp2 : 0 < t ^ η := Real.rpow_pos_of_pos ht _
  simp only at key
  rw [Real.div_rpow hupos.le ht.le, div_mul_eq_mul_div, le_div_iff₀ hp2]
  linarith [key]

/-- Order-zero metric variation along a Ricci flow with small Ricci defect.  `gv s = g_s(v,v)`
and `rv s = Ric_{g_s}(v,v)`, with `∂_s gv = -2 rv` and `|2 s rv + gv| ≤ η gv` on `[t,u]`; then
`φ(s) = gv(s)/s` satisfies `φ t ≤ (u/t)^η φ u` and `φ u ≤ (u/t)^η φ t`. -/
theorem metric_variation_S45 {gv rv : ℝ → ℝ} {t u η : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hflow : ∀ s ∈ Icc t u, HasDerivAt gv (-2 * rv s) s)
    (hdef : ∀ s ∈ Icc t u, |2 * s * rv s + gv s| ≤ η * gv s) :
    gv t / t ≤ (u / t) ^ η * (gv u / u) ∧ gv u / u ≤ (u / t) ^ η * (gv t / t) := by
  have hφ : ∀ s ∈ Icc t u, HasDerivAt (fun x => gv x / x)
      ((-2 * rv s * s - gv s) / s ^ 2) s := by
    intro s hs
    have hs0 : s ≠ 0 := (ht.trans_le hs.1).ne'
    have h := (hflow s hs).div (hasDerivAt_id' s) hs0
    convert h using 1
    ring
  have hbd : ∀ s ∈ Icc t u, |(-2 * rv s * s - gv s) / s ^ 2| ≤ η / s * (gv s / s) := by
    intro s hs
    have hspos : 0 < s := ht.trans_le hs.1
    have h1 := hdef s hs
    rw [abs_div, abs_of_pos (pow_pos hspos 2), div_le_iff₀ (pow_pos hspos 2)]
    have : |-2 * rv s * s - gv s| = |2 * s * rv s + gv s| := by
      rw [← abs_neg]; congr 1; ring
    rw [this]
    calc |2 * s * rv s + gv s| ≤ η * gv s := h1
      _ = η / s * (gv s / s) * s ^ 2 := by field_simp
  constructor
  · exact gronwall_log_lower_S45 ht htu hφ (fun s hs => by
      have := (abs_le.mp (hbd s hs)).1; linarith)
  · exact gronwall_log_upper_S45 ht htu hφ (fun s hs => by
      have := (abs_le.mp (hbd s hs)).2; linarith)

end GC.LongTime.Ch12
