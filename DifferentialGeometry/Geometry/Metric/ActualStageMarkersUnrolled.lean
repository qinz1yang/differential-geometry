import DifferentialGeometry.Geometry.Metric.ActualCloudCutoffSequence

/-!
# CFS29/CFS30 for one, two and three explicit stages (unrolled form)

Blueprint `master207B.tex`, CFS31 (B:3783–3855) with CFS29/CFS30, in the form GAF02 (B:5797)
uses it: the stages are given separately (`Q_k`, `P_k`, `ψ_k`, `S_k`, `sel_k`), the stage
outputs are `g₁ = Ψ₀ ∘ F`, `g₂ = Ψ₁ ∘ g₁`, `g₃ = Ψ₂ ∘ g₂` with `Ψ_k = adjustmentMap Q_k P_k ψ_k`,
and the conclusions of `actualCloud_scalar_zero_marker_bound` are stated at these outputs:

* every marker with `R_a < ρ/16` vanishes exactly at every stage output;
* (AM0) on the segment `[F p, g_n p]` (in particular at `g_n p`) once `‖g_n − F‖ ≤ Eρ`,
  `E ≤ 1/512`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **CFS29/CFS30 for one stage** `g₁ = Ψ₀ ∘ F`: small markers vanish at `g₁`, and (AM0) holds on
`[F p, g₁ p]` when `‖g₁ − F‖ ≤ Eρ`, `E ≤ 1/512`. -/
theorem stage_markers_one_GAF7 {A X : Type*}
    (v : A → H →L[ℝ] ℝ) (hv : ∀ a, ‖v a‖ ≤ 1) (R : A → ℝ) (hR : ∀ a, 0 < R a)
    (ρ : X → ℝ) (ζ : A → X → ℝ) (hζ0 : ∀ a p, 0 ≤ ζ a p) (F : X → H)
    (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (hcomp : ∀ a p, 0 < ζ a p → 3 / 4 * R a ≤ ρ p ∧ ρ p ≤ 5 / 4 * R a)
    (Q₀ : Submodule ℝ H) (P₀ : H → H) (hP₀ : ∀ z, P₀ z ∈ Q₀) (ψ₀ : H → ℝ)
    (hret₀ : ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₀ ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₀ᗮ)
    (S₀ : Set H) (sel₀ : H → X) {σ₀ : ℝ}
    (hsup₀ : ∀ a q, 0 < v a (Q₀.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hfull₀ : ∀ q, Q₀.starProjection (F q) ∈ S₀ → ∃ a, v a (Q₀.starProjection (F q)) = R a)
    (hsel₀ : ∀ x ∈ S₀, Q₀.starProjection (F (sel₀ x)) = x) (hσ₀ : 0 < σ₀)
    (hloc₀ : ∀ q, ψ₀ (F q) ≠ 0 → Q₀.starProjection (F q) ∈ S₀)
    (hnear₀ : ∀ x ∈ S₀, ∀ z ∈ ball x (σ₀ * ρ (sel₀ x)), ∀ q,
      Q₀.starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (P₀ z) = 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ q, ‖adjustmentMap Q₀ P₀ ψ₀ (F q) - F q‖ ≤ E * ρ q) :
    (∀ q a, R a < ρ q / 16 → v a (adjustmentMap Q₀ P₀ ψ₀ (F q)) = 0) ∧
      ∀ a p, ζ a p = 0 → ∀ z ∈ segment ℝ (F p) (adjustmentMap Q₀ P₀ ψ₀ (F p)),
        |v a z| ≤ R a / 32 := by
  have he : (0 : ℝ) ≤ 3 * σ₀ / 10 := by positivity
  have h := actualCloud_scalar_zero_marker_bound v hv R hR ρ ζ hζ0 F hvF hcomp 1
    (fun _ => Q₀) (fun _ => P₀) (fun _ => hP₀) (fun _ => ψ₀)
    (fun k q => if k = 0 then F q else adjustmentMap Q₀ P₀ ψ₀ (F q)) (fun q => by simp)
    (fun k hk q => by
      obtain rfl : k = 0 := by omega
      simp)
    (fun _ _ => hret₀) (fun _ => S₀) (fun _ => sel₀) (fun _ => σ₀) (fun _ => 0)
    (fun _ _ => hsup₀)
    (fun k hk q hq => by
      obtain rfl : k = 0 := by omega
      exact hfull₀ q (hloc₀ q (by simpa using hq)))
    (fun _ _ => hsel₀) (fun _ _ => hσ₀) (fun _ _ => he)
    (fun k hk q hq => by
      obtain rfl : k = 0 := by omega
      exact hloc₀ q (by simpa using hq))
    (fun k hk q _ => by
      obtain rfl : k = 0 := by omega
      simp)
    (fun _ _ => hnear₀) hE hE512 (fun q => by simpa using hcum q)
  refine ⟨fun q a ha => by simpa using h.1 1 le_rfl q a ha, fun a p hζ z hz => ?_⟩
  exact h.2 a p hζ z (by simpa using hz)

/-- **CFS29/CFS30 for two stages** `g₁ = Ψ₀ ∘ F`, `g₂ = Ψ₁ ∘ g₁`: small markers vanish at `g₁`
and `g₂`, and (AM0) holds on `[F p, g₂ p]` when `‖g₂ − F‖ ≤ Eρ`, `E ≤ 1/512`. -/
theorem stage_markers_two_GAF7 {A X : Type*}
    (v : A → H →L[ℝ] ℝ) (hv : ∀ a, ‖v a‖ ≤ 1) (R : A → ℝ) (hR : ∀ a, 0 < R a)
    (ρ : X → ℝ) (ζ : A → X → ℝ) (hζ0 : ∀ a p, 0 ≤ ζ a p) (F : X → H)
    (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (hcomp : ∀ a p, 0 < ζ a p → 3 / 4 * R a ≤ ρ p ∧ ρ p ≤ 5 / 4 * R a)
    (Q₀ Q₁ : Submodule ℝ H) (P₀ P₁ : H → H) (hP₀ : ∀ z, P₀ z ∈ Q₀) (hP₁ : ∀ z, P₁ z ∈ Q₁)
    (ψ₀ ψ₁ : H → ℝ)
    (hret₀ : ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₀ ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₀ᗮ)
    (hret₁ : ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₁ ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₁ᗮ)
    (S₀ S₁ : Set H) (sel₀ sel₁ : H → X) {σ₀ σ₁ e₁ : ℝ}
    (hsup₀ : ∀ a q, 0 < v a (Q₀.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hsup₁ : ∀ a q, 0 < v a (Q₁.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hfull₀ : ∀ q, Q₀.starProjection (F q) ∈ S₀ → ∃ a, v a (Q₀.starProjection (F q)) = R a)
    (hfull₁ : ∀ q, Q₁.starProjection (F q) ∈ S₁ → ∃ a, v a (Q₁.starProjection (F q)) = R a)
    (hsel₀ : ∀ x ∈ S₀, Q₀.starProjection (F (sel₀ x)) = x)
    (hsel₁ : ∀ x ∈ S₁, Q₁.starProjection (F (sel₁ x)) = x) (hσ₀ : 0 < σ₀) (hσ₁ : 0 < σ₁)
    (he₁ : e₁ ≤ 3 * σ₁ / 10)
    (hloc₀ : ∀ q, ψ₀ (F q) ≠ 0 → Q₀.starProjection (F q) ∈ S₀)
    (hloc₁ : ∀ q, ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q)) ≠ 0 → Q₁.starProjection (F q) ∈ S₁)
    (herr₁ : ∀ q, ‖adjustmentMap Q₀ P₀ ψ₀ (F q) - F q‖ ≤ e₁ * ρ q)
    (hnear₀ : ∀ x ∈ S₀, ∀ z ∈ ball x (σ₀ * ρ (sel₀ x)), ∀ q,
      Q₀.starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (P₀ z) = 0)
    (hnear₁ : ∀ x ∈ S₁, ∀ z ∈ ball x (σ₁ * ρ (sel₁ x)), ∀ q,
      Q₁.starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (P₁ z) = 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ q, ‖adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q)) - F q‖ ≤ E * ρ q) :
    (∀ q a, R a < ρ q / 16 → v a (adjustmentMap Q₀ P₀ ψ₀ (F q)) = 0) ∧
      (∀ q a, R a < ρ q / 16 →
        v a (adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q))) = 0) ∧
      ∀ a p, ζ a p = 0 → ∀ z ∈ segment ℝ (F p)
        (adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F p))), |v a z| ≤ R a / 32 := by
  have he₀ : (0 : ℝ) ≤ 3 * σ₀ / 10 := by positivity
  have h := actualCloud_scalar_zero_marker_bound v hv R hR ρ ζ hζ0 F hvF hcomp 2
    (fun k => if k = 0 then Q₀ else Q₁) (fun k => if k = 0 then P₀ else P₁)
    (fun k z => by
      by_cases hk : k = 0
      · simpa [hk] using hP₀ z
      · simpa [hk] using hP₁ z)
    (fun k => if k = 0 then ψ₀ else ψ₁)
    (fun k q => if k = 0 then F q else if k = 1 then adjustmentMap Q₀ P₀ ψ₀ (F q) else
      adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q))) (fun q => by simp)
    (fun k hk q => by
      interval_cases k <;> simp)
    (fun k hk => by
      interval_cases k
      · simpa using hret₀
      · simpa using hret₁)
    (fun k => if k = 0 then S₀ else S₁) (fun k => if k = 0 then sel₀ else sel₁)
    (fun k => if k = 0 then σ₀ else σ₁) (fun k => if k = 0 then 0 else e₁)
    (fun k hk => by
      interval_cases k
      · simpa using hsup₀
      · simpa using hsup₁)
    (fun k hk q hq => by
      interval_cases k
      · simp only [ite_true] at hq ⊢
        exact hfull₀ q (hloc₀ q hq)
      · simp only [one_ne_zero, ite_false, ite_true] at hq ⊢
        exact hfull₁ q (hloc₁ q hq))
    (fun k hk => by
      interval_cases k
      · simpa using hsel₀
      · simpa using hsel₁)
    (fun k hk => by
      interval_cases k
      · simpa using hσ₀
      · simpa using hσ₁)
    (fun k hk => by
      interval_cases k
      · simpa using he₀
      · simpa using he₁)
    (fun k hk q hq => by
      interval_cases k
      · simp only [ite_true] at hq ⊢
        exact hloc₀ q hq
      · simp only [one_ne_zero, ite_false, ite_true] at hq ⊢
        exact hloc₁ q hq)
    (fun k hk q _ => by
      interval_cases k
      · simp
      · simpa using herr₁ q)
    (fun k hk => by
      interval_cases k
      · simpa using hnear₀
      · simpa using hnear₁)
    hE hE512 (fun q => by simpa using hcum q)
  refine ⟨fun q a ha => by simpa using h.1 1 (by norm_num) q a ha,
    fun q a ha => by simpa using h.1 2 le_rfl q a ha, fun a p hζ z hz => ?_⟩
  exact h.2 a p hζ z (by simpa using hz)

/-- **CFS29/CFS30 for three stages** `g₁ = Ψ₀ ∘ F`, `g₂ = Ψ₁ ∘ g₁`, `g₃ = Ψ₂ ∘ g₂`: small markers
vanish at `g₁`, `g₂`, `g₃`, and (AM0) holds on `[F p, g₃ p]` when `‖g₃ − F‖ ≤ Eρ`,
`E ≤ 1/512`. -/
theorem stage_markers_three_GAF7 {A X : Type*}
    (v : A → H →L[ℝ] ℝ) (hv : ∀ a, ‖v a‖ ≤ 1) (R : A → ℝ) (hR : ∀ a, 0 < R a)
    (ρ : X → ℝ) (ζ : A → X → ℝ) (hζ0 : ∀ a p, 0 ≤ ζ a p) (F : X → H)
    (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (hcomp : ∀ a p, 0 < ζ a p → 3 / 4 * R a ≤ ρ p ∧ ρ p ≤ 5 / 4 * R a)
    (Q₀ Q₁ Q₂ : Submodule ℝ H) (P₀ P₁ P₂ : H → H) (hP₀ : ∀ z, P₀ z ∈ Q₀)
    (hP₁ : ∀ z, P₁ z ∈ Q₁) (hP₂ : ∀ z, P₂ z ∈ Q₂) (ψ₀ ψ₁ ψ₂ : H → ℝ)
    (hret₀ : ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₀ ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₀ᗮ)
    (hret₁ : ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₁ ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₁ᗮ)
    (hret₂ : ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₂ ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q₂ᗮ)
    (S₀ S₁ S₂ : Set H) (sel₀ sel₁ sel₂ : H → X) {σ₀ σ₁ σ₂ e₁ e₂ : ℝ}
    (hsup₀ : ∀ a q, 0 < v a (Q₀.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hsup₁ : ∀ a q, 0 < v a (Q₁.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hsup₂ : ∀ a q, 0 < v a (Q₂.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hfull₀ : ∀ q, Q₀.starProjection (F q) ∈ S₀ → ∃ a, v a (Q₀.starProjection (F q)) = R a)
    (hfull₁ : ∀ q, Q₁.starProjection (F q) ∈ S₁ → ∃ a, v a (Q₁.starProjection (F q)) = R a)
    (hfull₂ : ∀ q, Q₂.starProjection (F q) ∈ S₂ → ∃ a, v a (Q₂.starProjection (F q)) = R a)
    (hsel₀ : ∀ x ∈ S₀, Q₀.starProjection (F (sel₀ x)) = x)
    (hsel₁ : ∀ x ∈ S₁, Q₁.starProjection (F (sel₁ x)) = x)
    (hsel₂ : ∀ x ∈ S₂, Q₂.starProjection (F (sel₂ x)) = x) (hσ₀ : 0 < σ₀) (hσ₁ : 0 < σ₁)
    (hσ₂ : 0 < σ₂) (he₁ : e₁ ≤ 3 * σ₁ / 10) (he₂ : e₂ ≤ 3 * σ₂ / 10)
    (hloc₀ : ∀ q, ψ₀ (F q) ≠ 0 → Q₀.starProjection (F q) ∈ S₀)
    (hloc₁ : ∀ q, ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q)) ≠ 0 → Q₁.starProjection (F q) ∈ S₁)
    (hloc₂ : ∀ q, ψ₂ (adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q))) ≠ 0 →
      Q₂.starProjection (F q) ∈ S₂)
    (herr₁ : ∀ q, ‖adjustmentMap Q₀ P₀ ψ₀ (F q) - F q‖ ≤ e₁ * ρ q)
    (herr₂ : ∀ q, ‖adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q)) - F q‖ ≤ e₂ * ρ q)
    (hnear₀ : ∀ x ∈ S₀, ∀ z ∈ ball x (σ₀ * ρ (sel₀ x)), ∀ q,
      Q₀.starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (P₀ z) = 0)
    (hnear₁ : ∀ x ∈ S₁, ∀ z ∈ ball x (σ₁ * ρ (sel₁ x)), ∀ q,
      Q₁.starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (P₁ z) = 0)
    (hnear₂ : ∀ x ∈ S₂, ∀ z ∈ ball x (σ₂ * ρ (sel₂ x)), ∀ q,
      Q₂.starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (P₂ z) = 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ q, ‖adjustmentMap Q₂ P₂ ψ₂ (adjustmentMap Q₁ P₁ ψ₁
      (adjustmentMap Q₀ P₀ ψ₀ (F q))) - F q‖ ≤ E * ρ q) :
    (∀ q a, R a < ρ q / 16 → v a (adjustmentMap Q₀ P₀ ψ₀ (F q)) = 0) ∧
      (∀ q a, R a < ρ q / 16 →
        v a (adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q))) = 0) ∧
      (∀ q a, R a < ρ q / 16 → v a (adjustmentMap Q₂ P₂ ψ₂ (adjustmentMap Q₁ P₁ ψ₁
        (adjustmentMap Q₀ P₀ ψ₀ (F q)))) = 0) ∧
      ∀ a p, ζ a p = 0 → ∀ z ∈ segment ℝ (F p) (adjustmentMap Q₂ P₂ ψ₂
        (adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F p)))), |v a z| ≤ R a / 32 := by
  have he₀ : (0 : ℝ) ≤ 3 * σ₀ / 10 := by positivity
  have h := actualCloud_scalar_zero_marker_bound v hv R hR ρ ζ hζ0 F hvF hcomp 3
    (fun k => if k = 0 then Q₀ else if k = 1 then Q₁ else Q₂)
    (fun k => if k = 0 then P₀ else if k = 1 then P₁ else P₂)
    (fun k z => by
      by_cases hk : k = 0
      · simpa [hk] using hP₀ z
      · by_cases hk1 : k = 1
        · simpa [hk, hk1] using hP₁ z
        · simpa [hk, hk1] using hP₂ z)
    (fun k => if k = 0 then ψ₀ else if k = 1 then ψ₁ else ψ₂)
    (fun k q => if k = 0 then F q else if k = 1 then adjustmentMap Q₀ P₀ ψ₀ (F q) else
      if k = 2 then adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q)) else
      adjustmentMap Q₂ P₂ ψ₂ (adjustmentMap Q₁ P₁ ψ₁ (adjustmentMap Q₀ P₀ ψ₀ (F q))))
    (fun q => by simp)
    (fun k hk q => by
      interval_cases k <;> simp)
    (fun k hk => by
      interval_cases k
      · simpa using hret₀
      · simpa using hret₁
      · simpa using hret₂)
    (fun k => if k = 0 then S₀ else if k = 1 then S₁ else S₂)
    (fun k => if k = 0 then sel₀ else if k = 1 then sel₁ else sel₂)
    (fun k => if k = 0 then σ₀ else if k = 1 then σ₁ else σ₂)
    (fun k => if k = 0 then 0 else if k = 1 then e₁ else e₂)
    (fun k hk => by
      interval_cases k
      · simpa using hsup₀
      · simpa using hsup₁
      · simpa using hsup₂)
    (fun k hk q hq => by
      interval_cases k
      · simp only [ite_true] at hq ⊢
        exact hfull₀ q (hloc₀ q hq)
      · simp only [one_ne_zero, ite_false, ite_true] at hq ⊢
        exact hfull₁ q (hloc₁ q hq)
      · simp only [two_ne_zero, OfNat.ofNat_ne_one, ite_false, ite_true] at hq ⊢
        exact hfull₂ q (hloc₂ q hq))
    (fun k hk => by
      interval_cases k
      · simpa using hsel₀
      · simpa using hsel₁
      · simpa using hsel₂)
    (fun k hk => by
      interval_cases k
      · simpa using hσ₀
      · simpa using hσ₁
      · simpa using hσ₂)
    (fun k hk => by
      interval_cases k
      · simpa using he₀
      · simpa using he₁
      · simpa using he₂)
    (fun k hk q hq => by
      interval_cases k
      · simp only [ite_true] at hq ⊢
        exact hloc₀ q hq
      · simp only [one_ne_zero, ite_false, ite_true] at hq ⊢
        exact hloc₁ q hq
      · simp only [two_ne_zero, OfNat.ofNat_ne_one, ite_false, ite_true] at hq ⊢
        exact hloc₂ q hq)
    (fun k hk q _ => by
      interval_cases k
      · simp
      · simpa using herr₁ q
      · simpa using herr₂ q)
    (fun k hk => by
      interval_cases k
      · simpa using hnear₀
      · simpa using hnear₁
      · simpa using hnear₂)
    hE hE512 (fun q => by simpa using hcum q)
  refine ⟨fun q a ha => by simpa using h.1 1 (by norm_num) q a ha,
    fun q a ha => by simpa using h.1 2 (by norm_num) q a ha,
    fun q a ha => by simpa using h.1 3 le_rfl q a ha, fun a p hζ z hz => ?_⟩
  exact h.2 a p hζ z (by simpa using hz)

end GC.MetricGeometry
