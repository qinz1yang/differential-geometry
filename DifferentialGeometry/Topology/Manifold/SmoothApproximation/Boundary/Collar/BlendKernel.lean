import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Euclidean kernel of the collar straightening (A3-c)

Near a boundary point, in a half-space chart `z = (y, v)` with "height" `τ z ≥ 0`, the collar
straightening replaces a `C¹` map `G` by the blend
`X_δ = m + ρ (τ / δ) • (G - m)` of a model `m` (a first-order model of `G` along `τ = 0`) and `G`,
with a cutoff `ρ` that is `1` on `[1, ∞)`. This file proves:

* `hasFDerivWithinAt_collarBlend`: the derivative of the blend;
* `collarBlend_close` (blend kernel): if on `{τ < δ}` the derivative of the model is close to
  `G' z₀` and the model is `o(δ)`-close to `G`, then the blend is `C¹`-close to `G` near `z₀`
  uniformly for small `δ` (the cutoff's derivative `ρ' / δ` is paid for by the `o(δ)`-closeness);
* `collarBlend_hyp_of_jet` (jet estimate, product charts `E₁ × E₂`): the hypothesis of the kernel
  for the model `m (y, v) = a y + B y v` whose data `a`, `B` approximate `G (·, 0)` and
  `∂_v G (·, 0)`, using only that `G` is `C¹` up to `v = 0` (mean value theorem along `v`);
* `injOn_of_hasFDerivWithinAt_close`, `injective_of_norm_sub_le`: a map whose derivative is close
  to an injective linear map on a convex set is injective there, with injective derivatives;
* `comp_collarBlend_close`: the estimate survives composition with a `C¹` map `Π` fixing `G`
  (the tubular projection onto the boundary of the target).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

section Blend

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The collar blend `m + ρ (τ z / δ) • (G - m)`. -/
def collarBlend (ρ : ℝ → ℝ) (τ : E →L[ℝ] ℝ) (δ : ℝ) (m G : E → F) (z : E) : F :=
  m z + ρ (τ z / δ) • (G z - m z)

/-- The derivative of the collar blend, given derivatives `m'`, `G'` of `m`, `G`. -/
def collarBlendDeriv (ρ : ℝ → ℝ) (τ : E →L[ℝ] ℝ) (δ : ℝ) (m G : E → F)
    (m' G' : E → E →L[ℝ] F) (z : E) : E →L[ℝ] F :=
  m' z + ρ (τ z / δ) • (G' z - m' z) + (deriv ρ (τ z / δ) / δ) • τ.smulRight (G z - m z)

theorem hasFDerivWithinAt_collarBlend {ρ : ℝ → ℝ} (hρ : Differentiable ℝ ρ) (τ : E →L[ℝ] ℝ)
    (δ : ℝ) {m G : E → F} {m' G' : E → E →L[ℝ] F} {S : Set E} {z : E}
    (hm : HasFDerivWithinAt m (m' z) S z) (hG : HasFDerivWithinAt G (G' z) S z) :
    HasFDerivWithinAt (collarBlend ρ τ δ m G) (collarBlendDeriv ρ τ δ m G m' G' z) S z := by
  have hτ : HasFDerivWithinAt (fun z => τ z / δ) (δ⁻¹ • τ) S z := by
    have h := (τ.hasFDerivWithinAt (s := S) (x := z)).const_smul δ⁻¹
    convert h using 1
    funext w
    simp [div_eq_inv_mul, smul_eq_mul]
  have hσ : HasFDerivWithinAt (fun z => ρ (τ z / δ)) (deriv ρ (τ z / δ) • (δ⁻¹ • τ)) S z :=
    (hρ (τ z / δ)).hasDerivAt.comp_hasFDerivWithinAt z hτ
  have h := hm.add (hσ.smul (hG.sub hm))
  refine h.congr_fderiv ?_
  ext v
  simp only [collarBlendDeriv, add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.smulRight_apply, Pi.sub_apply,
    smul_eq_mul]
  rw [div_eq_mul_inv]
  module

/-- **Blend kernel.** -/
theorem collarBlend_close {ρ : ℝ → ℝ} {Cρ : ℝ} (hρ' : ∀ t, |deriv ρ t| ≤ Cρ)
    (hρ1 : ∀ t, 1 ≤ t → ρ t = 1) (hρd1 : ∀ t, 1 ≤ t → deriv ρ t = 0)
    (hρ01 : ∀ t, ρ t ∈ Icc (0 : ℝ) 1) (τ : E →L[ℝ] ℝ) {S : Set E} {z₀ : E}
    {G : E → F} {G' : E → E →L[ℝ] F} (hG' : ContinuousWithinAt G' S z₀)
    {m : ℕ → E → F} {m' : ℕ → E → E →L[ℝ] F} {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hA : ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ z ∈ S ∩ ball z₀ r, τ z < δ j →
      ‖m' j z - G' z₀‖ ≤ ε ∧ ‖G z - m j z‖ ≤ ε * δ j) :
    ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ z ∈ S ∩ ball z₀ r,
      ‖collarBlendDeriv ρ τ (δ j) (m j) G (m' j) G' z - G' z₀‖ ≤ ε ∧
      ‖collarBlend ρ τ (δ j) (m j) G z - G z‖ ≤ ε * δ j := by
  intro ε hε
  have hCρ : 0 ≤ Cρ := (abs_nonneg _).trans (hρ' 0)
  set K : ℝ := 1 + Cρ * ‖τ‖ with hK
  have hKpos : 0 < K := by positivity
  set ε₁ : ℝ := ε / K with hε₁def
  have hε₁ : 0 < ε₁ := div_pos hε hKpos
  have hε₁le : ε₁ ≤ ε := div_le_self hε.le (by nlinarith [mul_nonneg hCρ (norm_nonneg τ)])
  obtain ⟨r₁, hr₁, hev⟩ := hA ε₁ hε₁
  obtain ⟨r₂, hr₂, hcont⟩ : ∃ r₂ > 0, ∀ z ∈ S ∩ ball z₀ r₂, ‖G' z - G' z₀‖ ≤ ε₁ := by
    have h := Metric.continuousWithinAt_iff.mp hG' ε₁ hε₁
    obtain ⟨r₂, hr₂, h⟩ := h
    exact ⟨r₂, hr₂, fun z hz => by simpa [dist_eq_norm] using (h hz.1 (mem_ball.mp hz.2)).le⟩
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  filter_upwards [hev] with j hj z hz
  have hz₁ : z ∈ S ∩ ball z₀ r₁ := ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  have hz₂ : z ∈ S ∩ ball z₀ r₂ := ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
  by_cases hτz : τ z < δ j
  · obtain ⟨hd, hv⟩ := hj z hz₁ hτz
    set s := ρ (τ z / δ j) with hs
    have hs01 := hρ01 (τ z / δ j)
    have hc : ‖deriv ρ (τ z / δ j) / δ j‖ ≤ Cρ / δ j := by
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hδ j)]
      exact div_le_div_of_nonneg_right (hρ' _) (hδ j).le
    have hgm : ‖G z - m j z‖ ≤ ε₁ * δ j := hv
    have hgm' : ‖G' z - G' z₀‖ ≤ ε₁ := hcont z hz₂
    constructor
    · have hrw : collarBlendDeriv ρ τ (δ j) (m j) G (m' j) G' z - G' z₀ =
          (1 - s) • (m' j z - G' z₀) + s • (G' z - G' z₀) +
            (deriv ρ (τ z / δ j) / δ j) • τ.smulRight (G z - m j z) := by
        simp only [collarBlendDeriv, ← hs]
        module
      rw [hrw]
      calc _ ≤ ‖(1 - s) • (m' j z - G' z₀)‖ + ‖s • (G' z - G' z₀)‖ +
            ‖(deriv ρ (τ z / δ j) / δ j) • τ.smulRight (G z - m j z)‖ := norm_add₃_le
        _ ≤ (1 - s) * ε₁ + s * ε₁ + Cρ / δ j * (‖τ‖ * (ε₁ * δ j)) := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs01.2])]
            exact mul_le_mul_of_nonneg_left hd (by linarith [hs01.2])
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs01.1]
            exact mul_le_mul_of_nonneg_left hgm' hs01.1
          · rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul hc (mul_le_mul_of_nonneg_left hgm (norm_nonneg _))
              (by positivity) (div_nonneg hCρ (hδ j).le)
        _ = ε₁ * K := by
          have hδne : δ j ≠ 0 := (hδ j).ne'
          rw [hK]
          field_simp
          ring
        _ = ε := by rw [hε₁def]; field_simp
    · have hrw : collarBlend ρ τ (δ j) (m j) G z - G z = (1 - s) • (m j z - G z) := by
        simp only [collarBlend, ← hs]
        module
      rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs01.2]), norm_sub_rev]
      calc (1 - s) * ‖G z - m j z‖ ≤ 1 * (ε₁ * δ j) :=
            mul_le_mul (by linarith [hs01.1]) hgm (norm_nonneg _) zero_le_one
        _ ≤ ε * δ j := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hε₁le (hδ j).le
  · rw [not_lt] at hτz
    have h1 : 1 ≤ τ z / δ j := (one_le_div (hδ j)).mpr hτz
    have hX : collarBlendDeriv ρ τ (δ j) (m j) G (m' j) G' z = G' z := by
      simp only [collarBlendDeriv, hρ1 _ h1, hρd1 _ h1, zero_div, zero_smul, add_zero, one_smul]
      abel
    have hXv : collarBlend ρ τ (δ j) (m j) G z = G z := by
      simp only [collarBlend, hρ1 _ h1, one_smul]
      abel
    refine ⟨?_, ?_⟩
    · rw [hX]; exact (hcont z hz₂).trans hε₁le
    · rw [hXv, sub_self, norm_zero]; exact mul_nonneg hε.le (hδ j).le

end Blend

section Jet

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of the jet model `(y, v) ↦ a y + B y v`. -/
def jetModelDeriv (a' : E₁ →L[ℝ] F) (B : E₂ →L[ℝ] F) (B' : E₁ →L[ℝ] (E₂ →L[ℝ] F)) (v : E₂) :
    (E₁ × E₂) →L[ℝ] F :=
  (a' + B'.flip v).comp (ContinuousLinearMap.fst ℝ E₁ E₂) +
    B.comp (ContinuousLinearMap.snd ℝ E₁ E₂)

theorem hasFDerivAt_jetModel {a : E₁ → F} {a' : E₁ →L[ℝ] F} {B : E₁ → E₂ →L[ℝ] F}
    {B' : E₁ →L[ℝ] (E₂ →L[ℝ] F)} {z : E₁ × E₂} (ha : HasFDerivAt a a' z.1)
    (hB : HasFDerivAt B B' z.1) :
    HasFDerivAt (fun w : E₁ × E₂ => a w.1 + B w.1 w.2) (jetModelDeriv a' (B z.1) B' z.2) z := by
  have h1 : HasFDerivAt (fun w : E₁ × E₂ => a w.1) (a'.comp (ContinuousLinearMap.fst ℝ E₁ E₂)) z :=
    ha.comp z hasFDerivAt_fst
  have h2 : HasFDerivAt (fun w : E₁ × E₂ => B w.1)
      (B'.comp (ContinuousLinearMap.fst ℝ E₁ E₂)) z := hB.comp z hasFDerivAt_fst
  have h3 := h2.clm_apply (hasFDerivAt_snd (p := z))
  refine (h1.add h3).congr_fderiv ?_
  ext <;> simp [jetModelDeriv, add_comm, add_left_comm]

theorem norm_comp_fst_add_comp_snd_sub_le (L : (E₁ × E₂) →L[ℝ] F) (P : E₁ →L[ℝ] F)
    (Q : E₂ →L[ℝ] F) :
    ‖P.comp (ContinuousLinearMap.fst ℝ E₁ E₂) + Q.comp (ContinuousLinearMap.snd ℝ E₁ E₂) - L‖ ≤
      ‖P - L.comp (ContinuousLinearMap.inl ℝ E₁ E₂)‖ +
        ‖Q - L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by
  have hL : L = (L.comp (ContinuousLinearMap.inl ℝ E₁ E₂)).comp (ContinuousLinearMap.fst ℝ E₁ E₂) +
      (L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)).comp (ContinuousLinearMap.snd ℝ E₁ E₂) := by
    ext <;> simp [← map_add]
  have hrw : P.comp (ContinuousLinearMap.fst ℝ E₁ E₂) + Q.comp (ContinuousLinearMap.snd ℝ E₁ E₂) - L
      = (P - L.comp (ContinuousLinearMap.inl ℝ E₁ E₂)).comp (ContinuousLinearMap.fst ℝ E₁ E₂) +
        (Q - L.comp (ContinuousLinearMap.inr ℝ E₁ E₂)).comp
          (ContinuousLinearMap.snd ℝ E₁ E₂) := by
    conv_lhs => rw [hL]
    simp only [ContinuousLinearMap.sub_comp]
    abel
  rw [hrw]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ E₁ E₂))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E₁ E₂))

/-- **Jet estimate.** For `G` that is `C¹` on `ball y₀ r₁ ×ˢ C₂` (`C₂` convex, `0 ∈ C₂`, the height
`τ` controlling the norm on `C₂`), and a model `a y + B y v` whose data converge to `G (·, 0)` (at
rate `o(δ)`) and to the derivative of `G` at `(y₀, 0)`, with `B` having bounded derivative, the
hypothesis of `collarBlend_close` holds. -/
theorem collarBlend_hyp_of_jet (τ : E₂ →L[ℝ] ℝ) {C₂ : Set E₂} (hC₂ : Convex ℝ C₂)
    (h0 : (0 : E₂) ∈ C₂) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : ∀ v ∈ C₂, ‖v‖ ≤ κ * τ v) {y₀ : E₁}
    {r₁ : ℝ}
    {G : E₁ × E₂ → F} {G' : E₁ × E₂ → (E₁ × E₂) →L[ℝ] F}
    (hG : ∀ z ∈ ball y₀ r₁ ×ˢ C₂, HasFDerivWithinAt G (G' z) (ball y₀ r₁ ×ˢ C₂) z)
    (hG' : ContinuousWithinAt G' (ball y₀ r₁ ×ˢ C₂) (y₀, 0))
    {a : ℕ → E₁ → F} {a' : ℕ → E₁ → E₁ →L[ℝ] F} {B : ℕ → E₁ → E₂ →L[ℝ] F}
    {B' : ℕ → E₁ → E₁ →L[ℝ] (E₂ →L[ℝ] F)} {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hδpos : ∀ j, 0 < δ j)
    (ha : ∀ ε > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r₁, ‖a j y - G (y, 0)‖ ≤ ε * δ j)
    (ha' : ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r,
      ‖a' j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inl ℝ E₁ E₂)‖ ≤ ε)
    (hB : ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r,
      ‖B j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)‖ ≤ ε)
    (hB' : ∃ C, ∃ r > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r, ‖B' j y‖ ≤ C) :
    ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ z ∈ (ball y₀ r₁ ×ˢ C₂) ∩ ball (y₀, 0) r, τ z.2 < δ j →
      ‖jetModelDeriv (a' j z.1) (B j z.1) (B' j z.1) z.2 - G' (y₀, 0)‖ ≤ ε ∧
      ‖G z - (a j z.1 + B j z.1 z.2)‖ ≤ ε * δ j := by
  intro ε hε
  obtain ⟨C, rC, hrC, hBC⟩ := hB'
  set K : ℝ := 3 + 2 * κ with hK
  have hKpos : 0 < K := by positivity
  set ε₁ : ℝ := ε / K with hε₁def
  have hε₁ : 0 < ε₁ := div_pos hε hKpos
  obtain ⟨ra, hra, hev_a'⟩ := ha' ε₁ hε₁
  obtain ⟨rb, hrb, hev_B⟩ := hB ε₁ hε₁
  obtain ⟨rG, hrG, hGc⟩ : ∃ rG > 0, ∀ w ∈ (ball y₀ r₁ ×ˢ C₂) ∩ ball (y₀, 0) rG,
      ‖G' w - G' (y₀, 0)‖ ≤ ε₁ := by
    obtain ⟨rG, hrG, h⟩ := Metric.continuousWithinAt_iff.mp hG' ε₁ hε₁
    exact ⟨rG, hrG, fun w hw => by simpa [dist_eq_norm] using (h hw.1 (mem_ball.mp hw.2)).le⟩
  have hδC : ∀ᶠ j in atTop, (C + 1) * κ * δ j ≤ ε₁ := by
    have h : Tendsto (fun j => (C + 1) * κ * δ j) atTop (𝓝 0) := by
      simpa using hδ.const_mul ((C + 1) * κ)
    exact (h.eventually (ge_mem_nhds hε₁)).mono fun j hj => hj
  refine ⟨min (min ra rb) (min rG rC), by positivity, ?_⟩
  filter_upwards [ha ε₁ hε₁, hev_a', hev_B, hBC, hδC] with j hja hja' hjB hjBC hjδ
  rintro ⟨y, v⟩ ⟨⟨hy, hv⟩, hzr⟩ hτ
  have hzr' : dist (y, v) (y₀, 0) < min (min ra rb) (min rG rC) := hzr
  rw [Prod.dist_eq] at hzr'
  have hyd : dist y y₀ < min (min ra rb) (min rG rC) := lt_of_le_of_lt (le_max_left _ _) hzr'
  have hvd : dist v 0 < min (min ra rb) (min rG rC) := lt_of_le_of_lt (le_max_right _ _) hzr'
  have hya : y ∈ ball y₀ ra := mem_ball.mpr (lt_of_lt_of_le hyd ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hyb : y ∈ ball y₀ rb := mem_ball.mpr (lt_of_lt_of_le hyd ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hyC : y ∈ ball y₀ rC := mem_ball.mpr (lt_of_lt_of_le hyd ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hvn : ‖v‖ ≤ κ * δ j := (hκ v hv).trans (mul_le_mul_of_nonneg_left hτ.le hκ0)
  have hδj := hδpos j
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (B' j y)) (hjBC y hyC)
  constructor
  · -- derivative
    have h1 := norm_comp_fst_add_comp_snd_sub_le (G' (y₀, 0)) (a' j y + (B' j y).flip v) (B j y)
    have h2 : ‖a' j y + (B' j y).flip v - (G' (y₀, 0)).comp (ContinuousLinearMap.inl ℝ E₁ E₂)‖ ≤
        ε₁ + C * (κ * δ j) := by
      rw [show a' j y + (B' j y).flip v - (G' (y₀, 0)).comp (ContinuousLinearMap.inl ℝ E₁ E₂) =
        (a' j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inl ℝ E₁ E₂)) + (B' j y).flip v by abel]
      refine (norm_add_le _ _).trans (add_le_add (hja' y hya) ?_)
      calc ‖(B' j y).flip v‖ ≤ ‖(B' j y).flip‖ * ‖v‖ := (B' j y).flip.le_opNorm v
        _ = ‖B' j y‖ * ‖v‖ := by rw [ContinuousLinearMap.opNorm_flip]
        _ ≤ C * (κ * δ j) := mul_le_mul (hjBC y hyC) hvn (norm_nonneg _) hC0
    have h3 := hjB y hyb
    unfold jetModelDeriv
    calc _ ≤ _ := h1
      _ ≤ (ε₁ + C * (κ * δ j)) + ε₁ := add_le_add h2 h3
      _ ≤ ε₁ + ε₁ + ε₁ := by nlinarith [mul_nonneg hκ0 hδj.le]
      _ ≤ ε := by
        rw [hε₁def]
        have : 3 * (ε / K) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hKpos]
          nlinarith
        linarith
  · -- value
    have hT : Convex ℝ ((ball y₀ r₁ ×ˢ C₂) ∩ ball (y₀, 0) (min (min ra rb) (min rG rC))) :=
      ((convex_ball y₀ r₁).prod hC₂).inter (convex_ball _ _)
    have hy0mem : (y, (0 : E₂)) ∈ (ball y₀ r₁ ×ˢ C₂) ∩ ball (y₀, 0) (min (min ra rb) (min rG rC)) := by
      refine ⟨⟨hy, h0⟩, ?_⟩
      rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hyd
    have hzmem : (y, v) ∈ (ball y₀ r₁ ×ˢ C₂) ∩ ball (y₀, 0) (min (min ra rb) (min rG rC)) :=
      ⟨⟨hy, hv⟩, hzr⟩
    have hmvt := hT.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := G) (f' := G') (φ := G' (y₀, 0)) (C := ε₁)
      (fun w hw => (hG w hw.1).mono inter_subset_left)
      (fun w hw => hGc w ⟨hw.1, ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hw.2⟩)
      hy0mem hzmem
    have hdiff : ((y, v) : E₁ × E₂) - (y, 0) = (0, v) := by ext <;> simp
    rw [hdiff] at hmvt
    have hnorm0v : ‖((0 : E₁), v)‖ = ‖v‖ := by simp [Prod.norm_def]
    rw [hnorm0v] at hmvt
    have hinr : G' (y₀, 0) ((0 : E₁), v) =
        ((G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)) v := rfl
    have hrw : G (y, v) - (a j y + B j y v) = (G (y, v) - G (y, 0) - G' (y₀, 0) (0, v)) -
        (a j y - G (y, 0)) - (B j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)) v := by
      rw [hinr, sub_apply]
      abel
    change ‖G (y, v) - (a j y + B j y v)‖ ≤ ε * δ j
    rw [hrw]
    have hBv : ‖(B j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)) v‖ ≤
        ε₁ * (κ * δ j) :=
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hjB y hyb) hvn (norm_nonneg _) hε₁.le))
    calc _ ≤ ‖G (y, v) - G (y, 0) - G' (y₀, 0) (0, v)‖ + ‖a j y - G (y, 0)‖ +
          ‖(B j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)) v‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ε₁ * (κ * δ j) + ε₁ * δ j + ε₁ * (κ * δ j) :=
          add_le_add (add_le_add (hmvt.trans (mul_le_mul_of_nonneg_left hvn hε₁.le))
            (hja y hy)) hBv
      _ = ε₁ * K * δ j - ε₁ * 2 * δ j := by rw [hK]; ring
      _ ≤ ε₁ * K * δ j := by nlinarith [mul_pos hε₁ hδj]
      _ = ε * δ j := by rw [hε₁def]; field_simp

end Jet

section Injective

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A linear map close to an injective (antilipschitz) linear map is injective. -/
theorem injective_of_norm_sub_le {L T : E →L[ℝ] F} {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖v‖ ≤ ‖L v‖) (hT : ‖T - L‖ ≤ c / 2) : Function.Injective T := by
  intro v w hvw
  have hT0 : T (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have h1 : ‖L (v - w)‖ ≤ c / 2 * ‖v - w‖ := by
    have : L (v - w) = -((T - L) (v - w)) := by simp [hT0]
    rw [this, norm_neg]
    exact ((T - L).le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have h2 := hL (v - w)
  have : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- A map whose derivative on a convex set stays within `c / 2` of an antilipschitz linear map
`L` (constant `c`) is injective there. -/
theorem injOn_of_hasFDerivWithinAt_close {s : Set E} (hs : Convex ℝ s) {f : E → F}
    {f' : E → E →L[ℝ] F} (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z) {L : E →L[ℝ] F}
    {c : ℝ} (hc : 0 < c) (hL : ∀ v, c * ‖v‖ ≤ ‖L v‖) (hclose : ∀ z ∈ s, ‖f' z - L‖ ≤ c / 2) :
    InjOn f s := by
  intro z₁ hz₁ z₂ hz₂ he
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf hclose hz₁ hz₂
  rw [he, sub_self, zero_sub, norm_neg] at h
  have h2 := hL (z₂ - z₁)
  have : ‖z₂ - z₁‖ = 0 := by nlinarith [norm_nonneg (z₂ - z₁)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

/-- Composition of a blend estimate with a `C¹` map `Π` (derivative `Π'` continuous at `G z₀`)
that fixes `G` to first order at `z₀`. -/
theorem comp_collarBlend_close {S : Set E} {z₀ : E} {G : E → F} (hGc : ContinuousWithinAt G S z₀)
    {L : E →L[ℝ] F} {X : ℕ → E → F} {X' : ℕ → E → E →L[ℝ] F} {δ : ℕ → ℝ}
    (hδ : ∀ᶠ j in atTop, δ j ≤ 1)
    (hX : ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ z ∈ S ∩ ball z₀ r,
      ‖X' j z - L‖ ≤ ε ∧ ‖X j z - G z‖ ≤ ε * δ j)
    {P' : F → F →L[ℝ] F} (hP' : ContinuousAt P' (G z₀)) (hPL : (P' (G z₀)).comp L = L) :
    ∀ ε > 0, ∃ r > 0, ∀ᶠ j in atTop, ∀ z ∈ S ∩ ball z₀ r,
      ‖(P' (X j z)).comp (X' j z) - L‖ ≤ ε := by
  intro ε hε
  set A : ℝ := ‖P' (G z₀)‖ + 1 with hA
  set Bd : ℝ := ‖L‖ + 1 with hBd
  have hApos : 0 < A := by positivity
  have hBpos : 0 < Bd := by positivity
  set η : ℝ := min 1 (ε / (2 * A)) with hη
  have hηpos : 0 < η := lt_min one_pos (div_pos hε (by positivity))
  set ζ : ℝ := min 1 (ε / (2 * Bd)) with hζ
  have hζpos : 0 < ζ := lt_min one_pos (div_pos hε (by positivity))
  -- continuity of P' at G z₀
  obtain ⟨ρ₁, hρ₁, hPc⟩ := Metric.continuousAt_iff.mp hP' ζ hζpos
  obtain ⟨ρ₂, hρ₂, hGcont⟩ := Metric.continuousWithinAt_iff.mp hGc (ρ₁ / 2) (half_pos hρ₁)
  obtain ⟨r, hr, hev⟩ := hX (min η (ρ₁ / 2)) (lt_min hηpos (half_pos hρ₁))
  refine ⟨min r ρ₂, lt_min hr hρ₂, ?_⟩
  filter_upwards [hev, hδ] with j hj hδj z hz
  have hzr : z ∈ S ∩ ball z₀ r := ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  obtain ⟨hd, hv⟩ := hj z hzr
  have hd' : ‖X' j z - L‖ ≤ η := hd.trans (min_le_left _ _)
  have hXG : dist (X j z) (G z₀) < ρ₁ := by
    have h1 : ‖X j z - G z‖ ≤ ρ₁ / 2 := by
      have hδ0 : 0 ≤ δ j := by
        by_contra hneg
        rw [not_le] at hneg
        have := (norm_nonneg _).trans hv
        nlinarith [lt_min hηpos (half_pos hρ₁)]
      calc _ ≤ min η (ρ₁ / 2) * δ j := hv
        _ ≤ (ρ₁ / 2) * 1 := mul_le_mul (min_le_right _ _) hδj hδ0 (half_pos hρ₁).le
        _ = ρ₁ / 2 := mul_one _
    have h2 : dist (G z) (G z₀) < ρ₁ / 2 :=
      hGcont hz.1 (lt_of_lt_of_le (mem_ball.mp hz.2) (min_le_right _ _))
    rw [dist_eq_norm] at h2 ⊢
    calc ‖X j z - G z₀‖ = ‖(X j z - G z) + (G z - G z₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖X j z - G z‖ + ‖G z - G z₀‖ := norm_add_le _ _
      _ < ρ₁ / 2 + ρ₁ / 2 := add_lt_add_of_le_of_lt h1 h2
      _ = ρ₁ := add_halves ρ₁
  have hPz : ‖P' (X j z) - P' (G z₀)‖ ≤ ζ := by
    rw [← dist_eq_norm]; exact (hPc hXG).le
  have hX'b : ‖X' j z‖ ≤ Bd := by
    calc ‖X' j z‖ = ‖(X' j z - L) + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖X' j z - L‖ + ‖L‖ := norm_add_le _ _
      _ ≤ 1 + ‖L‖ := add_le_add_left (hd'.trans (min_le_left _ _)) _
      _ = Bd := by rw [hBd]; ring
  have hrw : (P' (X j z)).comp (X' j z) - L =
      (P' (X j z) - P' (G z₀)).comp (X' j z) + (P' (G z₀)).comp (X' j z - L) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hPL]
    abel
  rw [hrw]
  calc _ ≤ ‖(P' (X j z) - P' (G z₀)).comp (X' j z)‖ + ‖(P' (G z₀)).comp (X' j z - L)‖ :=
        norm_add_le _ _
    _ ≤ ζ * Bd + A * η := add_le_add
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hPz hX'b (norm_nonneg _)
          hζpos.le))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (by rw [hA]; linarith) hd'
          (norm_nonneg _) hApos.le))
    _ ≤ ε / (2 * Bd) * Bd + A * (ε / (2 * A)) := add_le_add
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hBpos.le)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hApos.le)
    _ = ε := by field_simp; ring

end Injective

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
