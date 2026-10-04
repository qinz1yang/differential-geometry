import DifferentialGeometry.Analysis.Integration.Convolution.IteratedDerivative
import DifferentialGeometry.Analysis.Integration.Convolution.Bilinear
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter ContinuousLinearMap Set
open scoped ContDiff Convolution Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_smooth_bilinear_approx_on_compact_with_background
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (k : ℕ)
    (hB : ContDiffOn ℝ (k : ℕ∞ω) B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (lower upper : ℝ)
    (hbound : ∀ x ∈ U, ∀ v,
      lower * ‖v‖ ^ 2 ≤ B x v v ∧ B x v v ≤ upper * ‖v‖ ^ 2)
    (B₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm₀ : ∀ v w, B₀ v w = B₀ w v)
    (hbound₀ : ∀ v, lower * ‖v‖ ^ 2 ≤ B₀ v v ∧ B₀ v v ≤ upper * ‖v‖ ^ 2) :
    ∃ g : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n x v w, g n x v w = g n x w v) ∧
      (∀ n x v, lower * ‖v‖ ^ 2 ≤ g n x v v ∧
        g n x v v ≤ upper * ‖v‖ ^ 2) ∧
      ∀ j, j ≤ k → TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ j (g n)) (iteratedFDeriv ℝ j B) atTop K := by
  borelize E
  obtain ⟨χ, hχ, hχc, hχone, hχU, hχrange⟩ := exists_bump_compact hK hU hKU
  let b : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => χ x • (B x - B₀)
  let Bext : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => B₀ + b x
  have hb : ContDiff ℝ (k : ℕ∞ω) b := by
    apply contDiffOn_univ.mp
    exact contDiffOn_cutoff_smul hU
      (hχ.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))) hχU
      (by simpa only [univ_inter] using hB.sub contDiffOn_const)
  have hbc : HasCompactSupport b := hχc.smul_right
  have hBext : ContDiff ℝ (k : ℕ∞ω) Bext := contDiff_const.add hb
  have heq : Bext =ᶠ[𝓝ˢ K] B := by
    filter_upwards [hχone] with x hx
    simp only [Bext, b, hx, Pi.one_apply, one_smul, add_sub_cancel]
  have hBextsymm : ∀ x v w, Bext x v w = Bext x w v := by
    intro x v w
    by_cases hx : x ∈ tsupport χ
    · simp only [Bext, b, add_apply, smul_apply,
        sub_apply, smul_eq_mul, hsymm x (hχU hx) v w, hsymm₀ v w]
    · simp only [Bext, b, image_eq_zero_of_notMem_tsupport hx, zero_smul, add_zero,
        hsymm₀ v w]
  have hBextbound : ∀ x v, lower * ‖v‖ ^ 2 ≤ Bext x v v ∧
      Bext x v v ≤ upper * ‖v‖ ^ 2 := by
    intro x v
    by_cases hx : x ∈ tsupport χ
    · have h0 : 0 ≤ χ x := (hχrange (mem_range_self x)).1
      have h1 : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχrange (mem_range_self x)).2
      have hlow := mul_le_mul_of_nonneg_left (hbound x (hχU hx) v).1 h0
      have hupp := mul_le_mul_of_nonneg_left (hbound x (hχU hx) v).2 h0
      have hlow₀ := mul_le_mul_of_nonneg_left (hbound₀ v).1 h1
      have hupp₀ := mul_le_mul_of_nonneg_left (hbound₀ v).2 h1
      simp only [Bext, b, add_apply, smul_apply,
        sub_apply, smul_eq_mul]
      constructor <;> nlinarith
    · simpa only [Bext, b, image_eq_zero_of_notMem_tsupport hx, zero_smul, add_zero]
        using hbound₀ v
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let ν : Measure E := Measure.addHaar
  let q (n : ℕ) := (φ n).normed ν ⋆[lsmul ℝ ℝ, ν] b
  let g (n : ℕ) (x : E) := B₀ + q n x
  have hq (n : ℕ) : ContDiff ℝ ∞ (q n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hb.continuous.locallyIntegrable
  have hg (n : ℕ) : ContDiff ℝ ∞ (g n) := contDiff_const.add (hq n)
  have hrepr (n : ℕ) : (φ n).normed ν ⋆[lsmul ℝ ℝ, ν] Bext = g n := by
    funext x
    have hc := ((φ n).hasCompactSupport_normed (μ := ν)).convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (φ n).integrable_normed.locallyIntegrable
      (continuous_const : Continuous (fun _ : E => B₀)) x
    have hcb := ((φ n).hasCompactSupport_normed (μ := ν)).convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (φ n).integrable_normed.locallyIntegrable hb.continuous x
    change ((φ n).normed ν ⋆[lsmul ℝ ℝ, ν] ((fun _ : E => B₀) + b)) x = _
    rw [hc.distrib_add hcb]
    have hconst : ((φ n).normed ν ⋆[lsmul ℝ ℝ, ν] (fun _ : E => B₀)) x = B₀ :=
      (φ n).normed_convolution_eq_right (fun _ _ => rfl)
    rw [hconst]
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro n x v w
    rw [← hrepr n]
    exact (φ n).normed_convolution_bilinear_symmetric hBext.continuous.locallyIntegrable hBextsymm x v w
  · intro n x v
    rw [← hrepr n]
    exact (φ n).normed_convolution_bilinear_quadratic_bounds
      hBext.continuous.locallyIntegrable lower upper hBextbound x v
  · intro j hj
    have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv := ContDiffBump.tendstoUniformly_iteratedFDeriv_normed_convolution
      (μ := ν) hφ hbc k hb j hj
    have hgconv : TendstoUniformly (fun n => iteratedFDeriv ℝ j (g n))
        (iteratedFDeriv ℝ j Bext) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro ε hε
      filter_upwards [Metric.tendstoUniformly_iff.mp hconv ε hε] with n hn
      intro x
      have hqj : ContDiff ℝ (j : ℕ∞ω) (q n) :=
        (hq n).of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
      have hbj : ContDiff ℝ (j : ℕ∞ω) b := hb.of_le (by exact_mod_cast hj)
      change dist (iteratedFDeriv ℝ j ((fun _ : E => B₀) + b) x)
        (iteratedFDeriv ℝ j ((fun _ : E => B₀) + q n) x) < ε
      rw [iteratedFDeriv_add contDiff_const hbj, iteratedFDeriv_add contDiff_const hqj]
      simpa only [Pi.add_apply, dist_add_left] using hn x
    apply hgconv.tendstoUniformlyOn.congr_right
    intro x hx
    exact ((heq.filter_mono (nhds_le_nhdsSet hx)).iteratedFDeriv ℝ j).self_of_nhds

theorem exists_smooth_bilinear_approx_on_compact
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {B : V → V →L[ℝ] V →L[ℝ] ℝ} (k : ℕ)
    (hB : ContDiffOn ℝ (k : ℕ∞ω) B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (lower upper : ℝ) (hlu : lower ≤ upper)
    (hbound : ∀ x ∈ U, ∀ v,
      lower * ‖v‖ ^ 2 ≤ B x v v ∧ B x v v ≤ upper * ‖v‖ ^ 2) :
    ∃ g : ℕ → V → V →L[ℝ] V →L[ℝ] ℝ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n x v w, g n x v w = g n x w v) ∧
      (∀ n x v, lower * ‖v‖ ^ 2 ≤ g n x v v ∧
        g n x v v ≤ upper * ‖v‖ ^ 2) ∧
      ∀ j, j ≤ k → TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ j (g n)) (iteratedFDeriv ℝ j B) atTop K := by
  apply exists_smooth_bilinear_approx_on_compact_with_background hK hU hKU k hB hsymm
    lower upper hbound (lower • innerSL ℝ)
  · intro v w
    change lower * inner ℝ v w = lower * inner ℝ w v
    rw [real_inner_comm v w]
  · intro v
    change lower * ‖v‖ ^ 2 ≤ lower * inner ℝ v v ∧
      lower * inner ℝ v v ≤ upper * ‖v‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
    exact ⟨le_rfl, mul_le_mul_of_nonneg_right hlu (sq_nonneg _)⟩

end DifferentialGeometry.Analysis
