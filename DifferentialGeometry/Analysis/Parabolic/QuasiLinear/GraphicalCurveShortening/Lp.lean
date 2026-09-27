import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Coefficients
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α}

private theorem graph_remainder_lipschitz :
    LipschitzWith 1 (fun p : E => graphDiffusionCoefficient p - 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
    (graphDiffusionCoefficient_lipschitz (E := E)).dist_le_mul p q

def graphDiffusionRemainderLp (p : Lp E ∞ μ) : Lp ℝ ∞ μ :=
  graph_remainder_lipschitz.compLp (by simp [graphDiffusionCoefficient]) p

theorem graphDiffusionRemainderLp_ae (p : Lp E ∞ μ) :
    graphDiffusionRemainderLp p =ᵐ[μ] fun x => graphDiffusionCoefficient (p x) - 1 :=
  graph_remainder_lipschitz.coeFn_compLp _ p

private theorem lp_top_ae_norm_le (p : Lp E ∞ μ) :
    ∀ᵐ x ∂μ, ‖p x‖ ≤ ‖p‖ := by
  simpa only [← toReal_eLpNorm p.1.aestronglyMeasurable, Lp.norm_def] using
    ae_le_lpNorm_exponent_top (Lp.memLp p)

private theorem lp_top_norm_le_of_ae_bound {c : Lp ℝ ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖c x‖ ≤ C) : ‖c‖ ≤ C := by
  rw [Lp.norm_def]
  apply (ENNReal.toReal_le_of_le_ofReal hC)
  exact eLpNormEssSup_le_of_ae_bound h

theorem graphDiffusionRemainderLp_norm_le (p : Lp E ∞ μ) :
    ‖graphDiffusionRemainderLp p‖ ≤ ‖p‖ ^ 2 := by
  apply lp_top_norm_le_of_ae_bound (sq_nonneg _)
  filter_upwards [graphDiffusionRemainderLp_ae p, lp_top_ae_norm_le p] with x hx hp
  rw [hx, Real.norm_eq_abs]
  apply (graphDiffusionCoefficient_sub_one_bound (p x)).trans
  nlinarith only [hp, norm_nonneg (p x), norm_nonneg p]

theorem graphDiffusionRemainderLp_sub_norm_le (p q : Lp E ∞ μ) :
    ‖graphDiffusionRemainderLp p - graphDiffusionRemainderLp q‖ ≤
      (‖p‖ + ‖q‖) * ‖p - q‖ := by
  apply lp_top_norm_le_of_ae_bound (by positivity)
  filter_upwards [Lp.coeFn_sub (graphDiffusionRemainderLp p) (graphDiffusionRemainderLp q),
    graphDiffusionRemainderLp_ae p, graphDiffusionRemainderLp_ae q,
    lp_top_ae_norm_le p, lp_top_ae_norm_le q, lp_top_ae_norm_le (p - q),
    Lp.coeFn_sub p q] with x hx hpx hqx hp hq hpq hsub
  rw [hx]
  change ‖(graphDiffusionRemainderLp p) x - (graphDiffusionRemainderLp q) x‖ ≤ _
  rw [hpx, hqx, sub_sub_sub_cancel_right, Real.norm_eq_abs]
  apply graphDiffusionCoefficient_local_lipschitz.trans
  rw [hsub] at hpq
  exact mul_le_mul (add_le_add hp hq) hpq (norm_nonneg _) (by positivity)

variable {l : ℝ≥0∞} [Fact (1 ≤ l)]

def graphDiffusionRemainderAction (p : Lp E ∞ μ) (f : Lp F l μ) : Lp F l μ :=
  graphDiffusionRemainderLp p • f

omit [Fact (1 ≤ l)] in
theorem graphDiffusionRemainderAction_norm_le (p : Lp E ∞ μ) (f : Lp F l μ) :
    ‖graphDiffusionRemainderAction p f‖ ≤ ‖p‖ ^ 2 * ‖f‖ := by
  exact (Lp.norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_right (graphDiffusionRemainderLp_norm_le p) (by rw [Lp.norm_def]; exact ENNReal.toReal_nonneg))

omit [Fact (1 ≤ l)] in
theorem graphDiffusionRemainderAction_ae (p : Lp E ∞ μ) (f : Lp F l μ) :
    graphDiffusionRemainderAction p f =ᵐ[μ]
      fun x => (graphDiffusionCoefficient (p x) - 1) • f x := by
  filter_upwards [Lp.coeFn_lpSMul (r := l) (graphDiffusionRemainderLp p) f,
    graphDiffusionRemainderLp_ae p] with x hx hp
  change (graphDiffusionRemainderLp p • f : Lp F l μ) x = _
  rw [hx]
  change (graphDiffusionRemainderLp p) x • f x = _
  rw [hp]

theorem graphDiffusionRemainderAction_sub_norm_le
    (p q : Lp E ∞ μ) (f g : Lp F l μ) :
    ‖graphDiffusionRemainderAction p f - graphDiffusionRemainderAction q g‖ ≤
      ‖p‖ ^ 2 * ‖f - g‖ + (‖p‖ + ‖q‖) * ‖p - q‖ * ‖g‖ := by
  have heq : graphDiffusionRemainderAction p f - graphDiffusionRemainderAction q g =
      graphDiffusionRemainderLp p • (f - g) +
        (graphDiffusionRemainderLp p - graphDiffusionRemainderLp q) • g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (graphDiffusionRemainderAction p f)
        (graphDiffusionRemainderAction q g),
      graphDiffusionRemainderAction_ae p f, graphDiffusionRemainderAction_ae q g,
      Lp.coeFn_add (graphDiffusionRemainderLp p • (f - g))
        ((graphDiffusionRemainderLp p - graphDiffusionRemainderLp q) • g),
      Lp.coeFn_lpSMul (r := l) (graphDiffusionRemainderLp p) (f - g),
      Lp.coeFn_lpSMul (r := l) (graphDiffusionRemainderLp p - graphDiffusionRemainderLp q) g,
      Lp.coeFn_sub f g,
      Lp.coeFn_sub (graphDiffusionRemainderLp p) (graphDiffusionRemainderLp q),
      graphDiffusionRemainderLp_ae p, graphDiffusionRemainderLp_ae q]
      with x hx hpf hqg hadd hsmul hsmul' hfg hpq hp hq
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply'] at hx hadd hsmul hsmul' hfg hpq
    rw [hx, hpf, hqg, hadd, hsmul, hsmul', hfg, hpq, hp, hq]
    simp only [smul_sub, sub_smul]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (Lp.norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (graphDiffusionRemainderLp_norm_le p) (norm_nonneg _))
  · exact (Lp.norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (graphDiffusionRemainderLp_sub_norm_le p q) (norm_nonneg _))

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α}

theorem continuous_graphDiffusionRemainderLp :
    Continuous (graphDiffusionRemainderLp : Lp E ∞ μ → Lp ℝ ∞ μ) := by
  have hl : LipschitzWith 1 (fun p : E => graphDiffusionCoefficient p - 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
      (graphDiffusionCoefficient_lipschitz (E := E)).dist_le_mul p q
  exact hl.continuous_compLp (by simp [graphDiffusionCoefficient])

variable {l : ℝ≥0∞} [Fact (1 ≤ l)]

theorem continuous_graphDiffusionRemainderAction :
    Continuous (fun z : Lp E ∞ μ × Lp F l μ => graphDiffusionRemainderAction z.1 z.2) := by
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := F)).holderL μ ∞ l l
  have hB : Continuous (fun z : Lp E ∞ μ × Lp F l μ =>
      B (graphDiffusionRemainderLp z.1) z.2) :=
    Continuous.clm_apply
      (B.continuous.comp (continuous_graphDiffusionRemainderLp.comp continuous_fst))
      continuous_snd
  convert hB using 1
  funext z
  apply Lp.ext
  filter_upwards [graphDiffusionRemainderAction_ae z.1 z.2,
    (ContinuousLinearMap.lsmul ℝ ℝ (E := F)).coeFn_holder
      (r := l) (graphDiffusionRemainderLp z.1) z.2,
    graphDiffusionRemainderLp_ae z.1] with x hx hb hp
  exact hx.trans (by simpa only [B, ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.lsmul_apply, hp] using hb.symm)

end DifferentialGeometry.Analysis.Parabolic

open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eLpNorm_graphDiffusionCoefficient_derivative_sub_le
    {α : Type*} [MeasurableSpace α] {p q r s : α → E} {μ : Measure α}
    {R D : ℝ} {l : ℝ≥0∞} (hR : 0 ≤ R) (hD : 0 ≤ D) (hl : 1 ≤ l)
    (hpR : ∀ᵐ x ∂μ, ‖p x‖ ≤ R) (hqR : ∀ᵐ x ∂μ, ‖q x‖ ≤ R)
    (hpq : ∀ᵐ x ∂μ, ‖p x - q x‖ ≤ D)
    (hr : AEStronglyMeasurable r μ) (hs : AEStronglyMeasurable s μ) :
    eLpNorm (fun x => (-2 * graphDiffusionCoefficient (p x) ^ 2 * ⟪p x, r x⟫_ℝ) -
        (-2 * graphDiffusionCoefficient (q x) ^ 2 * ⟪q x, s x⟫_ℝ)) l μ ≤
      ENNReal.ofReal (2 * R) * eLpNorm (fun x => r x - s x) l μ +
        ENNReal.ofReal ((2 + 8 * R ^ 2) * D) * eLpNorm s l μ := by
  let f : α → ℝ := fun x => ‖r x - s x‖
  let g : α → ℝ := fun x => ‖s x‖
  let A := 2 * R
  let B := (2 + 8 * R ^ 2) * D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf : AEStronglyMeasurable f μ := (hr.sub hs).norm
  have hg : AEStronglyMeasurable g μ := hs.norm
  have hpoint : ∀ᵐ x ∂μ,
      ‖(-2 * graphDiffusionCoefficient (p x) ^ 2 * ⟪p x, r x⟫_ℝ) -
        (-2 * graphDiffusionCoefficient (q x) ^ 2 * ⟪q x, s x⟫_ℝ)‖ ≤
        ((A • f + B • g) x) := by
    filter_upwards [hpR, hqR, hpq] with x hpxR hqxR hpqx
    have hb := graphDiffusionCoefficient_deriv_sub_bound_of_norm_le hpxR hqxR (r x) (s x)
    have hr := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpxR (by norm_num : (0:ℝ) ≤ 2))
      (norm_nonneg (r x - s x))
    rw [Real.norm_eq_abs]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpqx (by positivity : 0 ≤ 2 + 8 * R ^ 2))
      (norm_nonneg (s x))
    change _ ≤ A * f x + B * g x
    dsimp [A, B, f, g]
    nlinarith only [hb, hmul, hr]
  calc
    _ ≤ eLpNorm (A • f + B • g) l μ := eLpNorm_mono_ae_real hpoint
    _ ≤ eLpNorm (A • f) l μ + eLpNorm (B • g) l μ :=
      eLpNorm_add_le (hf.const_smul A) (hg.const_smul B) hl
    _ = _ := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul,
        Real.enorm_eq_ofReal hA, Real.enorm_eq_ofReal hB]
      simp only [f, g, eLpNorm_norm, A, B]

theorem eLpNorm_deriv_graphDiffusionCoefficient_sub_le
    {p q : ℝ → E} {μ : Measure ℝ} {R D : ℝ} {l : ℝ≥0∞}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hl : 1 ≤ l)
    (hp : ∀ᵐ x ∂μ, DifferentiableAt ℝ p x)
    (hq : ∀ᵐ x ∂μ, DifferentiableAt ℝ q x)
    (hpR : ∀ᵐ x ∂μ, ‖p x‖ ≤ R) (hqR : ∀ᵐ x ∂μ, ‖q x‖ ≤ R)
    (hpq : ∀ᵐ x ∂μ, ‖p x - q x‖ ≤ D)
    (hp'm : AEStronglyMeasurable (deriv p) μ)
    (hq'm : AEStronglyMeasurable (deriv q) μ) :
    eLpNorm (deriv (fun x => graphDiffusionCoefficient (p x) -
        graphDiffusionCoefficient (q x))) l μ ≤
      ENNReal.ofReal (2 * R) * eLpNorm (fun x => deriv p x - deriv q x) l μ +
        ENNReal.ofReal ((2 + 8 * R ^ 2) * D) * eLpNorm (deriv q) l μ := by
  have heq : deriv (fun x => graphDiffusionCoefficient (p x) - graphDiffusionCoefficient (q x)) =ᵐ[μ]
      fun x => (-2 * graphDiffusionCoefficient (p x) ^ 2 * ⟪p x, deriv p x⟫_ℝ) -
        (-2 * graphDiffusionCoefficient (q x) ^ 2 * ⟪q x, deriv q x⟫_ℝ) := by
    filter_upwards [hp, hq] with x hpx hqx
    exact ((hasDerivAt_graphDiffusionCoefficient hpx.hasDerivAt).sub
      (hasDerivAt_graphDiffusionCoefficient hqx.hasDerivAt)).deriv
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_graphDiffusionCoefficient_derivative_sub_le hR hD hl hpR hqR hpq hp'm hq'm

end DifferentialGeometry.Analysis.Parabolic

end
