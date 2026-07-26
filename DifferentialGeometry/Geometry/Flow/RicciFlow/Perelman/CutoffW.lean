import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CutoffEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.WEstimate
import DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Normalized Perelman cutoffs

This file converts a nonzero smooth cutoff into a unit-`L²` amplitude while
keeping its support and recording the exact rescaling of its Dirichlet energy.
-/

noncomputable section

open MeasureTheory Set Bundle Manifold Function
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Flow
namespace RicciFlow
namespace Perelman

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Integration
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A nonzero smooth scalar can be normalized to unit `L²` mass without
changing its support. Its Dirichlet energy is divided by the original squared
`L²` norm. -/
theorem normalize_cutoff
    (g : SmoothRiemannianMetric I M) {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hφpos : 0 < eLpNorm φ 2 (riemannianVolumeMeasure I M g))
    (hgrad : MemLp (fun x : M => Real.sqrt (g.inner x
      (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))) 2
        (riemannianVolumeMeasure I M g)) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      support v ⊆ support φ ∧
      (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 ∧
      Integrable (fun x => g.inner x (gradFun (I := I) g v x)
        (gradFun (I := I) g v x)) (riemannianVolumeMeasure I M g) ∧
      (∫ x, g.inner x (gradFun (I := I) g v x)
          (gradFun (I := I) g v x)
          ∂(riemannianVolumeMeasure I M g)) =
        (eLpNorm (fun x : M => Real.sqrt (g.inner x
          (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))) 2
            (riemannianVolumeMeasure I M g)).toReal ^ 2 /
          (eLpNorm φ 2 (riemannianVolumeMeasure I M g)).toReal ^ 2 := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let N : ℝ := (eLpNorm φ 2 μ).toReal
  let c : ℝ := N⁻¹
  let v : M → ℝ := c • φ
  have hφmem : MemLp φ 2 μ :=
    hφ.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNpos : 0 < N := by
    exact ENNReal.toReal_pos hφpos.ne' hφmem.eLpNorm_ne_top
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hvsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ v := by
    simpa only [v, Pi.smul_apply] using contMDiff_const.smul hφ
  refine ⟨v, hvsmooth, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply Function.mem_support.mpr
    intro hφx
    apply Function.mem_support.mp hx
    simp only [v, Pi.smul_apply, smul_eq_mul, hφx, mul_zero]
  · have hφsq := integral_sq_eq_l2 hφmem
    calc
      (∫ x, v x ^ 2 ∂μ) = ∫ x, c ^ 2 * φ x ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [v, Pi.smul_apply, smul_eq_mul]
        ring
      _ = c ^ 2 * ∫ x, φ x ^ 2 ∂μ := by
        rw [integral_const_mul]
      _ = 1 := by
        rw [hφsq]
        dsimp only [c, N]
        rw [inv_pow]
        exact inv_mul_cancel₀ (pow_ne_zero 2 hNne)
  · let gp : M → ℝ := fun x => Real.sqrt (g.inner x
      (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))
    have hgp_sq : ∀ x : M, gp x ^ 2 =
        g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g φ x) := by
      intro x
      dsimp only [gp]
      rw [sq, Real.mul_self_sqrt]
      by_cases hzero : gradFun (I := I) g φ x = 0
      · rw [hzero, map_zero]
      · exact (g.pos x _ hzero).le
    have hgrad_v : ∀ x : M, gradFun (I := I) g v x =
        c • gradFun (I := I) g φ x := by
      intro x
      exact gradFun_const_smul (I := I) g c
        (hφ.mdifferentiableAt (by norm_num))
    have henergy : ∀ x : M,
        g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x) =
          c ^ 2 * gp x ^ 2 := by
      intro x
      rw [hgrad_v x, (g.inner x).map_smul, ContinuousLinearMap.smul_apply,
        (g.inner x (gradFun (I := I) g φ x)).map_smul, smul_eq_mul,
        smul_eq_mul, hgp_sq x]
      ring
    have hgp_int := integral_sq_eq_l2 hgrad
    have henergy_int : Integrable (fun x =>
        g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x)) μ :=
      (hgrad.integrable_sq.const_mul (c ^ 2)).congr
        (Filter.Eventually.of_forall fun x => (henergy x).symm)
    exact henergy_int
  · let gp : M → ℝ := fun x => Real.sqrt (g.inner x
      (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))
    have hgp_sq : ∀ x : M, gp x ^ 2 =
        g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g φ x) := by
      intro x
      dsimp only [gp]
      rw [sq, Real.mul_self_sqrt]
      by_cases hzero : gradFun (I := I) g φ x = 0
      · rw [hzero, map_zero]
      · exact (g.pos x _ hzero).le
    have hgrad_v : ∀ x : M, gradFun (I := I) g v x =
        c • gradFun (I := I) g φ x := by
      intro x
      exact gradFun_const_smul (I := I) g c
        (hφ.mdifferentiableAt (by norm_num))
    have henergy : ∀ x : M,
        g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x) =
          c ^ 2 * gp x ^ 2 := by
      intro x
      rw [hgrad_v x, (g.inner x).map_smul, ContinuousLinearMap.smul_apply,
        (g.inner x (gradFun (I := I) g φ x)).map_smul, smul_eq_mul,
        smul_eq_mul, hgp_sq x]
      ring
    have hgp_int := integral_sq_eq_l2 hgrad
    calc
      (∫ x, g.inner x (gradFun (I := I) g v x)
          (gradFun (I := I) g v x) ∂μ) = ∫ x, c ^ 2 * gp x ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact henergy x
      _ = c ^ 2 * ∫ x, gp x ^ 2 ∂μ := by
        rw [integral_const_mul]
      _ = (eLpNorm gp 2 μ).toReal ^ 2 /
          (eLpNorm φ 2 μ).toReal ^ 2 := by
        rw [hgp_int]
        dsimp only [c, N]
        rw [div_eq_mul_inv, inv_pow]
        ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A metric ball admits a smooth unit-`L²` amplitude supported in that ball.
Its Dirichlet energy is bounded by the squared ratio of the outer gradient
scale to the half-ball mass scale. -/
theorem exists_cutoff_wdata
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (a : M)
    {r : ℝ} (hr : 0 < r) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      support v ⊆
        {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r} ∧
      (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 ∧
      Integrable (fun x => g.inner x (gradFun (I := I) g v x)
        (gradFun (I := I) g v x)) (riemannianVolumeMeasure I M g) ∧
      (∫ x, g.inner x (gradFun (I := I) g v x)
          (gradFun (I := I) g v x)
          ∂(riemannianVolumeMeasure I M g)) ≤
        ((ENNReal.ofReal (5 / r) *
            (riemannianVolumeMeasure I M g
              {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}) ^
                (1 / 2 : ℝ)).toReal /
          (((riemannianVolumeMeasure I M g
              {x | riemannianEDistOf (I := I) g a x <
                ENNReal.ofReal (r / 2)}) ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let A : Set M :=
    {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal (r / 2)}
  let U : Set M :=
    {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}
  have hAopen : IsOpen A := by
    dsimp only [A]
    exact isOpen_lt
      (by
        unfold riemannianEDistOf
        exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g a)
      continuous_const
  have hAne : A.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [A, mem_setOf_eq, riemannianEDistOf,
      Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  letI : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hμA : 0 < μ A := hAopen.measure_pos μ hAne
  let massScale : ENNReal := (μ A) ^ (1 / 2 : ℝ) / 2
  let gradScale : ENNReal :=
    ENNReal.ofReal (5 / r) * (μ U) ^ (1 / 2 : ℝ)
  have hmass_pos : 0 < massScale := by
    have hrpow_pos : 0 < (μ A) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_pos_of_nonneg hμA (by norm_num)
    exact ENNReal.div_pos hrpow_pos.ne' (by norm_num)
  have hmass_top : massScale ≠ (⊤ : ENNReal) := by
    exact ENNReal.div_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ A))
      (by norm_num)
  have hgrad_top : gradScale ≠ (⊤ : ENNReal) := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ U))
  obtain ⟨φ, hφ, hφsupp, hφlower, hφgrad⟩ :=
    exists_cutoff_energy (I := I) (M := M) g a hr
  have hφpos : 0 < eLpNorm φ 2 μ := by
    exact hmass_pos.trans_le hφlower
  let gp : M → ℝ := fun x => Real.sqrt (g.inner x
    (gradFun (I := I) g φ x) (gradFun (I := I) g φ x))
  have hφdiff : ∀ᵐ x ∂μ, MDifferentiableAt I 𝓘(ℝ, ℝ) φ x :=
    Filter.Eventually.of_forall fun x => hφ.mdifferentiableAt (by norm_num)
  have hgpmem : MemLp gp 2 μ := by
    refine ⟨grad_norm_aesm (I := I) g hφdiff, ?_⟩
    exact hφgrad.trans_lt (lt_top_iff_ne_top.mpr hgrad_top)
  obtain ⟨v, hv, hvsupp, hvmass, hvgradi, hvenergy⟩ :=
    normalize_cutoff (I := I) (M := M) g hφ hφpos hgpmem
  have hφmem : MemLp φ 2 μ :=
    hφ.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨v, hv, ?_, hvmass, hvgradi, ?_⟩
  · intro x hx
    exact hφsupp (subset_tsupport φ (hvsupp hx))
  · have hgrad_real : (eLpNorm gp 2 μ).toReal ≤ gradScale.toReal :=
      ENNReal.toReal_mono hgrad_top hφgrad
    have hmass_real : massScale.toReal ≤ (eLpNorm φ 2 μ).toReal :=
      ENNReal.toReal_mono hφmem.eLpNorm_ne_top hφlower
    have hmass_real_pos : 0 < massScale.toReal :=
      ENNReal.toReal_pos hmass_pos.ne' hmass_top
    have hφnorm_pos : 0 < (eLpNorm φ 2 μ).toReal :=
      ENNReal.toReal_pos hφpos.ne' (by
        exact hφmem.eLpNorm_ne_top)
    have hratio :
        (eLpNorm gp 2 μ).toReal / (eLpNorm φ 2 μ).toReal ≤
          gradScale.toReal / massScale.toReal := by
      calc
        (eLpNorm gp 2 μ).toReal / (eLpNorm φ 2 μ).toReal ≤
            gradScale.toReal / (eLpNorm φ 2 μ).toReal :=
          div_le_div_of_nonneg_right hgrad_real hφnorm_pos.le
        _ ≤ gradScale.toReal / massScale.toReal :=
          div_le_div_of_nonneg_left ENNReal.toReal_nonneg
            hmass_real_pos hmass_real
    calc
      (∫ x, g.inner x (gradFun (I := I) g v x)
          (gradFun (I := I) g v x) ∂μ) =
          ((eLpNorm gp 2 μ).toReal / (eLpNorm φ 2 μ).toReal) ^ 2 := by
        rw [hvenergy, div_pow]
      _ ≤ (gradScale.toReal / massScale.toReal) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ENNReal.toReal_nonneg hφnorm_pos.le) hratio 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The normalized ball cutoff satisfies the scalar square-form upper bound
obtained from its support volume, Dirichlet energy, and a scalar-curvature
upper bound on the ball. -/
theorem exists_cutoff_wform
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (a : M)
    {r : ℝ} (hr : 0 < r) {R : M → ℝ} (hRcont : Continuous R)
    {tau K C : ℝ} (htau : 0 ≤ tau)
    (hR : ∀ x, riemannianEDistOf (I := I) g a x < ENNReal.ofReal r → R x ≤ K) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      support v ⊆
        {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r} ∧
      (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 ∧
      Integrable (fun x => g.inner x (gradFun (I := I) g v x)
        (gradFun (I := I) g v x)) (riemannianVolumeMeasure I M g) ∧
      (∫ x, 4 * tau *
            g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x) +
          tau * R x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2
          ∂(riemannianVolumeMeasure I M g)) ≤
        4 * tau *
            ((ENNReal.ofReal (5 / r) *
                (riemannianVolumeMeasure I M g
                  {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}) ^
                    (1 / 2 : ℝ)).toReal /
              (((riemannianVolumeMeasure I M g
                  {x | riemannianEDistOf (I := I) g a x <
                    ENNReal.ofReal (r / 2)}) ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
          tau * K +
          Real.log (riemannianVolumeMeasure I M g
            {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}).toReal + C := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let U : Set M :=
    {x | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}
  let energyBound : ℝ :=
    ((ENNReal.ofReal (5 / r) * (μ U) ^ (1 / 2 : ℝ)).toReal /
      (((μ {x | riemannianEDistOf (I := I) g a x <
        ENNReal.ofReal (r / 2)}) ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  obtain ⟨v, hv, hvsupp, hvmass, hvgradi, hvenergy⟩ :=
    exists_cutoff_wdata (I := I) (M := M) g a hr
  have hv2i : Integrable (fun x => v x ^ 2) μ :=
    (hv.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have henti : Integrable (fun x => v x ^ 2 * Real.log (v x ^ 2)) μ :=
    (Real.continuous_mul_log.comp (hv.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRi : Integrable (fun x => R x * v x ^ 2) μ :=
    (hRcont.mul (hv.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨v, hv, hvsupp, hvmass, hvgradi, ?_⟩
  exact DifferentialGeometry.PDE.RicciFlow.Entropy.w_form_upper
    (U := U) (v := v) (R := R)
    (gradSq := fun x => g.inner x (gradFun (I := I) g v x)
      (gradFun (I := I) g v x))
    (tau := tau) (K := K) (G := energyBound) (C := C) μ
    hv.continuous.measurable hv2i hvmass henti hvsupp hvgradi hvenergy hRi
    (fun x hx => hR x hx) htau

end Perelman
end RicciFlow
end Flow
end Geometry
end DifferentialGeometry
