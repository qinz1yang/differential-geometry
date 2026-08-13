import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Bundle.PartialMfderiv
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_log_of_pos
    {u : ℝ → M → ℝ}
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Real.log (u p.1 p.2)) := by
  intro p
  exact (Real.contDiffAt_log.2 (hpos p.1 p.2).ne').comp_contMDiffAt
    (x := p) (hu p)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_log_of_pos_slice
    {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hpos : ∀ x : M, 0 < f x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => Real.log (f x)) := by
  intro x
  exact (Real.contDiffAt_log.2 (hpos x).ne').comp_contMDiffAt
    (x := x) (hf x)

omit [I.Boundaryless] [T2Space M] in
theorem inner_gradientFun_log_self
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hpos : 0 < f x) :
    g.inner x
        (gradientFun (I := I) g (fun y => Real.log (f y)) x)
        (gradientFun (I := I) g (fun y => Real.log (f y)) x) =
      (f x ^ 2)⁻¹ *
        g.inner x
          (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x) := by
  rw [gradientFun_log (I := I) g hf hpos]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp

variable [SigmaCompactSpace M]

def cutoffDirichletEnergy
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) : ℝ :=
  ∫ x, g.inner x
      (gradFun (I := I) g cutoff.toFun x)
      (gradFun (I := I) g cutoff.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [I.Boundaryless] in
theorem cutoffDirichletEnergy_nonneg
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) :
    0 ≤ cutoffDirichletEnergy (I := I) (M := M) cutoff := by
  exact integral_nonneg fun x =>
    metric_inner_self_nonneg (I := I) (M := M) g x _

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem twice_cutoff_inner_grad_le
    (g : SmoothRiemannianMetric I M) (cutoff w : SmoothScalar g) (x : M) :
    2 * cutoff.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g w.toFun x) ≤
      (1 / 2 : ℝ) * cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g w.toFun x)
            (gradFun (I := I) g w.toFun x) +
        2 *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g cutoff.toFun x) := by
  have hnonneg := metric_inner_self_nonneg (I := I) (M := M) g x
    (cutoff.toFun x • gradFun (I := I) g w.toFun x -
      (2 : ℝ) • gradFun (I := I) g cutoff.toFun x)
  simp only [map_sub, ContinuousLinearMap.sub_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hnonneg
  rw [g.symm x
    (gradFun (I := I) g cutoff.toFun x)
    (gradFun (I := I) g w.toFun x)] at hnonneg
  rw [g.symm x
    (gradFun (I := I) g cutoff.toFun x)
    (gradFun (I := I) g w.toFun x)]
  nlinarith

omit [SigmaCompactSpace M] in
theorem log_supersolution
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x + source t x ≤
        deriv (fun s => u s x) t) :
      Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun s y => Real.log (u s y))
            (contMDiff_log_of_pos hu hpos) t).toContMDiffMap x +
        g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) +
        (u t x)⁻¹ * source t x ≤
      deriv (fun s => Real.log (u s x)) t := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let hlog := contMDiff_log_of_pos hu hpos
  let logut := smoothScalarSlice (I := I) g (fun s y => Real.log (u s y)) hlog t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => Real.log (u s x)) t =
        (u t x)⁻¹ * deriv (fun s => u s x) t := by
    exact ((Real.hasDerivAt_log (hpos t x).ne').comp t
      ((htime.differentiable (by norm_num)).differentiableAt.hasDerivAt)).deriv
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.toContMDiffMap).mdifferentiable x
  have hlap_raw := laplacian_log (I := I)
    (LeviCivita (I := I) g) g
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g logut.toContMDiffMap x =
        (u t x)⁻¹ * Δ_g (I := I) g ut.toContMDiffMap x -
          (u t x ^ 2)⁻¹ *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    unfold SmoothScalar.toContMDiffMap
    rw [← laplacian_levi_eq (I := I) g logut.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, logut, smoothScalarSlice_toFun] using hlap_raw
  have hloggrad := inner_gradientFun_log_self (I := I) g
    (ut.smooth.mdifferentiable (by simp) x) (hpos t x)
  have hloggrad' :
      g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
        (u t x ^ 2)⁻¹ *
          g.inner x
            (gradientFun (I := I) g ut.toFun x)
            (gradientFun (I := I) g ut.toFun x) := by
    simpa only [ut, smoothScalarSlice_toFun] using hloggrad
  have hcoeff : 0 ≤ (u t x)⁻¹ := inv_nonneg.mpr (hpos t x).le
  have hmul := mul_le_mul_of_nonneg_left hpde hcoeff
  rw [htime_deriv]
  change Δ_g (I := I) g logut.toContMDiffMap x +
      g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) +
      (u t x)⁻¹ * source t x ≤
    (u t x)⁻¹ * deriv (fun s => u s x) t
  rw [hlap, hloggrad']
  convert hmul using 1
  all_goals ring

variable [CompactSpace M]

theorem log_energy_differential_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ)
    (hpde : ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) ≤
      deriv
          (fun s => localizedIntegral (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => Real.log (u r x))
              (contMDiff_log_of_pos hu hpos) s)) t +
        2 * cutoffDirichletEnergy (I := I) (M := M) cutoff := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t
  let test : SmoothScalar g :=
    ⟨fun x => cutoff.toFun x ^ 2, cutoff.smooth.pow 2⟩
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hwgrad_cont : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g w.toFun x)
        (gradFun (I := I) g w.toFun x)) := by
    simpa only [grad_g_apply] using w.continuous_inner_grad w
  have hcutoffgrad_cont : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) := by
    simpa only [grad_g_apply] using cutoff.continuous_inner_grad cutoff
  have hcross_cont : Continuous (fun x : M =>
      cutoff.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g w.toFun x)) := by
    have hinner := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g cutoff.toContMDiffMap) (grad_g (I := I) g w.toContMDiffMap)
    exact cutoff.smooth.continuous.mul (by simpa only [grad_g_apply] using hinner.continuous)
  have hlap_cont : Continuous (fun x : M => Δ_g (I := I) g w.toContMDiffMap x) :=
    (Δ_g_contMDiff (I := I) g w.toContMDiffMap).continuous
  let F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => Real.log (u p.1 p.2), hlog⟩
  have htime_cont : Continuous (fun x : M =>
      deriv (fun s => Real.log (u s x)) t) := by
    have hpartial := DifferentialGeometry.contMDiff_partial_deriv_fst I F
    exact (hpartial.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have henergy_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g w.toFun x)
          (gradFun (I := I) g w.toFun x)) μ :=
    ((cutoff.smooth.continuous.pow 2).mul hwgrad_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcutoffgrad_int : Integrable (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) μ :=
    hcutoffgrad_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcross_int : Integrable (fun x : M =>
      cutoff.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g w.toFun x)) μ :=
    hcross_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlap_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x) μ :=
    ((cutoff.smooth.continuous.pow 2).mul hlap_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have htime_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 * deriv (fun s => Real.log (u s x)) t) μ :=
    ((cutoff.smooth.continuous.pow 2).mul htime_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpointwise : ∀ x : M,
      cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x +
          cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g w.toFun x)
              (gradFun (I := I) g w.toFun x) ≤
        cutoff.toFun x ^ 2 * deriv (fun s => Real.log (u s x)) t := by
    intro x
    have h := log_supersolution (I := I) (M := M) g u (fun _ _ => 0)
      hu hpos (t := t) (x := x) (by simpa using hpde x)
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (cutoff.toFun x))
    simp only [mul_zero, add_zero] at hmul
    change cutoff.toFun x ^ 2 *
        (Δ_g (I := I) g w.toContMDiffMap x +
          g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)) ≤
      cutoff.toFun x ^ 2 * deriv (fun s => Real.log (u s x)) t at hmul
    change cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x +
        cutoff.toFun x ^ 2 *
          g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x) ≤
      cutoff.toFun x ^ 2 * deriv (fun s => Real.log (u s x)) t
    convert hmul using 1
    all_goals ring
  have htime_le :
      (∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x ∂μ) +
          ∫ x, cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g w.toFun x)
              (gradFun (I := I) g w.toFun x) ∂μ ≤
        ∫ x, cutoff.toFun x ^ 2 * deriv (fun s => Real.log (u s x)) t ∂μ := by
    rw [← integral_add hlap_int henergy_int]
    exact integral_mono (hlap_int.add henergy_int) htime_int hpointwise
  have hgreen :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g test.smooth w.smooth (HasCompactSupport.of_compactSpace _)
  have htest_pointwise : ∀ x : M,
      g.inner x
          (gradientFun (I := I) g test.toFun x)
          (gradientFun (I := I) g w.toFun x) =
        2 * cutoff.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g w.toFun x) := by
    intro x
    dsimp only [test]
    rw [gradientFun_pow (I := I) g 1
      (cutoff.smooth.mdifferentiable (by simp) x)]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [gradient_eq_gradFun (I := I), gradient_eq_gradFun (I := I)]
    ring
  have hlap_identity :
      (∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x ∂μ) =
        -2 * ∫ x, cutoff.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g w.toFun x) ∂μ := by
    have hgreen' :
        2 * ∫ x, cutoff.toFun x *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g w.toFun x) ∂μ =
          -∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x ∂μ := by
      calc
        2 * ∫ x, cutoff.toFun x *
              g.inner x
                (gradFun (I := I) g cutoff.toFun x)
                (gradFun (I := I) g w.toFun x) ∂μ =
            ∫ x, 2 * (cutoff.toFun x *
              g.inner x
                (gradFun (I := I) g cutoff.toFun x)
                (gradFun (I := I) g w.toFun x)) ∂μ := by
              rw [integral_const_mul]
        _ = ∫ x, g.inner x
              (gradientFun (I := I) g test.toFun x)
              (gradientFun (I := I) g w.toFun x) ∂μ := by
              exact integral_congr_ae (ae_of_all μ fun x => by
                simpa only [mul_assoc] using (htest_pointwise x).symm)
        _ = -∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g w.toContMDiffMap x ∂μ := by
              simpa only [μ, test, smoothScalarSlice_toFun, grad_g_apply] using hgreen
    linarith
  have hcross :
      2 * ∫ x, cutoff.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g w.toFun x) ∂μ ≤
        (1 / 2 : ℝ) * ∫ x, cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g w.toFun x)
            (gradFun (I := I) g w.toFun x) ∂μ +
          2 * ∫ x, g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g cutoff.toFun x) ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    rw [← integral_add (henergy_int.const_mul (1 / 2))
      (hcutoffgrad_int.const_mul 2)]
    exact integral_mono (hcross_int.const_mul 2)
      ((henergy_int.const_mul (1 / 2)).add (hcutoffgrad_int.const_mul 2))
      (fun x => by
        simpa only [mul_assoc] using
          twice_cutoff_inner_grad_le (I := I) (M := M) g cutoff w x)
  have hmass := hasDerivAt_localizedIntegral
    (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog t
  have hresult : (1 / 2 : ℝ) *
        (∫ x, cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g w.toFun x)
            (gradFun (I := I) g w.toFun x) ∂μ) ≤
      deriv
          (fun s => localizedIntegral (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => Real.log (u r x)) hlog s)) t +
        2 * ∫ x, g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ∂μ := by
    rw [hmass.deriv]
    rw [hlap_identity] at htime_le
    linarith
  simpa only [localizedDirichletEnergy, cutoffDirichletEnergy, μ, w, hlog,
    smoothScalarSlice_toFun] using hresult

theorem log_energy_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a b : ℝ} (hab : a ≤ b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) * ∫ t in a..b,
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) ≤
      localizedIntegral (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) b) -
        localizedIntegral (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) a) +
        2 * (b - a) * cutoffDirichletEnergy (I := I) (M := M) cutoff := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun t =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let energy : ℝ → ℝ := fun t => -mass t
  let denergy : ℝ → ℝ := fun t => -deriv mass t
  let dissipation : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let source : ℝ → ℝ := fun _ =>
    2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hdenergy_cont : ContinuousOn denergy (Icc a b) := by
    exact (hmass_smooth.continuous_deriv (by simp)).neg.continuousOn
  have henergy_deriv : ∀ t ∈ Icc a b,
      HasDerivAt energy (denergy t) t := by
    intro t _
    exact ((hmass_smooth.differentiable (by simp) t).hasDerivAt.neg)
  have hdissipation_cont : ContinuousOn dissipation (Icc a b) := by
    have hcont := contDiff_localizedDirichletEnergy
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
    exact (continuous_const.mul hcont.continuous).continuousOn
  have hpointwise : ∀ t ∈ Icc a b,
      0 * energy t + 1 * denergy t + dissipation t ≤ source t := by
    intro t ht
    have hdiff := log_energy_differential_of_supersolution
      (I := I) (M := M) g cutoff u hu hpos t (hpde t ht)
    change (1 / 2 : ℝ) * localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
      deriv mass t + 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff at hdiff
    dsimp only [energy, denergy, dissipation, source]
    linarith
  have hresult := weight_mul_energy_inequality
    (weight := fun _ => 1) (dweight := fun _ => 0)
    (energy := energy) (denergy := denergy)
    (dissipation := dissipation) (source := source) hab
    continuousOn_const (fun t _ => hasDerivAt_const t 1)
    hdenergy_cont henergy_deriv hdissipation_cont continuousOn_const hpointwise
  have hscaled :
      (∫ t in a..b, dissipation t) =
        (1 / 2 : ℝ) * ∫ t in a..b,
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) := by
    simp only [dissipation, intervalIntegral.integral_const_mul]
  have hsource :
      (∫ t in a..b, source t) =
        2 * (b - a) * cutoffDirichletEnergy (I := I) (M := M) cutoff := by
    simp only [source, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hscaled, hsource] at hresult
  dsimp only [energy] at hresult
  have hfinal :
      (1 / 2 : ℝ) * ∫ t in a..b,
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
        mass b - mass a +
          2 * (b - a) * cutoffDirichletEnergy (I := I) (M := M) cutoff := by
    linarith
  simpa only [hlog, mass] using hfinal

end DifferentialGeometry.Analysis.Parabolic.Moser

end
