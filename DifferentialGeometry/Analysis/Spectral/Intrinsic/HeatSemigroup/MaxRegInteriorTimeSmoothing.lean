import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup

/-!
# All-order interior-time smoothing of the per-mode Duhamel coordinates

For a closed Riemannian manifold `(M, g₀)` and ranks `(0, 2)`, the inhomogeneous
heat equation `∂_t u = Δ_∇ u + f`, `u(0) = 0`, has the `L²`-maximal-regularity
solution whose `i`-th eigen-coordinate is the per-mode Duhamel convolution
`φᵢ(t) = perModeConv λᵢ (f i) t = ∫₀ᵗ e^{−λᵢ(t−s)} (f i)(s) ds`.

The companion file `SpectralMassUniformSup.lean` controls the order-`0` time
value of the spectral mass uniformly on `[0,T]`.  This file strengthens the
control to **all time-derivatives**: for every time-derivative order `k` and
every spatial Sobolev order `σ ≥ 0`, the weighted square of the `k`-th
time-derivative `∂ₜᵏφᵢ` has a single, `t`-independent, summable-across-modes
majorant on `[0,T]`.

## The reasoning route (the parabolic time-bootstrap)

The eigen-coordinate solves the scalar ODE `φᵢ' = (f i) − λᵢ·φᵢ`, `φᵢ(0) = 0`
(`perModeConv_hasDerivAt`).  Differentiating `k` times gives the **one-step time
recursion**

  `∂ₜᵏ⁺¹φᵢ = ∂ₜᵏ(f i) − λᵢ·∂ₜᵏφᵢ`

(`perModeConv_iteratedDeriv_succ`, the iterated form of the ODE, valid for a
`C∞` forcing coordinate).  Each time-derivative therefore costs **one extra
power of `λᵢ`** — equivalently *two* extra spatial Sobolev orders after squaring.
The weighted square then bootstraps:

  `(1 + λᵢ)^σ (∂ₜᵏ⁺¹φᵢ)² ≤ 2·(1 + λᵢ)^σ (∂ₜᵏ(f i))² + 2·(1 + λᵢ)^{σ+2}(∂ₜᵏφᵢ)²`,

the first term controlled by the *forcing* mass at order `(k, σ)` and the second
by the order-`(k, σ+2)` instance of the very same statement — an induction on `k`
that raises the spatial order by `2` per step.  The base case `k = 0` is the
endpoint Cauchy–Schwarz bound `perModeConv_endpoint_sq_le` against the forcing's
own order-`σ` mass.

Because each step is dominated by a `t`-independent, summable majorant supplied
by the forcing hypothesis `hforcing_mass`, the conclusion is a single
summable-across-modes constant `Cmaj`, uniform over `t ∈ [0,T]`.

## Chart-independence

The forcing enters this file *only* through a genuine `C∞`-in-time
coordinate family `f : TensorEigenIdx … → ℝ → ℝ` (a smooth representative of the
per-mode forcing coordinate) together with its own all-order spectral-mass
control `hforcing_mass`.  The file is therefore independent of the chart-jet
coefficient tower: the smoothness and summability of that representative are
*hypotheses*, to be discharged by the parabolic interior smoothing of the
genuine engine forcing where this lemma is consumed.

## Sign convention

Geometer convention `Δ_∇ = −∇*∇`, eigenvalues `λᵢ ≥ 0`, weights
`(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {T : ℝ}

/-- **The one-step time recursion for the per-mode Duhamel convolution.**  For a
`C∞` forcing term `f`, the `(k+1)`-th time-derivative of the per-mode
convolution `perModeConv lam f` is, as a function,

  `∂ₜᵏ⁺¹(perModeConv lam f) = ∂ₜᵏf − lam·∂ₜᵏ(perModeConv lam f)`.

This is the iterated form of the defining ODE `φ' = f − lam·φ`
(`perModeConv_hasDerivAt`): one differentiates the ODE `k` times, using that the
time derivative of `perModeConv lam f` is `f − lam·perModeConv lam f`, and that
both `f` and `perModeConv lam f` are `C∞` (`perModeConv_contDiff_of_contDiff`), so
the `iteratedDeriv` of the difference splits termwise. -/
private theorem perModeConv_iteratedDeriv_succ (lam : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv (k + 1) (perModeConv lam f)
      = fun t => iteratedDeriv k f t - lam * iteratedDeriv k (perModeConv lam f) t := by
  have hfcont : Continuous f := hf.continuous
  have hphi_smooth : ContDiff ℝ ∞ (perModeConv lam f) :=
    perModeConv_contDiff_of_contDiff ⊤ lam f hf
  have hderiv_eq : deriv (perModeConv lam f)
      = fun t => f t - lam * perModeConv lam f t :=
    deriv_eq (fun t => perModeConv_hasDerivAt lam hfcont t)
  rw [iteratedDeriv_succ', hderiv_eq]
  funext t
  have hcd_f : ContDiffAt ℝ (k : WithTop ℕ∞) f t :=
    (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd_phi : ContDiffAt ℝ (k : WithTop ℕ∞) (perModeConv lam f) t :=
    (hphi_smooth.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd_lp : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun t => lam * perModeConv lam f t) t :=
    hcd_phi.const_smul lam
  have hsub :
      iteratedDeriv k (fun t => f t - lam * perModeConv lam f t) t
        = iteratedDeriv k f t
          - iteratedDeriv k (fun t => lam * perModeConv lam f t) t := by
    have hshow :
        (fun t => f t - lam * perModeConv lam f t)
          = f - fun t => lam * perModeConv lam f t := by
      funext u; simp
    rw [hshow, iteratedDeriv_sub hcd_f hcd_lp]
  rw [hsub]
  have hconst :
      iteratedDeriv k (fun t => lam * perModeConv lam f t) t
        = lam * iteratedDeriv k (perModeConv lam f) t := by
    have hsmul := iteratedDeriv_const_smul (𝕜 := ℝ) (F := ℝ) (R := ℝ)
      (n := k) (f := perModeConv lam f) hcd_phi lam
    simp only [smul_eq_mul] at hsmul
    exact hsmul
  rw [hconst]

/-- The pointwise endpoint bound on the per-mode convolution against the
forcing's pointwise square, uniform on `[0,T]`: for a continuous `f`, `0 ≤ lam`,
`0 ≤ T` and `t ∈ [0,T]`,

  `(perModeConv lam f t)² ≤ T · ∫₀ᵀ f(s)² ds`.

The endpoint Cauchy–Schwarz bound `perModeConv_endpoint_sq_le` dominates the
square by the kernel mass times `∫₀ᵗ f²`; the kernel mass is `≤ t ≤ T` and the
forcing square integral over `[0,t]` is `≤` the one over `[0,T]`. -/
private theorem perModeConv_sq_le_T_mul_integral (lam : ℝ) (hlam : 0 ≤ lam)
    (f : ℝ → ℝ) (hf : Continuous f) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (perModeConv lam f t) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, f s ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hkernel : (perModeConv lam f t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
    perModeConv_endpoint_sq_le lam hf ht0
  have hmass_le : duhamelKernelSqIntegral lam t ≤ T :=
    le_trans (duhamelKernelSqIntegral_le_t hlam ht0) htT
  have hmass_nn : 0 ≤ duhamelKernelSqIntegral lam t :=
    duhamelKernelSqIntegral_nonneg ht0
  have hintegral_t_nn : 0 ≤ ∫ s in (0 : ℝ)..t, f s ^ 2 :=
    intervalIntegral.integral_nonneg ht0 (fun s _ => sq_nonneg _)
  have hintegral_le : (∫ s in (0 : ℝ)..t, f s ^ 2) ≤ ∫ s in (0 : ℝ)..T, f s ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := t) (c := T)
        (((hf.pow 2)).intervalIntegrable 0 t)
        (((hf.pow 2)).intervalIntegrable t T)]
    have htail : 0 ≤ ∫ s in t..T, f s ^ 2 :=
      intervalIntegral.integral_nonneg htT (fun s _ => sq_nonneg _)
    linarith
  calc (perModeConv lam f t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2 := hkernel
    _ ≤ T * ∫ s in (0 : ℝ)..T, f s ^ 2 := by
        apply mul_le_mul hmass_le hintegral_le hintegral_t_nn hT

/-- **The all-order pointwise spectral-mass control of the per-mode Duhamel
coordinates.**  Let `f i : ℝ → ℝ` be a `C∞`-in-time forcing-coordinate family
(`hf_smooth`) whose own all-order weighted pointwise spectral masses are
summable across the spectrum, uniformly on `[0,T]` (`hforcing_mass`: for every
time-order `j` and spatial order `τ ≥ 0`, the family
`i ↦ (1 + λᵢ)^τ (∂ₜʲ(f i) t)²` has a `t`-independent summable majorant on
`[0,T]`).

Then for every time-derivative order `k` and spatial Sobolev order `σ ≥ 0`, the
per-mode Duhamel coordinates `φᵢ = perModeConv λᵢ (f i)` satisfy the analogous
control: there is a single summable-across-modes majorant `Cmaj`, independent of
`t`, with

  `(1 + λᵢ)^σ · (∂ₜᵏφᵢ t)² ≤ Cmaj i`   for all `i` and all `t ∈ [0,T]`.

This is the parabolic interior-time smoothing of the maximal-regularity
solution at the level of its eigen-coordinates: every time-derivative is
spatially controlled, summably across modes, uniformly up to `t = 0` on `[0,T]`.
The proof is the induction on `k` described in the module header, raising the
spatial order by `2` per time-derivative. -/
theorem perModeConv_allOrder_timeDeriv_spectralMass_le (hT : 0 ≤ T)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hforcing_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i) :
    ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i)) t) ^ 2
            ≤ Cmaj i := by
  intro k
  induction k with
  | zero =>
      intro σ hσ
      obtain ⟨B, hB_sum, hB_le⟩ := hforcing_mass 0 σ hσ
      refine ⟨fun i => T * (T * B i), (hB_sum.mul_left T).mul_left T, ?_⟩
      intro i t ht
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      have hcont : Continuous (f i) := (hf_smooth i).continuous
      have hbound : (perModeConv lam (f i) t) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, f i s ^ 2 :=
        perModeConv_sq_le_T_mul_integral lam hlam_nn (f i) hcont hT ht
      have hintegral_le :
          tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2
            ≤ T * B i := by
        have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2 ≤ B i := by
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        have hpoint_uIcc : ∀ s ∈ Set.uIcc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2 ≤ B i := by
          intro s hs
          rw [Set.uIcc_of_le hT] at hs
          exact hpoint s hs
        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2)
            volume 0 T :=
          ((hcont.pow 2).const_mul _).intervalIntegrable 0 T
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) volume 0 T :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..T,
              tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2
            ≤ ∫ _s in (0 : ℝ)..T, B i := by
          refine intervalIntegral.integral_mono_on hT hi_lhs hi_const ?_
          intro s hs
          exact hpoint s hs
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
        calc tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2
            ≤ (T - 0) * B i := hmono
          _ = T * B i := by ring
      calc tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv 0 (perModeConv lam (f i)) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ * (perModeConv lam (f i) t) ^ 2 := by
            rw [iteratedDeriv_zero]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ * (T * ∫ s in (0 : ℝ)..T, f i s ^ 2) :=
            mul_le_mul_of_nonneg_left hbound hwt_nn
        _ = T * (tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2) := by
            ring
        _ ≤ T * (T * B i) := by
            apply mul_le_mul_of_nonneg_left hintegral_le hT
  | succ k ih =>
      intro σ hσ
      obtain ⟨Bf, hBf_sum, hBf_le⟩ := hforcing_mass k σ hσ
      obtain ⟨Cprev, hCprev_sum, hCprev_le⟩ := ih (σ + 2) (by linarith)
      refine ⟨fun i => 2 * Bf i + 2 * Cprev i,
        (hBf_sum.mul_left 2).add (hCprev_sum.mul_left 2), ?_⟩
      intro i t ht
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      have hwtσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      have hrec := perModeConv_iteratedDeriv_succ lam (f i) (hf_smooth i) k
      have hval : iteratedDeriv (k + 1) (perModeConv lam (f i)) t
          = iteratedDeriv k (f i) t - lam * iteratedDeriv k (perModeConv lam (f i)) t := by
        rw [hrec]
      have hexpand_sq :
          (iteratedDeriv (k + 1) (perModeConv lam (f i)) t) ^ 2
            ≤ 2 * (iteratedDeriv k (f i) t) ^ 2
              + 2 * (lam * iteratedDeriv k (perModeConv lam (f i)) t) ^ 2 := by
        rw [hval]
        nlinarith [sq_nonneg (iteratedDeriv k (f i) t
            + lam * iteratedDeriv k (perModeConv lam (f i)) t),
          sq_nonneg (iteratedDeriv k (f i) t
            - lam * iteratedDeriv k (perModeConv lam (f i)) t)]
      have hforce_term :
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (f i) t) ^ 2 ≤ Bf i :=
        hBf_le i t ht
      have hphi_term :
          tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv k (perModeConv lam (f i)) t) ^ 2 ≤ Cprev i :=
        hCprev_le i t ht
      have hweight_step :
          tensorSobolevWeight (I := I) (M := M) i σ * lam ^ 2
            ≤ tensorSobolevWeight (I := I) (M := M) i (σ + 2) := by
        have h1le : (1 : ℝ) ≤ 1 + lam := by linarith
        have hlamsq_le : lam ^ 2 ≤ (1 + lam) ^ 2 := by nlinarith [hlam_nn]
        have hwtσ_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
          tensorSobolevWeight_pos (I := I) (M := M) i σ
        have hsplit : tensorSobolevWeight (I := I) (M := M) i (σ + 2)
            = tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam) ^ 2 := by
          unfold tensorSobolevWeight
          rw [hlam_def] at *
          rw [Real.rpow_add (by linarith)]
          congr 1
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hlamsq_le hwtσ_nn
      have hlam_sq_term :
          tensorSobolevWeight (I := I) (M := M) i σ *
              (lam * iteratedDeriv k (perModeConv lam (f i)) t) ^ 2
            ≤ Cprev i := by
        have heq : (lam * iteratedDeriv k (perModeConv lam (f i)) t) ^ 2
            = lam ^ 2 * (iteratedDeriv k (perModeConv lam (f i)) t) ^ 2 := by ring
        calc tensorSobolevWeight (I := I) (M := M) i σ *
              (lam * iteratedDeriv k (perModeConv lam (f i)) t) ^ 2
            = (tensorSobolevWeight (I := I) (M := M) i σ * lam ^ 2) *
                (iteratedDeriv k (perModeConv lam (f i)) t) ^ 2 := by
              rw [heq]; ring
          _ ≤ tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
                (iteratedDeriv k (perModeConv lam (f i)) t) ^ 2 := by
              apply mul_le_mul_of_nonneg_right hweight_step (sq_nonneg _)
          _ ≤ Cprev i := hphi_term
      calc tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv (k + 1) (perModeConv lam (f i)) t) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (2 * (iteratedDeriv k (f i) t) ^ 2
                + 2 * (lam * iteratedDeriv k (perModeConv lam (f i)) t) ^ 2) :=
            mul_le_mul_of_nonneg_left hexpand_sq hwtσ_nn
        _ = 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv k (f i) t) ^ 2)
              + 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (lam * iteratedDeriv k (perModeConv lam (f i)) t) ^ 2) := by ring
        _ ≤ 2 * Bf i + 2 * Cprev i := by
            have h1 := mul_le_mul_of_nonneg_left hforce_term (by norm_num : (0 : ℝ) ≤ 2)
            have h2 := mul_le_mul_of_nonneg_left hlam_sq_term (by norm_num : (0 : ℝ) ≤ 2)
            linarith

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
