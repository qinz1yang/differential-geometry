import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.SpectralSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator

/-!
# Parabolic smoothing of the Duhamel (inhomogeneous-heat) integral into every `Hˢ`

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the
inhomogeneous heat equation `∂_t u = Δ_∇ u + F`, `u(0) = 0`, has the
Duhamel solution

  `u(t) = ∫₀ᵗ e^{(t−s)Δ_∇} F(s) ds`.

After the spatial spectral decomposition this decouples mode by mode: on
the eigen-coordinate belonging to the connection-Laplacian eigenvalue
`λᵢ ≥ 0` the heat operator acts as multiplication by `e^{−λᵢ(t−s)}`, so the
`i`-th coordinate of `u(t)` is the scalar **per-mode Duhamel convolution**

  `φᵢ(t) = ∫₀ᵗ e^{−λᵢ(t−s)} Fᵢ(s) ds`   (`perModeConv λᵢ Fᵢ t`).

This file proves the **pointwise-in-time parabolic-regularity gain** at the
level of these per-mode coordinates and assembles it into the statement
that, for `t > 0`, the Duhamel value `u(t)` lands in the spectral Sobolev
space `Hˢ` for every `σ` provided the forcing is spatially smooth (lands in
`H^c` for every order `c`, with the same underlying `L²([0,T])` time
coordinates).  This is the Duhamel half of the analytic-semigroup
parabolic smoothing that, together with the homogeneous half
`heat_semigroup_into_all_tensorHs` (companion file), gives the spatial
`C^∞` of a strong solution.

## The per-mode kernel estimate (the heart)

The genuine smoothing is the **one-derivative pointwise gain**.  By the
endpoint Cauchy–Schwarz inequality,

  `(φᵢ(t))² ≤ (∫₀ᵗ e^{−2λᵢ(t−s)} ds) · ∫₀ᵗ Fᵢ(s)² ds`,

and the kernel `L²`-mass `mass(λᵢ) = ∫₀ᵗ e^{−2λᵢ(t−s)} ds = (1 −
e^{−2λᵢt})/(2λᵢ)` satisfies the **uniform-in-`λ`** spectral bound

  `(1 + λᵢ) · mass(λᵢ) ≤ t + 1/2`.

(For small `λ` the mass `→ t`; for large `λ` the `λ⁻¹` decay of the mass is
exactly compensated by the `(1 + λ)` weight, leaving the constant `1/2`.)
Hence `(1 + λᵢ) · (φᵢ(t))² ≤ (t + 1/2) · ‖Fᵢ‖²_{L²}` — one Sobolev order is
gained, uniformly across the spectrum, at every fixed `t > 0`.

Iterating the order: if the forcing is in `H^c` for *every* `c`, the
gained order `c + 1` is again attained for every `c`, so the Duhamel value
lies in `⋂_σ Hˢ`.

## Main results

* `duhamelKernelSqIntegral` — the kernel `L²`-mass `∫₀ᵗ e^{−2λ(t−s)} ds`.
* `one_add_lambda_mul_duhamel_kernel_sq_integral_le` — the uniform-in-`λ`
  spectral kernel bound `(1 + λ)·mass(λ) ≤ t + 1/2`.
* `perModeConv_endpoint_sq_le` — the endpoint Cauchy–Schwarz bound
  `(φ(t))² ≤ mass(λ)·∫₀ᵗ f²`.
* `one_add_lambda_mul_perModeConv_endpoint_sq_le` — the **per-mode
  one-derivative-gain estimate** `(1 + λ)·(φ(t))² ≤ (t + 1/2)·∫₀ᵗ f²`.

## Sign convention

Geometer convention `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; resolvent
`(1 − Δ_∇)⁻¹`, eigenvalues `λᵢ ≥ 0`, heat factor `e^{−λᵢ(t−s)} ∈ (0,1]`,
weight `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

section Scalar

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

/-- The kernel `L²`-mass `∫₀ᵗ e^{−2·lam·(t−s)} ds`, as a stand-alone real
number.  Equals `(1 − e^{−2·lam·t})/(2·lam)` for `lam ≠ 0` and `t` for
`lam = 0`; the uniform packaging used below is the weighted bound
`one_add_lambda_mul_duhamel_kernel_sq_integral_le`. -/
def duhamelKernelSqIntegral (lam t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-(2 * lam * (t - s)))

/-- **The telescoped kernel-mass identity.**  For every `lam` and `t`,

  `(2·lam) · ∫₀ᵗ e^{−2·lam·(t−s)} ds = 1 − e^{−2·lam·t}`,

the `s`-primitive of `s ↦ e^{−2·lam·(t−s)}` being itself.  This is
`kernelIntegral_space` of the scalar maximal-regularity core, specialised to
decay rate `2·lam`. -/
theorem two_lambda_mul_duhamelKernelSqIntegral (lam t : ℝ) :
    (2 * lam) * duhamelKernelSqIntegral lam t = 1 - Real.exp (-(2 * lam * t)) := by
  unfold duhamelKernelSqIntegral
  rw [← intervalIntegral.integral_const_mul]
  exact kernelIntegral_space (2 * lam) t

/-- The kernel `L²`-mass is nonnegative for `0 ≤ t`. -/
theorem duhamelKernelSqIntegral_nonneg {lam t : ℝ} (ht : 0 ≤ t) :
    0 ≤ duhamelKernelSqIntegral lam t := by
  unfold duhamelKernelSqIntegral
  exact intervalIntegral.integral_nonneg ht (fun s _ => (Real.exp_pos _).le)

/-- The kernel `L²`-mass is at most `t` (the integrand is `≤ 1`), for
`0 ≤ lam` and `0 ≤ t`. -/
theorem duhamelKernelSqIntegral_le_t {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    duhamelKernelSqIntegral lam t ≤ t := by
  unfold duhamelKernelSqIntegral
  calc ∫ s in (0 : ℝ)..t, Real.exp (-(2 * lam * (t - s)))
      ≤ ∫ _s in (0 : ℝ)..t, (1 : ℝ) := by
        refine intervalIntegral.integral_mono_on ht
          (Continuous.intervalIntegrable (by fun_prop) 0 t)
          intervalIntegral.intervalIntegrable_const (fun s hs => ?_)
        refine Real.exp_le_one_iff.mpr ?_
        have : 0 ≤ 2 * lam * (t - s) := by nlinarith [hs.1, hs.2]
        linarith
    _ = t := by simp

/-- **The uniform-in-`λ` spectral kernel bound.**  For `0 ≤ lam` and
`0 ≤ t`,

  `(1 + lam) · ∫₀ᵗ e^{−2·lam·(t−s)} ds ≤ t + 1/2`.

This is the spectral heart of the Duhamel one-derivative gain: the `λ⁻¹`
decay of the kernel mass for large `λ` exactly cancels the `(1 + λ)` weight
(leaving the constant `1/2`), while for `λ → 0` the mass tends to `t`.

Proof.  Write `mass = duhamelKernelSqIntegral lam t`.  Two bounds:
`mass ≤ t` always (the integrand is `≤ 1`), and `lam·mass ≤ 1/2` (from the
telescoped identity `2·lam·mass = 1 − e^{−2·lam·t} ≤ 1`).  Then
`(1 + lam)·mass = mass + lam·mass ≤ t + 1/2`. -/
theorem one_add_lambda_mul_duhamel_kernel_sq_integral_le {lam t : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (1 + lam) * duhamelKernelSqIntegral lam t ≤ t + 1 / 2 := by
  have hmass_nn : 0 ≤ duhamelKernelSqIntegral lam t :=
    duhamelKernelSqIntegral_nonneg ht
  have hmass_le_t : duhamelKernelSqIntegral lam t ≤ t :=
    duhamelKernelSqIntegral_le_t hlam ht
  have hlam_mass : lam * duhamelKernelSqIntegral lam t ≤ 1 / 2 := by
    have h := two_lambda_mul_duhamelKernelSqIntegral lam t
    have hexp_nn : (0 : ℝ) ≤ Real.exp (-(2 * lam * t)) := (Real.exp_pos _).le
    nlinarith [h, hexp_nn]
  have hexpand : (1 + lam) * duhamelKernelSqIntegral lam t
      = duhamelKernelSqIntegral lam t + lam * duhamelKernelSqIntegral lam t := by
    ring
  rw [hexpand]; linarith

variable {f : ℝ → ℝ}

/-- **The endpoint Cauchy–Schwarz bound.**  For a forcing `f` continuous on
`[0,t]` and `0 ≤ t`,

  `(perModeConv lam f t)² ≤ (∫₀ᵗ e^{−2·lam·(t−s)} ds) · ∫₀ᵗ f(s)² ds`.

The square of the kernel-weighted integral of `f` is `≤` the kernel mass
times the kernel-weighted integral of `f²`; here the weight is the full
kernel `e^{−2·lam·(t−s)}` paired against `f`, i.e. the weight is
`e^{−lam·(t−s)}` applied with multiplicity (so that the weighted average of
`g = e^{−lam·(t−s)}·f / w` recovers the convolution).  We pair the kernel
`e^{−lam·(t−s)}` with `f` directly through the discriminant inequality. -/
theorem perModeConv_endpoint_sq_le (lam : ℝ) (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) :
    (perModeConv lam f t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  set k : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s))) with hk_def
  have hconv_eq : perModeConv lam f t = ∫ s in (0 : ℝ)..t, k s * f s := rfl
  set A : ℝ := ∫ s in (0 : ℝ)..t, f s ^ 2 with hA
  set B : ℝ := ∫ s in (0 : ℝ)..t, k s * f s with hB
  set C : ℝ := ∫ s in (0 : ℝ)..t, k s ^ 2 with hC
  have hC_eq : C = duhamelKernelSqIntegral lam t := by
    rw [hC]; unfold duhamelKernelSqIntegral
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [hk_def, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have hquad : ∀ c : ℝ, 0 ≤ A * (c * c) + (-(2 * B)) * c + C := by
    intro c
    have hintegrand : (fun s => (k s - c * f s) ^ 2)
        = fun s => (c * c) * f s ^ 2 + (-(2 * c)) * (k s * f s) + k s ^ 2 := by
      funext s; ring
    have hi_f2 : IntervalIntegrable (fun s => f s ^ 2) volume 0 t :=
      ((hf.pow 2)).intervalIntegrable 0 t
    have hi_kf : IntervalIntegrable (fun s => k s * f s) volume 0 t := by
      apply Continuous.intervalIntegrable; rw [hk_def]; fun_prop
    have hi_k2 : IntervalIntegrable (fun s => k s ^ 2) volume 0 t := by
      apply Continuous.intervalIntegrable; rw [hk_def]; fun_prop
    have hexpand : (∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2)
        = (c * c) * A + (-(2 * c)) * B + C := by
      rw [hintegrand,
        intervalIntegral.integral_add
          ((hi_f2.const_mul (c * c)).add (hi_kf.const_mul (-(2 * c)))) hi_k2,
        intervalIntegral.integral_add (hi_f2.const_mul (c * c))
          (hi_kf.const_mul (-(2 * c))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2 :=
      intervalIntegral.integral_nonneg ht (fun s _ => sq_nonneg _)
    rw [hexpand] at hnonneg
    nlinarith [hnonneg]
  have hdiscrim : discrim A (-(2 * B)) C ≤ 0 :=
    discrim_le_zero (fun c => by nlinarith [hquad c])
  rw [discrim] at hdiscrim
  rw [hC_eq] at hdiscrim
  rw [hconv_eq]
  nlinarith [hdiscrim]

/-- **The per-mode one-derivative-gain estimate.**  For a forcing `f`
continuous on `[0,t]`, `0 ≤ lam` and `0 ≤ t`,

  `(1 + lam) · (perModeConv lam f t)² ≤ (t + 1/2) · ∫₀ᵗ f(s)² ds`.

The endpoint Cauchy–Schwarz bound times the uniform-in-`λ` kernel bound.
One Sobolev order is gained at every fixed `t > 0`, uniformly across the
spectrum. -/
theorem one_add_lambda_mul_perModeConv_endpoint_sq_le (lam : ℝ)
    (hlam : 0 ≤ lam) (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (1 + lam) * (perModeConv lam f t) ^ 2
      ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  have hcs := perModeConv_endpoint_sq_le (f := f) lam hf ht
  have hkernel := one_add_lambda_mul_duhamel_kernel_sq_integral_le hlam ht
  have hf2_nn : 0 ≤ ∫ s in (0 : ℝ)..t, f s ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun s _ => sq_nonneg _)
  have h1plus_nn : 0 ≤ 1 + lam := by linarith
  calc (1 + lam) * (perModeConv lam f t) ^ 2
      ≤ (1 + lam) * (duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2) :=
        mul_le_mul_of_nonneg_left hcs h1plus_nn
    _ = ((1 + lam) * duhamelKernelSqIntegral lam t) * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
        ring
    _ ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
        mul_le_mul_of_nonneg_right hkernel hf2_nn

end Scalar

section Assembly

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The endpoint mass `H^{c+1}`-summability (the σ-summability heart).**
For a fixed time `0 ≤ t`, a family of continuous-in-time per-mode forcing
functions `φ`, and an exponent `c`: if the `H^c`-weighted endpoint masses
`i ↦ (1 + λᵢ)^c · ∫₀ᵗ (φ i)²` are summable, then the `H^{c+1}`-weighted
squared endpoint values `i ↦ (1 + λᵢ)^{c+1} · (perModeConv λᵢ (φ i) t)²` are
summable.  The one-derivative gain `(1 + λᵢ)·(value)² ≤ (t + 1/2)·(mass)`
applied mode-by-mode dominates the value family by `(t + 1/2)` times the
forcing-mass family. -/
theorem duhamel_endpoint_value_weighted_summable
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (c + 1) *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hmass.mul_left (t + 1 / 2))
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (c + 1))
      (sq_nonneg _)
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hweight_split :
        tensorSobolevWeight (I := I) (M := M) i (c + 1) =
          tensorSobolevWeight (I := I) (M := M) i c * (1 + lam) := by
      have hbase_pos : (0 : ℝ) < 1 + lam :=
        lt_of_lt_of_le one_pos (by linarith)
      rw [tensorSobolevWeight, tensorSobolevWeight, hlam_def, Real.rpow_add hbase_pos,
        Real.rpow_one]
    have hwc_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i c
    have hgain := one_add_lambda_mul_perModeConv_endpoint_sq_le
      (f := φ i) lam hlam_nn (hφ i) ht
    calc tensorSobolevWeight (I := I) (M := M) i (c + 1) *
            (perModeConv lam (φ i) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i c *
            ((1 + lam) * (perModeConv lam (φ i) t) ^ 2) := by
          rw [hweight_split]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i c *
            ((t + 1 / 2) * ∫ s in (0 : ℝ)..t, (φ i s) ^ 2) :=
          mul_le_mul_of_nonneg_left hgain hwc_nn
      _ = (t + 1 / 2) * (tensorSobolevWeight (I := I) (M := M) i c *
            ∫ s in (0 : ℝ)..t, (φ i s) ^ 2) := by ring

/-- **The Duhamel value at fixed time `t`, viewed in `H^{c+1}`.**  For a
spatially-`H^c` forcing (continuous per-mode functions `φ` with summable
`H^c`-weighted endpoint masses), the element of `tensorHs (c + 1)` whose
`i`-th eigen-coordinate is the per-mode Duhamel value
`perModeConv λᵢ (φ i) t`.  The one-derivative gain places it one Sobolev
order above the forcing. -/
def duhamelValueHs {g : SmoothRiemannianMetric I M} {r s : ℕ} (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    tensorHs (I := I) (M := M) g r s (c + 1) where
  coeff i := perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t
  weighted_summable :=
    duhamel_endpoint_value_weighted_summable (I := I) (M := M) c ht φ hφ hmass

@[simp] theorem duhamelValueHs_coeff {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (duhamelValueHs (I := I) (M := M) c ht φ hφ hmass).coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := rfl

/-- For a spatially-`H^c` forcing with `c ≥ 0`, the value coordinate family
`i ↦ perModeConv λᵢ (φ i) t` is square-summable, hence the coordinate family
of an honest `L²` tensor (`H^{c+1} ⊆ L²`). -/
theorem duhamel_endpoint_value_summable_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {c : ℝ} (hc : 0 ≤ c) {t : ℝ}
    (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) :=
  tensorHs.coeff_summable_sq_of_nonneg (I := I) (M := M) (by linarith : 0 ≤ c + 1)
    (duhamelValueHs (I := I) (M := M) c ht φ hφ hmass)

set_option maxHeartbeats 800000 in
/-- **The Duhamel value at fixed time `t` lands in every `Hˢ` for a
spatially-smooth forcing.**  Fix `0 ≤ t` and continuous per-mode forcing
functions `φ`.  Suppose the forcing is **spatially smooth**: its
`H^c`-weighted endpoint masses `i ↦ (1 + λᵢ)^c · ∫₀ᵗ (φ i)²` are summable
for *every* `c ≥ 0` (the forcing lies in `H^c` at the integrated-`L²` level
for every order).  Then for every exponent `σ ≥ 0` there is an `Hˢ` element
whose chart-locality-free `L²` realization equals the fixed `L²` element

  `u := (eigenbasis).repr.symm (i ↦ perModeConv λᵢ (φ i) t)`

— the Duhamel value at `t`.  This is the precise statement that the Duhamel
value lies in the spectral smooth subspace `⋂_σ Hˢ`.

The single fixed `u` is realized coherently by every `Hˢ` witness because
all witnesses have the *same* eigen-coordinate family `i ↦ perModeConv λᵢ
(φ i) t`, and `tensorHsToL2` is coordinate-faithful. -/
theorem duhamel_into_all_tensorHs {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {t : ℝ} (ht : 0 ≤ t)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hsmooth : ∀ c : ℝ, 0 ≤ c →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    ∃ u : TensorL2 r s g,
      (∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ∧
      ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g r s σ,
          tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
              h_compact hσ v = u := by
  classical
  set bsis := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hbsis_def
  have hval_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) :=
    duhamel_endpoint_value_summable_sq (I := I) (M := M) (c := 0) le_rfl ht φ hφ
      (by simpa using hsmooth 0 le_rfl)
  have hmemℓp : Memℓp (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t‖ ^
            (2 : ℝ≥0∞).toReal) =
        (fun i => (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (φ i) t) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [h_eq]; exact hval_summable
  set u : TensorL2 r s g := bsis.repr.symm ⟨_, hmemℓp⟩ with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := by
    intro i
    rw [tensorL2Coeff, hu_def, hbsis_def,
      LinearIsometryEquiv.apply_symm_apply]
  refine ⟨u, hu_coeff, fun σ hσ => ?_⟩
  set c : ℝ := max (σ - 1) 0 with hc_def
  have hc_nn : 0 ≤ c := le_max_right _ _
  have hσ_le : σ ≤ c + 1 := by
    have : σ - 1 ≤ c := le_max_left _ _; linarith
  set vTop : tensorHs (I := I) (M := M) g r s (c + 1) :=
    duhamelValueHs (I := I) (M := M) (c := c) ht φ hφ (hsmooth c hc_nn) with hvTop_def
  have hv_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i σ * (vTop.coeff i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) vTop.weighted_summable
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
        (sq_nonneg _)
    · have hbase : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        one_le_one_add_lambda (I := I) (M := M) i
      have hwle : tensorSobolevWeight (I := I) (M := M) i σ ≤
          tensorSobolevWeight (I := I) (M := M) i (c + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase hσ_le
      exact mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
  set v : tensorHs (I := I) (M := M) g r s σ :=
    { coeff := vTop.coeff, weighted_summable := hv_summable } with hv_def
  refine ⟨v, ?_⟩
  refine bsis.repr.injective ?_
  ext i
  have hcoeff_lhs : (bsis.repr (tensorHsToL2 (I := I) (M := M)
        (g := g) (r := r) (s := s) h_compact hσ v)) i =
      tensorL2Coeff (I := I) (M := M) h_compact
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ v) i := rfl
  have hcoeff_rhs : (bsis.repr u) i =
      tensorL2Coeff (I := I) (M := M) h_compact u i := rfl
  rw [hcoeff_lhs, hcoeff_rhs,
    tensorHsToL2_tensorL2Coeff
      (I := I) (M := M) (h_compact := h_compact) hσ v i,
    hu_coeff i]
  rfl

end Assembly

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
