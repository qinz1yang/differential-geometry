import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighMinimizer_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.LaplaceCoefficient

/-!
# Weak Euler–Lagrange equation of the Rayleigh minimizer (S-W-EIG, G2)

A minimizer `u ∈ H¹₀(Ω)` of `(∫|∇v|² + W v²)/∫ρ v²` (normalized by `∫ρu² = 1`, value `μ`) satisfies
`∫⟨∇u,∇φ⟩ = ∫ (μρ − W) u φ` for every `φ ∈ H¹₀(Ω)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem inner_gradLp_eq_integral_EG {u φ : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hφ : DeGiorgi.MemW1pWitness 2 φ Ω) :
    ⟪DeGiorgi.gradLpOfWitness hu, DeGiorgi.gradLpOfWitness hφ⟫_ℝ =
      ∫ x in Ω, ⟪hu.weakGrad x, hφ.weakGrad x⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.weakGrad_memLp.coeFn_toLp, hφ.weakGrad_memLp.coeFn_toLp] with x hx hy
  change ⟪hu.weakGrad_memLp.toLp hu.weakGrad x, hφ.weakGrad_memLp.toLp hφ.weakGrad x⟫_ℝ = _
  rw [hx, hy]

omit [NeZero d] in
theorem gradLp_add_smul_EG {u φ : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hφ : DeGiorgi.MemW1pWitness 2 φ Ω) (t : ℝ) :
    DeGiorgi.gradLpOfWitness (hu.add (hφ.smul t)) =
      DeGiorgi.gradLpOfWitness hu + t • DeGiorgi.gradLpOfWitness hφ := by
  apply Lp.ext
  filter_upwards [(hu.add (hφ.smul t)).weakGrad_memLp.coeFn_toLp, hu.weakGrad_memLp.coeFn_toLp,
    hφ.weakGrad_memLp.coeFn_toLp, Lp.coeFn_add (DeGiorgi.gradLpOfWitness hu)
      (t • DeGiorgi.gradLpOfWitness hφ),
    Lp.coeFn_smul t (DeGiorgi.gradLpOfWitness hφ)] with x h1 h2 h3 h4 h5
  change (hu.add (hφ.smul t)).weakGrad_memLp.toLp _ x = _
  rw [h1, h4]
  simp only [Pi.add_apply, h5, Pi.smul_apply]
  change hu.weakGrad x + t • hφ.weakGrad x = _
  congr 1
  · exact h2.symm
  · rw [show (DeGiorgi.gradLpOfWitness hφ) x = hφ.weakGrad x from h3]

omit [NeZero d] in
theorem integral_weight_sq_add_EG {c : E → ℝ} (hcm : Measurable c) {B : ℝ}
    (hB : ∀ᵐ x ∂(volume.restrict Ω), |c x| ≤ B) {a b : E → ℝ}
    (ha : MemLp a 2 (volume.restrict Ω)) (hb : MemLp b 2 (volume.restrict Ω)) (t : ℝ) :
    (∫ x in Ω, c x * (a x + t * b x) ^ 2) = (∫ x in Ω, c x * a x ^ 2) +
      2 * t * (∫ x in Ω, c x * a x * b x) + t ^ 2 * ∫ x in Ω, c x * b x ^ 2 := by
  have h1 := integrable_weight_sq_EG hcm hB ha
  have h2 : Integrable (fun x => c x * a x * b x) (volume.restrict Ω) :=
    (memLp_weight_mul_EG hcm hB ha).integrable_mul hb
  have h3 := integrable_weight_sq_EG hcm hB hb
  have : (fun x => c x * (a x + t * b x) ^ 2) = fun x =>
      (c x * a x ^ 2 + (2 * t) * (c x * a x * b x)) + t ^ 2 * (c x * b x ^ 2) := by
    ext x
    ring
  have hs1 : Integrable (fun x => c x * a x ^ 2 + 2 * t * (c x * a x * b x))
      (volume.restrict Ω) := h1.add (h2.const_mul _)
  rw [this, integral_add hs1 (h3.const_mul _), integral_add h1 (h2.const_mul _),
    integral_const_mul, integral_const_mul]

theorem eq_zero_of_quadratic_nonneg_EG {L M : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * L + t ^ 2 * M) :
    L = 0 := by
  by_contra hL
  have hM : 0 < |M| + 1 := by positivity
  have := h (-L / (|M| + 1))
  have h2 : 2 * (-L / (|M| + 1)) * L + (-L / (|M| + 1)) ^ 2 * M =
      -L ^ 2 / (|M| + 1) ^ 2 * (2 * (|M| + 1) - M) := by
    field_simp
    ring
  rw [h2] at this
  have h3 : 0 < 2 * (|M| + 1) - M := by
    nlinarith [le_abs_self M]
  have h4 : 0 < L ^ 2 := by positivity
  have h5 : 0 < L ^ 2 / (|M| + 1) ^ 2 * (2 * (|M| + 1) - M) := by positivity
  have h6 : -L ^ 2 / (|M| + 1) ^ 2 * (2 * (|M| + 1) - M) =
      -(L ^ 2 / (|M| + 1) ^ 2 * (2 * (|M| + 1) - M)) := by ring
  linarith

theorem weak_euler_lagrange_EG (hΩ : IsOpen Ω) {ρ W : E → ℝ} (hρm : Measurable ρ)
    (hWm : Measurable W) {B : ℝ} (hρB : ∀ x ∈ Ω, |ρ x| ≤ B) (hWB : ∀ x ∈ Ω, |W x| ≤ B)
    {u : E → ℝ} (hu0 : DeGiorgi.MemW01p 2 u Ω) (hu : DeGiorgi.MemW1pWitness 2 u Ω) {μ : ℝ}
    (hN : (∫ x in Ω, ρ x * u x ^ 2) = 1)
    (hQ : (∫ x in Ω, ‖hu.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * u x ^ 2 = μ)
    (hmin : ∀ v : E → ℝ, DeGiorgi.MemW01p 2 v Ω → ∀ hv : DeGiorgi.MemW1pWitness 2 v Ω,
      μ * (∫ x in Ω, ρ x * v x ^ 2) ≤
        (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * v x ^ 2)
    {φ : E → ℝ} (hφ0 : DeGiorgi.MemW01p 2 φ Ω) (hφ : DeGiorgi.MemW1pWitness 2 φ Ω) :
    (∫ x in Ω, ⟪hu.weakGrad x, hφ.weakGrad x⟫_ℝ) =
      ∫ x in Ω, ((μ * ρ x - W x) * u x) * φ x := by
  have hρae : ∀ᵐ x ∂(volume.restrict Ω), |ρ x| ≤ B :=
    ae_restrict_of_forall_mem hΩ.measurableSet hρB
  have hWae : ∀ᵐ x ∂(volume.restrict Ω), |W x| ≤ B :=
    ae_restrict_of_forall_mem hΩ.measurableSet hWB
  have huL := hu.memLp
  have hφL := hφ.memLp
  have hinner := inner_gradLp_eq_integral_EG hu hφ
  have hGsq := norm_gradLpOfWitness_sq_eq_integral hu
  have hHsq := norm_gradLpOfWitness_sq_eq_integral hφ
  have hWuφ : Integrable (fun x => W x * u x * φ x) (volume.restrict Ω) :=
    (memLp_weight_mul_EG hWm hWae huL).integrable_mul hφL
  have hρuφ : Integrable (fun x => ρ x * u x * φ x) (volume.restrict Ω) :=
    (memLp_weight_mul_EG hρm hρae huL).integrable_mul hφL
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (⟪DeGiorgi.gradLpOfWitness hu, DeGiorgi.gradLpOfWitness hφ⟫_ℝ +
      (∫ x in Ω, W x * u x * φ x) - μ * ∫ x in Ω, ρ x * u x * φ x) +
      t ^ 2 * (‖DeGiorgi.gradLpOfWitness hφ‖ ^ 2 + (∫ x in Ω, W x * φ x ^ 2) -
        μ * ∫ x in Ω, ρ x * φ x ^ 2) := by
    intro t
    have hv0 : DeGiorgi.MemW01p 2 (fun x => u x + t * φ x) Ω := hu0.add (hφ0.smul t)
    have h := hmin _ hv0 (hu.add (hφ.smul t))
    rw [← norm_gradLpOfWitness_sq_eq_integral (hu.add (hφ.smul t)), gradLp_add_smul_EG,
      integral_weight_sq_add_EG hWm hWae huL hφL t,
      integral_weight_sq_add_EG hρm hρae huL hφL t] at h
    have hexp : ‖DeGiorgi.gradLpOfWitness hu + t • DeGiorgi.gradLpOfWitness hφ‖ ^ 2 =
        ‖DeGiorgi.gradLpOfWitness hu‖ ^ 2 + 2 * t * ⟪DeGiorgi.gradLpOfWitness hu,
          DeGiorgi.gradLpOfWitness hφ⟫_ℝ + t ^ 2 * ‖DeGiorgi.gradLpOfWitness hφ‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hexp] at h
    have hμN : μ * (∫ x in Ω, ρ x * u x ^ 2) = μ := by rw [hN, mul_one]
    nlinarith [hμN, hGsq, hQ]
  have hL := eq_zero_of_quadratic_nonneg_EG key
  rw [← hinner]
  have hrhs : (∫ x in Ω, ((μ * ρ x - W x) * u x) * φ x) =
      μ * (∫ x in Ω, ρ x * u x * φ x) - ∫ x in Ω, W x * u x * φ x := by
    rw [← integral_const_mul, ← integral_sub (hρuφ.const_mul μ) hWuφ]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hrhs]
  linarith

end DifferentialGeometry.Analysis.Sobolev.Euclidean
