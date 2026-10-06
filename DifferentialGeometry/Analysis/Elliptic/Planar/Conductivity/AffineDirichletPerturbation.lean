import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.FrozenComparison
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation

/-!
The homogeneous Dirichlet replacement of a unit affine function has a uniformly
bounded gradient and a small gradient error when the coefficient is close to a
fixed constant elliptic coefficient. Both estimates concern the same constructed
solution and the same weak-gradient witness.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

namespace DifferentialGeometry.Analysis

open DeGiorgi

local notation "V" => EuclideanSpace ℝ (Fin 2)

private theorem norm_toLp_two_eq_sqrt_integral
    {μ : Measure V} {f : V → V} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ) := by
  rw [Lp.norm_toLp, toReal_eLpNorm]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using
    (lpNorm_eq_integral_norm_rpow_toReal (μ := μ) (f := f) (p := (2 : ENNReal))
      (by norm_num) (by simp) hf.aestronglyMeasurable)

/-- Construct the homogeneous weak Dirichlet solution with unit affine trace.
The coefficient oscillation is measured against the fixed constant coefficient
`B`; its coercivity constant controls both estimates for the selected witness. -/
theorem exists_affine_dirichlet_solution_with_uniform_gradient_error
    (A B : EllipticCoeff 2 (Metric.ball (0 : V) 1))
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hB : B.a = fun _ => K)
    (e : V) (he : ‖e‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε / B.lam ≤ 1 / 2)
    (hosc : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), ∀ ξ : V,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖) :
    ∃ (u : V → ℝ) (wu : MemW1pWitness 2 u (Metric.ball (0 : V) 1)),
      IsHomogeneousWeakSolution A u ∧
      MemW01p 2 (fun x => u x - inner ℝ e x) (Metric.ball (0 : V) 1) ∧
      (∫ x in Metric.ball (0 : V) 1, ‖wu.weakGrad x - e‖ ^ (2 : ℕ)) ≤
        4 * (ε / B.lam) ^ 2 * volume.real (Metric.ball (0 : V) 1) ∧
      (∫ x in Metric.ball (0 : V) 1, ‖wu.weakGrad x‖ ^ (2 : ℕ)) ≤
        4 * volume.real (Metric.ball (0 : V) 1) := by
  let μ := volume.restrict (Metric.ball (0 : V) 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let ℓ : V → ℝ := fun x => inner ℝ e x
  have hℓderiv (x : V) : fderiv ℝ ℓ x = innerSL ℝ e := (innerSL ℝ e).fderiv
  let wℓ : MemW1pWitness 2 ℓ (Metric.ball (0 : V) 1) :=
    { memLp := by
        apply MemLp.of_bound (innerSL ℝ e).continuous.aestronglyMeasurable 1
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        have hxnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
        exact (norm_inner_le_norm e x).trans (by simpa only [he, one_mul] using hxnorm.le)
      weakGrad := fun _ => e
      weakGrad_component_memLp := fun i => memLp_const (e i)
      isWeakGrad := by
        intro i
        have hi := HasWeakPartialDeriv.of_contDiff (Ω := Metric.ball (0 : V) 1)
          (i := i) Metric.isOpen_ball
          (show ContDiff ℝ 1 ℓ from (innerSL ℝ e).contDiff)
        simpa [hℓderiv, innerSL_apply_apply, EuclideanSpace.inner_single_right] using hi }
  have hdiv_const : HasWeakDiv (fun _ : V => (0 : ℝ))
      (fun _ : V => matMulE K e) (Metric.ball (0 : V) 1) := by
    have hd := hasWeakDiv_sum_of_hasWeakPartialDeriv
      (Ω := Metric.ball (0 : V) 1) (F := fun _ : V => matMulE K e)
      (G := fun _ : Fin 2 => fun _ : V => (0 : ℝ))
      (fun i => (integrable_const ((matMulE K e) i)).locallyIntegrable)
      (fun _ => (integrable_const (0 : ℝ)).locallyIntegrable)
      (fun i => by
        simpa using HasWeakPartialDeriv.of_contDiff (i := i) Metric.isOpen_ball
          (contDiff_const : ContDiff ℝ 1 (fun _ : V => (matMulE K e) i)))
    simpa using hd
  have hℓweak : IsHomogeneousWeakSolution B ℓ := by
    refine ⟨wℓ.memW1p, ?_⟩
    intro w φ hφ wφ
    rw [bilinFormOfCoeff_eq_left Metric.isOpen_ball B w wℓ wφ]
    have hd : HasWeakDiv (fun _ : V => -(0 : ℝ))
        (fun x => matMulE (B.a x) (wℓ.weakGrad x)) (Metric.ball (0 : V) 1) := by
      simpa only [hB, wℓ, neg_zero] using hdiv_const
    have hw := (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv Metric.isOpen_ball wℓ
      (memLp_const 0 : MemLp (fun _ : V => (0 : ℝ)) 2 μ)).mpr hd
    simpa only [zero_mul, integral_zero] using hw φ hφ wφ
  obtain ⟨u, hu, htrace⟩ := aHarmonic_replacement_exists (by norm_num)
    Metric.isOpen_ball Metric.isBounded_ball A wℓ.memW1p
  let wu : MemW1pWitness 2 u (Metric.ball (0 : V) 1) := hu.1.someWitness
  have htraceNeg : MemW01p 2 (fun x => ℓ x - u x) (Metric.ball (0 : V) 1) := by
    simpa only [neg_one_mul, neg_sub] using htrace.smul (-1)
  have hcompare := weakGrad_l2_sub_le_of_coefficient_oscillation Metric.isOpen_ball
    A B hu hℓweak htraceNeg wu wℓ hε hosc
  let U := gradLpOfWitness wu
  let E := gradLpOfWitness wℓ
  have hU : ‖U‖ = Real.sqrt (∫ x, ‖wu.weakGrad x‖ ^ (2 : ℕ) ∂μ) :=
    norm_toLp_two_eq_sqrt_integral wu.weakGrad_memLp
  have hE : ‖E‖ = Real.sqrt (volume.real (Metric.ball (0 : V) 1)) := by
    calc
      ‖E‖ = Real.sqrt (∫ x, ‖wℓ.weakGrad x‖ ^ (2 : ℕ) ∂μ) :=
        norm_toLp_two_eq_sqrt_integral wℓ.weakGrad_memLp
      _ = Real.sqrt (volume.real (Metric.ball (0 : V) 1)) := by simp [wℓ, he, μ]
  have hD : ‖E - U‖ =
      Real.sqrt (∫ x, ‖e - wu.weakGrad x‖ ^ (2 : ℕ) ∂μ) := by
    change ‖wℓ.weakGrad_memLp.toLp wℓ.weakGrad -
      wu.weakGrad_memLp.toLp wu.weakGrad‖ = _
    rw [← MemLp.toLp_sub]
    exact norm_toLp_two_eq_sqrt_integral (wℓ.weakGrad_memLp.sub wu.weakGrad_memLp)
  have hDU : ‖E - U‖ ≤ (ε / B.lam) * ‖U‖ := by
    rw [hD, hU]
    simpa only [wℓ, Real.rpow_two, ← Real.sqrt_eq_rpow] using hcompare
  have htriangle : ‖U‖ ≤ ‖E - U‖ + ‖E‖ := by
    calc
      ‖U‖ = ‖(U - E) + E‖ := by rw [sub_add_cancel]
      _ ≤ ‖U - E‖ + ‖E‖ := norm_add_le _ _
      _ = ‖E - U‖ + ‖E‖ := by rw [norm_sub_rev]
  have hhalf := mul_le_mul_of_nonneg_right hsmall (norm_nonneg U)
  have hUbound : ‖U‖ ≤ 2 * ‖E‖ := by linarith only [htriangle, hDU, hhalf]
  have hδ : 0 ≤ ε / B.lam := div_nonneg hε B.hlam.le
  have hDbound : ‖E - U‖ ≤ 2 * (ε / B.lam) * ‖E‖ := by
    calc
      ‖E - U‖ ≤ (ε / B.lam) * ‖U‖ := hDU
      _ ≤ (ε / B.lam) * (2 * ‖E‖) := mul_le_mul_of_nonneg_left hUbound hδ
      _ = _ := by ring
  have hU2 : ‖U‖ ^ 2 = ∫ x, ‖wu.weakGrad x‖ ^ (2 : ℕ) ∂μ := by
    rw [hU, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  have hE2 : ‖E‖ ^ 2 = volume.real (Metric.ball (0 : V) 1) := by
    rw [hE, Real.sq_sqrt (measureReal_nonneg)]
  have hD2 : ‖E - U‖ ^ 2 = ∫ x, ‖wu.weakGrad x - e‖ ^ (2 : ℕ) ∂μ := by
    rw [hD, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      congrArg (fun r : ℝ => r ^ (2 : ℕ)) (norm_sub_rev e (wu.weakGrad x)))
  refine ⟨u, wu, hu, htrace, ?_, ?_⟩
  · have hs := (sq_le_sq₀ (norm_nonneg (E - U))
      (mul_nonneg (mul_nonneg (by norm_num) hδ) (norm_nonneg E))).mpr hDbound
    rw [hD2] at hs
    calc
      (∫ x, ‖wu.weakGrad x - e‖ ^ (2 : ℕ) ∂μ) ≤
          (2 * (ε / B.lam) * ‖E‖) ^ 2 := hs
      _ = 4 * (ε / B.lam) ^ 2 * volume.real (Metric.ball (0 : V) 1) := by
        rw [mul_pow, mul_pow, hE2]
        norm_num
  · have hs := (sq_le_sq₀ (norm_nonneg U) (mul_nonneg (by norm_num) (norm_nonneg E))).mpr
      hUbound
    rw [hU2] at hs
    calc
      (∫ x, ‖wu.weakGrad x‖ ^ (2 : ℕ) ∂μ) ≤ (2 * ‖E‖) ^ 2 := hs
      _ = 4 * volume.real (Metric.ball (0 : V) 1) := by rw [mul_pow, hE2]; norm_num

end DifferentialGeometry.Analysis
