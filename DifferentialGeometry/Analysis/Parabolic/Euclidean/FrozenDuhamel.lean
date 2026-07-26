import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelApprox
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelPDE
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Frozen Euclidean Duhamel evolution

This file starts the analytic realization behind the frozen-coefficient
parametrix.  The first layer is deliberately dimension-generic: for a bounded
continuous spatial datum with bounded realized first and second Frechet
derivatives, the positive-time heat evolution differentiates in time by the
Euclidean Laplacian.

The proof does not assume a heat equation for the evolved datum.  It rewrites
the heat convolution using the time-one Gaussian, differentiates that scaled
integral using the finite first Gaussian moment, and transfers the resulting
first derivative by integration by parts.  The zero-trace Duhamel theorem and
constant-SPD conjugation are built on this producer below.
-/

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section CoreOperators

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Trace evaluation on a bounded realized second Frechet derivative. -/
def lapEval : (V →L[ℝ] V →L[ℝ] F) →L[ℝ] F :=
  ∑ i : Fin (Module.finrank ℝ V),
    (ContinuousLinearMap.apply ℝ F ((stdOrthonormalBasis ℝ V) i)).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] F)
        ((stdOrthonormalBasis ℝ V) i))

/-- The bounded continuous Euclidean Laplacian associated to a bounded
continuous realized second Frechet derivative. -/
def coreLap (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) :
    BoundedContinuousFunction V F :=
  (lapEval (V := V) (F := F)).compLeftContinuousBounded V d2u

@[simp]
theorem coreLap_apply
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) (x : V) :
    coreLap d2u x =
      ∑ i : Fin (Module.finrank ℝ V),
        d2u x ((stdOrthonormalBasis ℝ V) i)
          ((stdOrthonormalBasis ℝ V) i) := by
  simp [coreLap, lapEval]

end CoreOperators

section ScaledEvolution

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat evolution written against the fixed time-one Gaussian. -/
def heatScaled (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ z : V, baseHeat z • u (x - heatScale t • z)

/-- Positive-time heat convolution equals its fixed-Gaussian scaled form. -/
theorem heatSup_scaled {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    heatSup t u x = heatScaled t u x := by
  let r := heatScale t
  have hr : 0 < r := by
    simpa only [r] using heatScale_pos ht
  let f : V → F := fun z => baseHeat z • u (x - r • z)
  have hscale :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) f hr.le
  have hscale' :
      (∫ y : V, baseHeat (r⁻¹ • y) • u (x - y)) =
        r ^ Module.finrank ℝ V •
          ∫ z : V, baseHeat z • u (x - r • z) := by
    simpa only [f, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hscale
  unfold heatSup supKernel heatKernel heatScaled
  change
    (∫ y : V,
      ((r ^ Module.finrank ℝ V)⁻¹ * baseHeat (r⁻¹ • y)) • u (x - y)) = _
  calc
    (∫ y : V,
        ((r ^ Module.finrank ℝ V)⁻¹ * baseHeat (r⁻¹ • y)) • u (x - y)) =
        (r ^ Module.finrank ℝ V)⁻¹ •
          ∫ y : V, baseHeat (r⁻¹ • y) • u (x - y) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      rw [mul_smul]
    _ = (r ^ Module.finrank ℝ V)⁻¹ •
          (r ^ Module.finrank ℝ V •
            ∫ z : V, baseHeat z • u (x - r • z)) := by
      rw [hscale']
    _ = ∫ z : V, baseHeat z • u (x - r • z) := by
      rw [inv_smul_smul₀ (pow_ne_zero _ hr.ne')]

/-- The fixed-Gaussian scaled heat evolution is continuous in its time
parameter, including at time zero. -/
theorem heatScaled_cont (u : BoundedContinuousFunction V F) (x : V) :
    Continuous (fun t : ℝ => heatScaled t u x) := by
  unfold heatScaled
  apply continuous_of_dominated
    (bound := fun z : V => ‖u‖ * baseHeat z)
  · intro t
    apply Continuous.aestronglyMeasurable
    fun_prop
  · intro t
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (baseHeat_nonneg z)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (baseHeat_nonneg z)
  · exact (baseHeat_int (V := V)).const_mul ‖u‖
  · apply Filter.Eventually.of_forall
    intro z
    fun_prop

/-- The fixed-Gaussian formula has the correct value at time zero. -/
@[simp]
theorem heatScaled_zero (u : BoundedContinuousFunction V F) (x : V) :
    heatScaled 0 u x = u x := by
  unfold heatScaled heatScale
  simp only [Real.sqrt_zero, zero_smul, sub_zero]
  rw [integral_smul_const, integral_baseHeat, one_smul]

/-- The fixed-Gaussian heat formula is a contraction at every real parameter.
For negative parameters this merely uses Lean's convention `sqrt t = 0`. -/
theorem heatScaled_norm (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatScaled t u x‖ ≤ ‖u‖ := by
  unfold heatScaled
  calc
    ‖∫ z : V, baseHeat z • u (x - heatScale t • z)‖ ≤
        ∫ z : V, ‖u‖ * baseHeat z := by
      apply norm_integral_le_of_norm_le
        ((baseHeat_int (V := V)).const_mul ‖u‖)
      filter_upwards with z
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (baseHeat_nonneg z)]
      exact mul_le_mul_of_nonneg_left
        (u.norm_coe_le_norm (x - heatScale t • z)) (baseHeat_nonneg z)
    _ = ‖u‖ := by
      rw [integral_const_mul, integral_baseHeat, mul_one]

/-- A continuous linear map commutes with the fixed-Gaussian heat formula. -/
theorem heatScaled_map {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) :
    L (heatScaled t u x) =
      heatScaled t (L.compLeftContinuousBounded V u) x := by
  have hint : Integrable
      (fun z : V => baseHeat z • u (x - heatScale t • z)) :=
    kernel_comp_int (baseHeat_int (V := V)) u (by fun_prop)
  unfold heatScaled
  rw [← L.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards with z
  simp

/-- Spatial differentiation commutes with the fixed-Gaussian heat formula
when the supplied bounded first jet is globally realized. -/
theorem heatScaled_space (t : ℝ)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    HasFDerivAt (fun y : V => heatScaled t u y) (heatScaled t du x) x := by
  let F₀ : V → V → F := fun y z =>
    baseHeat z • u (y - heatScale t • z)
  let F₁ : V → V → (V →L[ℝ] F) := fun y z =>
    baseHeat z • du (y - heatScale t • z)
  let bound : V → ℝ := fun z => ‖du‖ * baseHeat z
  have hs : (Set.univ : Set V) ∈ 𝓝 x := Set.univ_mem
  have hmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (F₀ y) (volume : Measure V) := by
    apply Filter.Eventually.of_forall
    intro y
    apply Continuous.aestronglyMeasurable
    dsimp only [F₀]
    fun_prop
  have hint : Integrable (F₀ x) := by
    dsimp only [F₀]
    exact kernel_comp_int (baseHeat_int (V := V)) u (by fun_prop)
  have hder_meas : AEStronglyMeasurable (F₁ x) (volume : Measure V) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [F₁]
    fun_prop
  have hbound : ∀ᵐ z ∂(volume : Measure V), ∀ y ∈ Set.univ,
      ‖F₁ y z‖ ≤ bound z := by
    apply Filter.Eventually.of_forall
    intro z y hy
    dsimp only [F₁, bound]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (baseHeat_nonneg z)]
    exact mul_le_mul_of_nonneg_left
      (du.norm_coe_le_norm (y - heatScale t • z)) (baseHeat_nonneg z)
  have hbound_int : Integrable bound := by
    dsimp only [bound]
    exact (baseHeat_int (V := V)).const_mul ‖du‖
  have hdiff : ∀ᵐ z ∂(volume : Measure V), ∀ y ∈ Set.univ,
      HasFDerivAt (F₀ · z) (F₁ y z) y := by
    apply Filter.Eventually.of_forall
    intro z y hy
    have harg : HasFDerivAt (fun q : V => q - heatScale t • z)
        (ContinuousLinearMap.id ℝ V) y :=
      (hasFDerivAt_id y).sub_const (heatScale t • z)
    have hcomp := (hu (y - heatScale t • z)).comp y harg
    dsimp only [F₀, F₁]
    exact hcomp.const_smul (baseHeat z)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F₀) (F' := F₁) (bound := bound) hs hmeas hint hder_meas
      hbound hbound_int hdiff
  simpa only [F₀, F₁, heatScaled] using key

/-- Quantitative approximation gives right convergence of the positive-time
heat evolution to its bounded half-Holder datum. -/
theorem heatSup_zero {K : ℝ≥0} (u : BoundedContinuousFunction V F)
    (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x : V) :
    Tendsto (fun t : ℝ => heatSup t u x) (ᵊ[>] (0 : ℝ)) (ᵊ (u x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (heatScale t))
      (ᵊ[>] (0 : ℝ)) (ᵊ 0) := by
    have hfull := (Real.continuous_sqrt.comp Real.continuous_sqrt).continuousAt
    simpa only [heatScale, Real.sqrt_zero] using hfull.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto
      (fun t : ℝ => (K : ℝ) * Real.sqrt (heatScale t) * heatC0Half V)
      (ᵊ[>] (0 : ℝ)) (ᵊ 0) := by
    have h₁ := Tendsto.const_mul (K : ℝ) hsqrt
    have h₂ := Tendsto.mul_const (heatC0Half V) h₁
    simpa only [mul_zero] using h₂
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hupper
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact heatSup_id_norm ht hu x

private theorem kernel_comp_int {K : V → ℝ} (hK : Integrable K)
    (u : BoundedContinuousFunction V F) {p : V → V} (hp : Continuous p) :
    Integrable (fun z : V => K z • u (p z)) := by
  refine (hK.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hK.aestronglyMeasurable.smul
      ((u.continuous.comp hp).aestronglyMeasurable)
  · filter_upwards with z
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (p z)) (norm_nonneg _)

private theorem baseFirst_int :
    Integrable (fun z : V => ‖z‖ * baseHeat z) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul (baseHeatMass V)⁻¹
  have heq : (fun z : V => ‖z‖ * baseHeat z) = fun z : V =>
      (baseHeatMass V)⁻¹ *
        (‖z‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖z‖ ^ 2)) := by
    funext z
    unfold baseHeat
    ring
  rw [heq]
  exact h

private def scaledDt (t : ℝ)
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (x z : V) : F :=
  baseHeat z •
    du (x - heatScale t • z) ((-(2 * heatScale t)⁻¹) • z)

/-- Differentiation of the fixed-Gaussian scaled heat evolution at positive
time.  The derivative is still in first-derivative form; the following layer
identifies it with the heat evolution of the Laplacian. -/
theorem heatScaled_time {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    HasDerivAt (fun s : ℝ => heatScaled s u x)
      (∫ z : V, scaledDt t du x z) t := by
  let s₀ : ℝ := t / 2
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]
    linarith
  let r₀ : ℝ := heatScale s₀
  have hr₀ : 0 < r₀ := by
    simpa only [r₀] using heatScale_pos hs₀
  let F₀ : ℝ → V → F := fun s z =>
    baseHeat z • u (x - heatScale s • z)
  let F₁ : ℝ → V → F := fun s z => scaledDt s du x z
  let bound : V → ℝ := fun z =>
    ((2 * r₀)⁻¹ * ‖du‖) * (‖z‖ * baseHeat z)
  have hs : Set.Ioi s₀ ∈ ᵊ t := Set.Ioi_mem_nhds (by
    dsimp only [s₀]
    linarith)
  have hmeas : ∀ᶠ s in ᵊ t, AEStronglyMeasurable (F₀ s) := by
    apply Filter.Eventually.of_forall
    intro s
    apply Continuous.aestronglyMeasurable
    dsimp only [F₀]
    fun_prop
  have hint : Integrable (F₀ t) := by
    apply kernel_comp_int (baseHeat_int (V := V)) u
    fun_prop
  have hder_meas : AEStronglyMeasurable (F₁ t) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [F₁, scaledDt]
    fun_prop
  have hbound_int : Integrable bound := by
    dsimp only [bound]
    exact (baseFirst_int (V := V)).const_mul _
  have hcoef : ∀ s ∈ Set.Ioi s₀,
      ‖(-(2 * heatScale s)⁻¹ : ℝ)‖ ≤ (2 * r₀)⁻¹ := by
    intro s hs_mem
    have hs_pos : 0 < s := hs₀.trans hs_mem
    have hrs : r₀ ≤ heatScale s := by
      dsimp only [r₀, heatScale]
      exact Real.sqrt_le_sqrt hs_mem.le
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num)
      (heatScale_pos hs_pos)))]
    exact (inv_le_inv₀ (mul_pos (by norm_num) (heatScale_pos hs_pos))
      (mul_pos (by norm_num) hr₀)).2 (mul_le_mul_of_nonneg_left hrs (by norm_num))
  have hbound : ∀ᵐ z ∂(volume : Measure V), ∀ s ∈ Set.Ioi s₀,
      ‖F₁ s z‖ ≤ bound z := by
    apply Filter.Eventually.of_forall
    intro z s hs_mem
    have hc := hcoef s hs_mem
    dsimp only [F₁, scaledDt, bound]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (baseHeat_nonneg z)]
    calc
      baseHeat z *
          ‖du (x - heatScale s • z) ((-(2 * heatScale s)⁻¹) • z)‖ ≤
          baseHeat z *
            (‖du (x - heatScale s • z)‖ * ‖(-(2 * heatScale s)⁻¹ : ℝ) • z‖) := by
        gcongr
        exact (du (x - heatScale s • z)).le_opNorm _
      _ ≤ baseHeat z * (‖du‖ * ((2 * r₀)⁻¹ * ‖z‖)) := by
        rw [norm_smul]
        gcongr
        · exact du.norm_coe_le_norm _
        · exact hc
      _ = ((2 * r₀)⁻¹ * ‖du‖) * (‖z‖ * baseHeat z) := by ring
  have hdiff : ∀ᵐ z ∂(volume : Measure V), ∀ s ∈ Set.Ioi s₀,
      HasDerivAt (F₀ · z) (F₁ s z) s := by
    apply Filter.Eventually.of_forall
    intro z s hs_mem
    have hs_pos : 0 < s := hs₀.trans hs_mem
    have hscale : HasDerivAt heatScale (1 / (2 * heatScale s)) s := by
      simpa only [heatScale] using Real.hasDerivAt_sqrt hs_pos.ne'
    have harg : HasDerivAt (fun q : ℝ => x - heatScale q • z)
        ((-(2 * heatScale s)⁻¹) • z) s := by
      convert (hasDerivAt_const s x).sub (hscale.smul_const z) using 1
      simp only [zero_sub, one_div, neg_smul]
    have hcomp := (hu (x - heatScale s • z)).comp_hasDerivAt s harg
    dsimp only [F₀, F₁, scaledDt]
    exact hcomp.const_smul (baseHeat z)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F₀) (F' := F₁) (bound := bound) hs hmeas hint hder_meas
      hbound hbound_int hdiff
  simpa only [F₀, F₁, heatScaled] using key.2

private def evalD1
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (v : V) :
    BoundedContinuousFunction V F :=
  (ContinuousLinearMap.apply ℝ F v).compLeftContinuousBounded V du

private def evalD2
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (v w : V) : BoundedContinuousFunction V F :=
  ((ContinuousLinearMap.apply ℝ F w).comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] F) v)).compLeftContinuousBounded V d2u

@[simp] private theorem evalD1_apply
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (v x : V) :
    evalD1 du v x = du x v := rfl

@[simp] private theorem evalD2_apply
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (v w x : V) : evalD2 d2u v w x = d2u x v w := rfl

private theorem baseD1_integrable (v : V) :
    Integrable (baseD1 v : V → ℝ) := by
  simpa [heatD1, heatScale] using
    (heatD1_int (V := V) (t := (1 : ℝ)) (by norm_num) v)

/-- The scaled first-derivative expression is the fixed-Gaussian heat
evolution of the realized Euclidean Laplacian.  This is the analytic
integration-by-parts step; no heat equation is assumed. -/
theorem scaledDt_eq_lap {t : ℝ} (ht : 0 < t)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    (∫ z : V, scaledDt t du x z) = heatScaled t (coreLap d2u) x := by
  let r := heatScale t
  have hr : 0 < r := by
    simpa only [r] using heatScale_pos ht
  let b := stdOrthonormalBasis ℝ V
  let p : V → V := fun z => x - r • z
  have hp : Continuous p := by
    dsimp only [p]
    fun_prop
  have harg : ∀ z : V,
      HasFDerivAt p (-r • ContinuousLinearMap.id ℝ V) z := by
    intro z
    dsimp only [p]
    simpa using (hasFDerivAt_const z x).sub
      ((r • ContinuousLinearMap.id ℝ V).hasFDerivAt)
  have hgder : ∀ (i : Fin (Module.finrank ℝ V)) (z : V),
      fderiv ℝ (fun y : V => du (p y) (b i)) z (b i) =
        (-r) • d2u (p z) (b i) (b i) := by
    intro i z
    let ev : (V →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (b i)
    have hcomp := (hdu (p z)).comp z (harg z)
    have heval := ev.hasFDerivAt.comp z hcomp
    rw [heval.fderiv]
    simp [ev, ContinuousLinearMap.comp_apply]
  have hgdiff : ∀ (i : Fin (Module.finrank ℝ V)) (z : V),
      DifferentiableAt ℝ (fun y : V => du (p y) (b i)) z := by
    intro i z
    let ev : (V →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (b i)
    exact (ev.hasFDerivAt.comp z ((hdu (p z)).comp z (harg z))).differentiableAt
  have hD1int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => baseD1 (b i) z • du (p z) (b i)) := by
    intro i
    simpa only [evalD1_apply] using
      kernel_comp_int (baseD1_integrable (V := V) (b i)) (evalD1 du (b i)) hp
  have hD2int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => baseHeat z • d2u (p z) (b i) (b i)) := by
    intro i
    simpa only [evalD2_apply] using
      kernel_comp_int (baseHeat_int (V := V)) (evalD2 d2u (b i) (b i)) hp
  have hD0int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => baseHeat z • du (p z) (b i)) := by
    intro i
    simpa only [evalD1_apply] using
      kernel_comp_int (baseHeat_int (V := V)) (evalD1 du (b i)) hp
  have hparts : ∀ i : Fin (Module.finrank ℝ V),
      (∫ z : V, baseD1 (b i) z • du (p z) (b i)) =
        r • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
    intro i
    have hleft : Integrable (fun z : V =>
        fderiv ℝ (baseHeat : V → ℝ) z (b i) • du (p z) (b i)) := by
      simpa only [(baseHeat_hasFDeriv _).fderiv, baseD1Map_apply] using hD1int i
    have hright : Integrable (fun z : V =>
        baseHeat z • fderiv ℝ (fun y : V => du (p y) (b i)) z (b i)) := by
      have hraw := (hD2int i).const_smul (-r)
      refine hraw.congr (Filter.Eventually.of_forall fun z => ?_)
      rw [hgder i z]
      simp only [smul_smul]
      congr 1
      ring
    have hzero : Integrable (fun z : V => baseHeat z • du (p z) (b i)) :=
      hD0int i
    have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (f := baseHeat) (g := fun z : V => du (p z) (b i)) (v := b i)
      hleft hright hzero
      (fun z _ => (baseHeat_hasFDeriv z).differentiableAt)
      (fun z _ => hgdiff i z)
    simp_rw [(baseHeat_hasFDeriv _).fderiv, baseD1Map_apply, hgder i] at hibp
    have hfactor :
        (∫ z : V, baseHeat z • ((-r) • d2u (p z) (b i) (b i))) =
          (-r) • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with z
      simp only [smul_smul]
      congr 1
      ring
    calc
      (∫ z : V, baseD1 (b i) z • du (p z) (b i)) =
          -(∫ z : V, baseHeat z • ((-r) • d2u (p z) (b i) (b i))) := by
        rw [hibp]
        simp
      _ = -((-r) • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i)) := by
        rw [hfactor]
      _ = r • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
        simp
  have hdir : ∀ i : Fin (Module.finrank ℝ V),
      (∫ z : V, r⁻¹ • (baseD1 (b i) z • du (p z) (b i))) =
        ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
    intro i
    rw [integral_smul, hparts i, inv_smul_smul₀ hr.ne']
  have hpoint : ∀ z : V, scaledDt t du x z =
      ∑ i : Fin (Module.finrank ℝ V),
        r⁻¹ • (baseD1 (b i) z • du (p z) (b i)) := by
    intro z
    have hz := b.sum_repr' z
    unfold scaledDt
    change baseHeat z • du (p z) ((-(2 * r)⁻¹) • z) = _
    conv_lhs => rw [← hz]
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    unfold baseD1
    rw [real_inner_comm z (b i)]
    simp only [smul_smul]
    congr 1
    field_simp [hr.ne']
    ring
  have hterm_int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => r⁻¹ • (baseD1 (b i) z • du (p z) (b i))) :=
    fun i => (hD1int i).const_smul r⁻¹
  unfold heatScaled
  change (∫ z : V, scaledDt t du x z) =
    ∫ z : V, baseHeat z • coreLap d2u (p z)
  calc
    (∫ z : V, scaledDt t du x z) =
        ∫ z : V, ∑ i : Fin (Module.finrank ℝ V),
          r⁻¹ • (baseD1 (b i) z • du (p z) (b i)) := by
      apply integral_congr_ae
      filter_upwards with z
      exact hpoint z
    _ = ∑ i : Fin (Module.finrank ℝ V),
          ∫ z : V, r⁻¹ • (baseD1 (b i) z • du (p z) (b i)) := by
      rw [MeasureTheory.integral_finset_sum _ (fun i _ => hterm_int i)]
    _ = ∑ i : Fin (Module.finrank ℝ V),
          ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdir i
    _ = ∫ z : V, ∑ i : Fin (Module.finrank ℝ V),
          baseHeat z • d2u (p z) (b i) (b i) := by
      rw [MeasureTheory.integral_finset_sum _ (fun i _ => hD2int i)]
    _ = ∫ z : V, baseHeat z • coreLap d2u (p z) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [coreLap_apply, b, Finset.smul_sum]

/-- Positive-time heat evolution of a bounded realized `C²` spatial jet
satisfies the Euclidean heat equation pointwise. -/
theorem heatSup_time {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    HasDerivAt (fun s : ℝ => heatSup s u x) (heatSup t (coreLap d2u) x) t := by
  have hscaled := heatScaled_time ht u du hu x
  rw [scaledDt_eq_lap ht du d2u hdu x, ← heatSup_scaled ht] at hscaled
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [Set.Ioi_mem_nhds ht] with s hs
  exact heatSup_scaled hs u x

/-- Fundamental heat-evolution identity on a positive interval.  This is the
zero-endpoint bridge used to recover the Duhamel boundary term. -/
theorem heatSup_primitive {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (hholder : HolderWith K (1 / 2 : ℝ≥0) u) (x : V) :
    (∫ s in (0 : ℝ)..t, heatSup s (coreLap d2u) x) = heatSup t u x - u x := by
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun q : ℝ => heatSup q u x) (heatSup s (coreLap d2u) x) s := by
    intro s hs
    exact heatSup_time hs.1 u du d2u hu hdu x
  have hint : IntervalIntegrable (fun s : ℝ => heatSup s (coreLap d2u) x)
      volume 0 t := by
    have hscaled := (heatScaled_cont (coreLap d2u) x).intervalIntegrable 0 t
    apply hscaled.congr_ae
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [ae_ne (0 : ℝ)] with s hs_ne
    intro hs_mem
    rw [uIoc_of_le ht.le] at hs_mem
    exact (heatSup_scaled hs_mem.1 (coreLap d2u) x).symm
  have hzero := heatSup_zero u hholder x
  have htlim : Tendsto (fun s : ℝ => heatSup s u x) (ᵊ[<] t)
      (ᵊ (heatSup t u x)) :=
    (heatSup_time ht u du d2u hu hdu x).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht hderiv hint hzero htlim

section Duhamel

/-- A Volterra integral whose coefficient vanishes at zero has no moving-
endpoint boundary term.  The proof separates a fixed interval from the
moving sliver; boundedness of the realized derivative makes the latter
quadratic in the time increment. -/
private theorem volterra_zero {t : ℝ}
    (b db : BoundedContinuousFunction ℝ ℝ)
    (hb : ∀ q : ℝ, HasDerivAt (b : ℝ → ℝ) (db q) q)
    (hb0 : b 0 = 0) (k : ℝ → F) (hk : Continuous k)
    (Ck : ℝ) (hk_bound : ∀ r : ℝ, ‖k r‖ ≤ Ck) :
    HasDerivAt
      (fun q : ℝ => ∫ r in (0 : ℝ)..q, b (q - r) • k r)
      (∫ r in (0 : ℝ)..t, db (t - r) • k r) t := by
  let fixed : ℝ → F := fun q =>
    ∫ r in (0 : ℝ)..t, b (q - r) • k r
  let tail : ℝ → F := fun q =>
    ∫ r in t..q, b (q - r) • k r
  let F₀ : ℝ → ℝ → F := fun q r => b (q - r) • k r
  let F₁ : ℝ → ℝ → F := fun q r => db (q - r) • k r
  let bound : ℝ → ℝ := fun _ => ‖db‖ * Ck
  have hfixed : HasDerivAt fixed
      (∫ r in (0 : ℝ)..t, db (t - r) • k r) t := by
    have hs : (Set.univ : Set ℝ) ∈ 𝓝 t := Set.univ_mem
    have hmeas : ∀ᶠ q in 𝓝 t,
        AEStronglyMeasurable (F₀ q)
          (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
      apply Filter.Eventually.of_forall
      intro q
      exact ((b.continuous.comp (continuous_const.sub continuous_id)).smul hk)
        |>.aestronglyMeasurable.restrict
    have hint : IntervalIntegrable (F₀ t) volume 0 t :=
      ((b.continuous.comp (continuous_const.sub continuous_id)).smul hk)
        |>.intervalIntegrable 0 t
    have hder_meas : AEStronglyMeasurable (F₁ t)
        (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
      ((db.continuous.comp (continuous_const.sub continuous_id)).smul hk)
        |>.aestronglyMeasurable.restrict
    have hbound : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.uIoc (0 : ℝ) t →
        ∀ q ∈ Set.univ, ‖F₁ q r‖ ≤ bound r := by
      apply Filter.Eventually.of_forall
      intro r hr q hq
      dsimp only [F₁, bound]
      rw [norm_smul]
      exact mul_le_mul (db.norm_coe_le_norm (q - r)) (hk_bound r)
        (norm_nonneg _) (norm_nonneg _)
    have hbound_int : IntervalIntegrable bound volume 0 t := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hdiff : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.uIoc (0 : ℝ) t →
        ∀ q ∈ Set.univ, HasDerivAt (F₀ · r) (F₁ q r) q := by
      apply Filter.Eventually.of_forall
      intro r hr q hq
      have harg : HasDerivAt (fun s : ℝ => s - r) 1 q := by
        simpa using (hasDerivAt_id q).sub_const r
      have hcomp := (hb (q - r)).comp q harg
      dsimp only [F₀, F₁]
      exact hcomp.smul_const (k r)
    have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F₀) (F' := F₁) (bound := bound) hs hmeas hint hder_meas
        hbound hbound_int hdiff
    simpa only [fixed, F₀, F₁] using key.2
  have hb_lip : ∀ q r : ℝ, ‖b (q - r)‖ ≤ ‖db‖ * |q - r| := by
    intro q r
    calc
      ‖b (q - r)‖ = ‖b (q - r) - b 0‖ := by rw [hb0, sub_zero]
      _ ≤ ‖db‖ * ‖(q - r) - 0‖ := by
        exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := (b : ℝ → ℝ)) (f' := fun s => db s)
          (s := Set.univ)
          (fun s hs => (hb s).hasDerivWithinAt)
          (fun s hs => db.norm_coe_le_norm s) convex_univ
          (Set.mem_univ 0) (Set.mem_univ (q - r))
      _ = ‖db‖ * |q - r| := by simp [Real.norm_eq_abs]
  have htail_bound : ∀ q : ℝ,
      ‖tail q‖ ≤ (‖db‖ * Ck) * ‖q - t‖ ^ 2 := by
    intro q
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := q)
      (C := (‖db‖ * Ck) * |q - t|)
      (f := fun r : ℝ => b (q - r) • k r) (fun r hr => by
        have hr' : r ∈ Set.uIcc t q := Set.uIoc_subset_uIcc hr
        have hdist : |q - r| ≤ |q - t| :=
          abs_sub_right_of_mem_uIcc hr'
        rw [norm_smul]
        calc
          ‖b (q - r)‖ * ‖k r‖ ≤
              (‖db‖ * |q - r|) * Ck := by
            exact mul_le_mul (hb_lip q r) (hk_bound r)
              (norm_nonneg _) (mul_nonneg (norm_nonneg _) (abs_nonneg _))
          _ ≤ (‖db‖ * |q - t|) * Ck := by
            gcongr
          _ = (‖db‖ * Ck) * |q - t| := by ring)
    dsimp only [tail]
    calc
      ‖∫ r in t..q, b (q - r) • k r‖ ≤
          ((‖db‖ * Ck) * |q - t|) * |q - t| := hraw
      _ = (‖db‖ * Ck) * ‖q - t‖ ^ 2 := by
        rw [Real.norm_eq_abs]
        ring
  have htail_big : tail =O[𝓝 t] (fun q : ℝ => ‖q - t‖ ^ 2) := by
    apply isBigO_iff.2
    refine ⟨‖db‖ * Ck, ?_⟩
    filter_upwards with q
    simpa only [Real.norm_eq_abs, abs_pow,
      abs_of_nonneg (norm_nonneg (q - t))] using htail_bound q
  have htail_der : HasDerivAt tail 0 t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    simpa using htail_big.hasFDerivAt (by norm_num : 1 < (2 : ℕ))
  have hsplit :
      (fun q : ℝ => ∫ r in (0 : ℝ)..q, b (q - r) • k r) =
        fun q => fixed q + tail q := by
    funext q
    symmetry
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact ((b.continuous.comp (continuous_const.sub continuous_id)).smul hk)
        |>.intervalIntegrable 0 t
    · exact ((b.continuous.comp (continuous_const.sub continuous_id)).smul hk)
        |>.intervalIntegrable t q
  rw [hsplit]
  exact hfixed.add htail_der

/-- Leibniz rule for a bounded `C¹` Volterra coefficient and a bounded
continuous Banach-valued path. -/
private theorem volterra_time {t : ℝ}
    (b db : BoundedContinuousFunction ℝ ℝ)
    (hb : ∀ q : ℝ, HasDerivAt (b : ℝ → ℝ) (db q) q)
    (k : ℝ → F) (hk : Continuous k)
    (Ck : ℝ) (hk_bound : ∀ r : ℝ, ‖k r‖ ≤ Ck) :
    HasDerivAt
      (fun q : ℝ => ∫ r in (0 : ℝ)..q, b (q - r) • k r)
      (b 0 • k t + ∫ r in (0 : ℝ)..t, db (t - r) • k r) t := by
  let bz : BoundedContinuousFunction ℝ ℝ :=
    b - BoundedContinuousFunction.const ℝ (b 0)
  have hbz : ∀ q : ℝ, HasDerivAt (bz : ℝ → ℝ) (db q) q := by
    intro q
    simpa only [bz, BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.const_apply, Pi.sub_apply] using
      (hb q).sub_const (b 0)
  have hbz0 : bz 0 = 0 := by simp [bz]
  have hz := volterra_zero bz db hbz hbz0 k hk Ck hk_bound
  have hc : HasDerivAt
      (fun q : ℝ => ∫ r in (0 : ℝ)..q, b 0 • k r) (b 0 • k t) t :=
    (hk.smul_const (b 0)).integral_hasStrictDerivAt 0 t |>.hasDerivAt
  have hsplit :
      (fun q : ℝ => ∫ r in (0 : ℝ)..q, b (q - r) • k r) =
        fun q => (∫ r in (0 : ℝ)..q, b 0 • k r) +
          ∫ r in (0 : ℝ)..q, bz (q - r) • k r := by
    funext q
    rw [← intervalIntegral.integral_add
      ((hk.smul_const (b 0)).intervalIntegrable 0 q)
      (((bz.continuous.comp (continuous_const.sub continuous_id)).smul hk)
        |>.intervalIntegrable 0 q)]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only [bz]
    simp only [BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.const_apply, Pi.sub_apply]
    rw [add_smul, sub_add_cancel]
  rw [hsplit]
  simpa only [add_assoc] using hc.add hz

/-- Time-reversed simple-tensor Duhamel evolution.  Reversal keeps the heat
parameter fixed while the scalar coefficient is differentiated. -/
def frozenDuh (t : ℝ) (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ r in (0 : ℝ)..t, a (t - r) • heatScaled r u x

@[simp]
theorem frozenDuh_zero (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction V F) (x : V) :
    frozenDuh 0 a u x = 0 := by
  simp [frozenDuh]

/-- The spatial first jet of the simple-tensor Duhamel evolution is the
Duhamel evolution of the supplied realized first jet. -/
theorem frozenDuh_space (t : ℝ) (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    HasFDerivAt (fun y : V => frozenDuh t a u y)
      (frozenDuh t a du x) x := by
  let F₀ : V → ℝ → F := fun y r =>
    a (t - r) • heatScaled r u y
  let F₁ : V → ℝ → (V →L[ℝ] F) := fun y r =>
    a (t - r) • heatScaled r du y
  let bound : ℝ → ℝ := fun r => |a (t - r)| * ‖du‖
  have hs : (Set.univ : Set V) ∈ 𝓝 x := Set.univ_mem
  have hmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (F₀ y)
        (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    apply Filter.Eventually.of_forall
    intro y
    exact ((a.continuous.comp (continuous_const.sub continuous_id)).smul
      (heatScaled_cont u y)).aestronglyMeasurable.restrict
  have hint : IntervalIntegrable (F₀ x) volume 0 t :=
    ((a.continuous.comp (continuous_const.sub continuous_id)).smul
      (heatScaled_cont u x)).intervalIntegrable 0 t
  have hder_meas : AEStronglyMeasurable (F₁ x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ((a.continuous.comp (continuous_const.sub continuous_id)).smul
      (heatScaled_cont du x)).aestronglyMeasurable.restrict
  have hbound : ∀ᵐ r ∂(volume.restrict (Set.uIoc (0 : ℝ) t)),
      ∀ y ∈ Set.univ, ‖F₁ y r‖ ≤ bound r := by
    apply Filter.Eventually.of_forall
    intro r y hy
    dsimp only [F₁, bound]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (heatScaled_norm r du y) (abs_nonneg _)
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    apply Continuous.intervalIntegrable
    dsimp only [bound]
    fun_prop
  have hdiff : ∀ᵐ r ∂(volume.restrict (Set.uIoc (0 : ℝ) t)),
      ∀ y ∈ Set.univ, HasFDerivAt (F₀ · r) (F₁ y r) y := by
    apply Filter.Eventually.of_forall
    intro r y hy
    dsimp only [F₀, F₁]
    exact (heatScaled_space r u du hu y).const_smul (a (t - r))
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := F₀) (F' := F₁) (bound := bound) hs hmeas hint hder_meas
      hbound hbound_int hdiff
  simpa only [F₀, F₁, frozenDuh] using key

/-- Continuous linear maps commute with the simple-tensor Duhamel formula. -/
theorem frozenDuh_map {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) (t : ℝ) (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction V F) (x : V) :
    L (frozenDuh t a u x) =
      frozenDuh t a (L.compLeftContinuousBounded V u) x := by
  have hint : IntervalIntegrable
      (fun r : ℝ => a (t - r) • heatScaled r u x) volume 0 t :=
    ((a.continuous.comp (continuous_const.sub continuous_id)).smul
      (heatScaled_cont u x)).intervalIntegrable 0 t
  unfold frozenDuh
  rw [← L.intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [map_smul, heatScaled_map]

/-- Tracing the realized Duhamel Hessian is Duhamel evolution of the traced
spatial Hessian. -/
theorem frozenDuh_lap (t : ℝ) (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) (x : V) :
    lapEval (frozenDuh t a d2u x) =
      frozenDuh t a (coreLap d2u) x := by
  simpa only [coreLap] using
    frozenDuh_map (lapEval (V := V) (F := F)) t a d2u x

/-- Time derivative of the simple-tensor Duhamel evolution.  The coefficient
Leibniz formula is converted to the heat form by one interval integration by
parts, using the already proved positive-time heat equation. -/
theorem frozenDuh_time {t : ℝ} (ht : 0 < t)
    (a da : BoundedContinuousFunction ℝ ℝ)
    (ha : ∀ q : ℝ, HasDerivAt (a : ℝ → ℝ) (da q) q)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    HasDerivAt (fun q : ℝ => frozenDuh q a u x)
      (a t • u x + frozenDuh t a (coreLap d2u) x) t := by
  have hraw := volterra_time a da ha
    (fun r : ℝ => heatScaled r u x) (heatScaled_cont u x) ‖u‖
      (fun r => heatScaled_norm r u x)
  let g : ℝ → F := fun r => a (t - r) • heatScaled r u x
  let gp : ℝ → F := fun r =>
    a (t - r) • heatScaled r (coreLap d2u) x -
      da (t - r) • heatScaled r u x
  have hg_cont : Continuous g := by
    dsimp only [g]
    exact (a.continuous.comp (continuous_const.sub continuous_id)).smul
      (heatScaled_cont u x)
  have hgp_cont : Continuous gp := by
    dsimp only [gp]
    exact ((a.continuous.comp (continuous_const.sub continuous_id)).smul
      (heatScaled_cont (coreLap d2u) x)).sub
        ((da.continuous.comp (continuous_const.sub continuous_id)).smul
          (heatScaled_cont u x))
  have hg_der : ∀ r ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt g (gp r) r := by
    intro r hr
    have harg : HasDerivAt (fun s : ℝ => t - s) (-1) r := by
      convert (hasDerivAt_const r t).sub (hasDerivAt_id r) using 1 <;> ring
    have harev : HasDerivAt (fun s : ℝ => a (t - s)) (-da (t - r)) r := by
      convert (ha (t - r)).comp r harg using 1 <;> ring
    have hheat := heatScaled_time hr.1 u du hu x
    rw [scaledDt_eq_lap hr.1 du d2u hdu x] at hheat
    dsimp only [g, gp]
    convert harev.smul hheat using 1 <;> simp [sub_eq_add_neg, add_comm]
  have hftc : (∫ r in (0 : ℝ)..t, gp r) = g t - g 0 := by
    have hzero : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htlim : Tendsto g (𝓝[<] t) (𝓝 (g t)) :=
      hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      ht hg_der (hgp_cont.intervalIntegrable 0 t) hzero htlim
  have hsplit : (∫ r in (0 : ℝ)..t, gp r) =
      (∫ r in (0 : ℝ)..t,
        a (t - r) • heatScaled r (coreLap d2u) x) -
      ∫ r in (0 : ℝ)..t, da (t - r) • heatScaled r u x := by
    dsimp only [gp]
    rw [intervalIntegral.integral_sub]
    · exact ((a.continuous.comp (continuous_const.sub continuous_id)).smul
        (heatScaled_cont (coreLap d2u) x)).intervalIntegrable 0 t
    · exact ((da.continuous.comp (continuous_const.sub continuous_id)).smul
        (heatScaled_cont u x)).intervalIntegrable 0 t
  rw [hsplit] at hftc
  dsimp only [g] at hftc
  rw [heatScaled_zero] at hftc
  have hcoef :
      a 0 • heatScaled t u x +
          (∫ r in (0 : ℝ)..t, da (t - r) • heatScaled r u x) =
        a t • u x +
          ∫ r in (0 : ℝ)..t,
            a (t - r) • heatScaled r (coreLap d2u) x := by
    abel
  unfold frozenDuh
  convert hraw using 1
  exact hcoef

/-- Complete isotropic zero-trace Duhamel PDE producer.  The two spatial
statements realize the Hessian jet used in the PDE derivative. -/
theorem frozenDuh_pde {t : ℝ} (ht : 0 < t)
    (a da : BoundedContinuousFunction ℝ ℝ)
    (ha : ∀ q : ℝ, HasDerivAt (a : ℝ → ℝ) (da q) q)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    HasFDerivAt (fun y : V => frozenDuh t a u y)
        (frozenDuh t a du x) x ∧
      HasFDerivAt (fun y : V => frozenDuh t a du y)
        (frozenDuh t a d2u x) x ∧
      HasDerivAt (fun q : ℝ => frozenDuh q a u x)
        (lapEval (frozenDuh t a d2u x) + a t • u x) t := by
  refine ⟨frozenDuh_space t a u du hu x,
    frozenDuh_space t a du d2u hdu x, ?_⟩
  rw [frozenDuh_lap, add_comm]
  exact frozenDuh_time ht a da ha u du d2u hu hdu x

end Duhamel

end ScaledEvolution

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
