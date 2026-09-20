import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts
import DifferentialGeometry.Analysis.Convex.Convolution
import DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import DifferentialGeometry.Analysis.Integration.Integral.Convergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Convolution

private theorem integral_hessian_apply_le_of_integral_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {φ : E → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {V : E → E} (hV : Continuous V)
    {K : E → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (hidentity : ∀ g : E → ℝ, ContDiff ℝ 2 g →
      (∫ x, fderiv ℝ (fderiv ℝ g) x (V x) (V x) * φ x ∂μ) = ∫ x, g x * K x ∂μ) :
    Integrable (fun x => B x (V x) (V x) * φ x) μ ∧
      (∫ x, B x (V x) (V x) * φ x ∂μ) ≤ ∫ x, u x * K x ∂μ := by
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  let χ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let κ := χ.normed μ
  have hκd : ContDiff ℝ 2 κ := χ.contDiff_normed
  have hκc : HasCompactSupport κ := χ.hasCompactSupport_normed
  have hκ0 : ∀ x, 0 ≤ κ x := χ.nonneg_normed
  have hκm : ∫ x, κ x ∂μ = 1 := χ.integral_normed
  let k : ℝ → E → ℝ := fun r z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)
  let g : ℝ → E → ℝ := fun r => k r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u
  have hkd (r : ℝ) : ContDiff ℝ 2 (k r) :=
    contDiff_const.mul (hκd.comp (contDiff_const.smul contDiff_id))
  have hkc {r : ℝ} (hr : 0 < r) : HasCompactSupport (k r) := by
    have h : HasCompactSupport (fun z : E => κ (r⁻¹ • z)) :=
      hκc.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr.ne')).unit)
    exact h.mul_left
  have hkm {r : ℝ} (hr : 0 < r) : ∫ x, k r x ∂μ = 1 := by
    dsimp only [k]
    rw [integral_const_mul, μ.integral_comp_inv_smul_of_nonneg κ hr.le, hκm]
    simp only [smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]
  have hg {r : ℝ} (hr : 0 < r) : ContDiff ℝ 2 (g r) :=
    (hkc hr).contDiff_convolution_left _ (hkd r) huc.locallyIntegrable
  have hlow {r : ℝ} (hr : 0 < r) (x : E) :
      -A (V x) (V x) ≤ fderiv ℝ (fderiv ℝ (g r)) x (V x) (V x) := by
    have hk0 : ∀ᵐ z ∂μ, 0 ≤ k r z := ae_of_all μ fun z =>
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (hκ0 _)
    have h := hu.fderiv_fderiv_convolution_left_lower_bound A hA hk0
      ((hkd r).continuous.integrable_of_hasCompactSupport (hkc hr))
      (hkd r) (hkc hr) huc.locallyIntegrable x (V x)
    simpa only [hkm hr, neg_one_mul] using h
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hr⟩
  have huni := DifferentialGeometry.Analysis.tendstoLocallyUniformly_convolution_rescale
    (μ := μ) hκ0 (hκc.isCompact.isBounded.subset (subset_tsupport κ)) hκm huc
  have hKuni : TendstoUniformlyOn g u (𝓝[>] (0 : ℝ)) (Function.support K) :=
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKc.isCompact).mp
      huni.tendstoLocallyUniformlyOn).mono (subset_tsupport K)
  have hgi : ∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable (fun x => K x • g t x) μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hK.smul (hg ht).continuous).integrable_of_hasCompactSupport hKc.smul_right
  have hui : Integrable (fun x => K x • u x) μ :=
    (hK.smul huc).integrable_of_hasCompactSupport hKc.smul_right
  have hI := hKuni.integral_smul (hK.integrable_of_hasCompactSupport hKc) hgi hui
  have hIBP (n : ℕ) : (∫ x, fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x ∂μ) =
      ∫ x, g (r n) x * K x ∂μ := hidentity _ (hg (hr n))
  have hint : Tendsto (fun n => ∫ x, fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x ∂μ)
      atTop (𝓝 (∫ x, u x * K x ∂μ)) := by
    simp_rw [hIBP]
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hI.comp hrt
  have hFi (n : ℕ) : Integrable (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x) μ := by
    have hc : Continuous (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x)) :=
      ((((hg (hr n)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
        hV).clm_apply hV
    exact (hc.mul hφ).integrable_of_hasCompactSupport hφc.mul_left
  have hlower : Integrable (fun x => -A (V x) (V x) * φ x) μ := by
    have hc : Continuous (fun x => -A (V x) (V x) * φ x) := by fun_prop
    exact hc.integrable_of_hasCompactSupport hφc.mul_left
  have hbound (n : ℕ) : (fun x => -A (V x) (V x) * φ x) ≤ᵐ[μ]
      (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x) :=
    ae_of_all μ fun x => mul_le_mul_of_nonneg_right (hlow (hr n) x) (hφ0 x)
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x)
      atTop (𝓝 (B x (V x) (V x) * φ x)) := by
    filter_upwards [hB] with x hx
    obtain ⟨hsym, p, hp⟩ := hx
    have ht := DifferentialGeometry.Analysis.tendsto_fderiv_fderiv_convolution_rescale_of_isLittleO
      hκd hκc hκm huc.locallyIntegrable hsym hp
    have heval : Continuous (fun D : E →L[ℝ] E →L[ℝ] ℝ => D (V x) (V x)) := by fun_prop
    exact ((heval.tendsto (B x)).comp (ht.comp hrt)).mul_const _
  exact MeasureTheory.integrable_and_integral_le_of_tendsto_ae hFi hlower hbound hlim hint

theorem ConvexOn.integral_hessian_vector_field_le
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (b : Module.Basis ι ℝ E) {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {V : E → E} (hV : ContDiff ℝ 2 V) :
    Integrable (fun x => B x (V x) (V x) * φ x) μ ∧
      (∫ x, B x (V x) (V x) * φ x ∂μ) ≤
        ∑ i, ∑ j, ∫ x, u x * fderiv ℝ
          (fderiv ℝ (fun y => b.repr (V y) i * b.repr (V y) j * φ y)) x (b j) (b i) ∂μ := by
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  let ψ (i j : ι) : E → ℝ := fun x => b.repr (V x) i * b.repr (V x) j * φ x
  have hψ (i j : ι) : ContDiff ℝ 2 (ψ i j) :=
    (((b.coord i).toContinuousLinearMap.contDiff.comp hV).mul
      ((b.coord j).toContinuousLinearMap.contDiff.comp hV)).mul hφ
  have hψc (i j : ι) : HasCompactSupport (ψ i j) := hφc.mul_left
  let D (i j : ι) : E → ℝ := fun x => fderiv ℝ (fderiv ℝ (ψ i j)) x (b j) (b i)
  have hD (i j : ι) : Continuous (D i j) :=
    ((((hψ i j).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hDc (i j : ι) : HasCompactSupport (D i j) :=
    (((hψc i j).fderiv ℝ).fderiv_apply ℝ (b j)).comp_left
      (g := fun C : E →L[ℝ] ℝ => C (b i)) rfl
  let K : E → ℝ := fun x => ∑ i, ∑ j, D i j x
  have hK : Continuous K := continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => hD i j
  have hKc : HasCompactSupport K := by
    have h : HasCompactSupport (∑ i, ∑ j, D i j) :=
      HasCompactSupport.finset_sum (fun i _ =>
        HasCompactSupport.finset_sum (fun j _ => hDc i j))
    convert h using 1
    funext x
    simp only [K, Finset.sum_apply]
  have hsum (f : E → ℝ) (hf : Continuous f) : (∫ x, f x * K x ∂μ) =
      ∑ i, ∑ j, ∫ x, f x * D i j x ∂μ := by
    have hi (i j : ι) : Integrable (fun x => f x * D i j x) μ :=
      (hf.mul (hD i j)).integrable_of_hasCompactSupport (hDc i j).mul_left
    simp only [K, Finset.mul_sum]
    rw [integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
    exact Finset.sum_congr rfl (fun i _ => integral_finsetSum Finset.univ (fun j _ => hi i j))
  obtain ⟨hi, hle⟩ := integral_hessian_apply_le_of_integral_identity A hA hu hB
    hφ.continuous hφc hφ0 hV.continuous hK hKc (fun f hf => by
      rw [hsum f hf.continuous]
      have h := DifferentialGeometry.Analysis.integral_fderiv_fderiv_apply_mul_eq
        (μ := μ) b isOpen_univ (hf.differentiable (by norm_num)).differentiableOn
        (hf.fderiv_right (m := 1) (by norm_num)).locallyLipschitz.locallyLipschitzOn
        hV.contDiffOn hV.contDiffOn hφ hφc (subset_univ _)
      simpa only [Measure.restrict_univ] using h)
  exact ⟨hi, hle.trans_eq (hsum u huc)⟩

theorem ConvexOn.integral_hessian_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (v : E) :
    Integrable (fun x => B x v v * φ x) μ ∧
      (∫ x, B x v v * φ x ∂μ) ≤ ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v v ∂μ := by
  let b := Module.finBasis ℝ E
  obtain ⟨hi, hle⟩ := hu.integral_hessian_vector_field_le b A hA hB hφ hφc hφ0
    (V := fun _ => v) contDiff_const
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  have hcoeff (i j : Fin (Module.finrank ℝ E)) (x : E) :
      fderiv ℝ (fderiv ℝ (fun y => b.repr v i * b.repr v j * φ y)) x (b j) (b i) =
        b.repr v i * b.repr v j * fderiv ℝ (fderiv ℝ φ) x (b j) (b i) := by
    change fderiv ℝ (fderiv ℝ ((b.repr v i * b.repr v j) • φ)) x (b j) (b i) = _
    rw [fderiv_const_smul_field, fderiv_const_smul_field]
    rfl
  simp_rw [hcoeff] at hle
  have hDi (i j : Fin (Module.finrank ℝ E)) :
      Integrable (fun x => u x * (b.repr v i * b.repr v j *
        fderiv ℝ (fderiv ℝ φ) x (b j) (b i))) μ := by
    have hc : Continuous (fun x => u x * (b.repr v i * b.repr v j *
        fderiv ℝ (fderiv ℝ φ) x (b j) (b i))) := by
      exact huc.mul (continuous_const.mul
        ((((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).clm_apply continuous_const))
    have hs : HasCompactSupport (fun x => fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) :=
      ((hφc.fderiv ℝ).fderiv_apply ℝ (b j)).comp_left
        (g := fun C : E →L[ℝ] ℝ => C (b i)) rfl
    exact hc.integrable_of_hasCompactSupport hs.mul_left.mul_left
  have hexp (x : E) : (∑ i, ∑ j, b.repr v i * b.repr v j *
      fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) = fderiv ℝ (fderiv ℝ φ) x v v := by
    conv_rhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq : (∑ i, ∑ j, ∫ x, u x * (b.repr v i * b.repr v j *
      fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) ∂μ) =
      ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v v ∂μ := by
    have hinner (i : Fin (Module.finrank ℝ E)) :
        (∑ j, ∫ x, u x * (b.repr v i * b.repr v j *
          fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) ∂μ) =
        ∫ x, ∑ j, u x * (b.repr v i * b.repr v j *
          fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) ∂μ :=
      (integral_finsetSum Finset.univ (fun j _ => hDi i j)).symm
    simp_rw [hinner]
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hDi i j))]
    apply integral_congr_ae
    filter_upwards with x
    simpa only [Finset.mul_sum] using congrArg (fun z : ℝ => u x * z) (hexp x)
  exact ⟨hi, hle.trans_eq heq⟩
