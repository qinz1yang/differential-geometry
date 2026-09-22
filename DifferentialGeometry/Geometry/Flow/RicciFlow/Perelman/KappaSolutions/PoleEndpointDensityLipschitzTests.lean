import DifferentialGeometry.Analysis.Parabolic.WeakEquation.LipschitzTests
import DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiTimeChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTimeChartRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineGradientCoefficients
import DifferentialGeometry.Analysis.Calculus.Derivative.WeakIdentification
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import DifferentialGeometry.Analysis.Integration.Lp.BoundedLinearPairing
import DifferentialGeometry.Analysis.Calculus.GaussianNormalizationDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineVolumeDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Analysis.Integration.Integral.WeightedTimeDerivative
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.ExponentialTransform



noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeCovectorNormedAddCommGroup : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeCovectorNormedSpace : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance projectionNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance projectionNormedSpace :
    NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeDualNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeDualNormedSpace : NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem weak_log_coefficients_measurable_bounded_on_compacts
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (rho R q : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hrho : ContinuousOn rho Ω) (hR : ContinuousOn R Ω) (hq : ContinuousOn q Ω)
    (hB : ContinuousOn B Ω)
    (π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (μ : Measure (ℝ × E)) :
    let d := fun z => π (fderiv ℝ f z)
    let b := fun z => rho z • ((B z (d z)).comp π)
    let c := fun z => rho z *
      ((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z)
    (∀ v, AEStronglyMeasurable (fun z => b z v) (μ.restrict Ω)) ∧
      AEStronglyMeasurable c (μ.restrict Ω) ∧
      ∀ K : Set (ℝ × E), IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
        (∀ᵐ z ∂μ.restrict K, ‖b z‖ ≤ M) ∧
        (∀ᵐ z ∂μ.restrict K, ‖c z‖ ≤ N) := by
  let d := fun z => π (fderiv ℝ f z)
  let b := fun z => rho z • ((B z (d z)).comp π)
  let c := fun z => rho z *
    ((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z)
  change (∀ v, AEStronglyMeasurable (fun z => b z v) (μ.restrict Ω)) ∧
    AEStronglyMeasurable c (μ.restrict Ω) ∧
    ∀ K : Set (ℝ × E), IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
      (∀ᵐ z ∂μ.restrict K, ‖b z‖ ≤ M) ∧
      (∀ᵐ z ∂μ.restrict K, ‖c z‖ ≤ N)
  have hdm : AEStronglyMeasurable d (μ.restrict Ω) :=
    π.continuous.comp_aestronglyMeasurable (measurable_fderiv ℝ f).aestronglyMeasurable
  have hrhom : AEStronglyMeasurable rho (μ.restrict Ω) :=
    hrho.aestronglyMeasurable hΩ.measurableSet
  have hRm : AEStronglyMeasurable R (μ.restrict Ω) :=
    hR.aestronglyMeasurable hΩ.measurableSet
  have hqm : AEStronglyMeasurable q (μ.restrict Ω) :=
    hq.aestronglyMeasurable hΩ.measurableSet
  have hBm : AEStronglyMeasurable B (μ.restrict Ω) :=
    hB.aestronglyMeasurable hΩ.measurableSet
  have hBdm : AEStronglyMeasurable (fun z => B z (d z)) (μ.restrict Ω) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E →L[ℝ] ℝ)
      (F := (E →L[ℝ] ℝ) →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable
        (hBm.prodMk hdm)
  have hQm : AEStronglyMeasurable (fun z => B z (d z) (d z)) (μ.restrict Ω) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E →L[ℝ] ℝ)
      (F := ℝ)).continuous.comp_aestronglyMeasurable (hBdm.prodMk hdm)
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact (hrhom.mul (hBdm.apply_continuousLinearMap (π v))).congr
      (Eventually.of_forall fun z => by
        simp only [b, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Pi.mul_apply])
  · exact hrhom.mul (((hQm.const_mul (1 / 2 : ℝ)).sub (hRm.const_mul (1 / 2 : ℝ))).add hqm)
  · intro K hK hKΩ
    obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
    obtain ⟨C, hLip⟩ := (hf.mono hLΩ).exists_lipschitzOnWith_of_compact hL
    have hderiv (z : ℝ × E) (hz : z ∈ K) : ‖fderiv ℝ f z‖ ≤ (C : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (mem_interior_iff_mem_nhds.mp (hKL hz)) hLip
    let D : ℝ := ‖π‖ * (C : ℝ)
    have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) C.coe_nonneg
    have hd (z : ℝ × E) (hz : z ∈ K) : ‖d z‖ ≤ D :=
      π.le_opNorm_of_le (hderiv z hz)
    have hcoeff : ContinuousOn
        (fun z => ‖rho z‖ + ‖B z‖ + ‖R z‖ + ‖q z‖) K :=
      ((((hrho.mono hKΩ).norm.add (hB.mono hKΩ).norm).add
        (hR.mono hKΩ).norm).add (hq.mono hKΩ).norm)
    obtain ⟨A₀, hA₀⟩ := hK.exists_bound_of_continuousOn hcoeff
    let A : ℝ := max A₀ 0
    have hA : 0 ≤ A := le_max_right _ _
    have hbounds (z : ℝ × E) (hz : z ∈ K) :
        ‖rho z‖ ≤ A ∧ ‖B z‖ ≤ A ∧ ‖R z‖ ≤ A ∧ ‖q z‖ ≤ A := by
      have hsum : ‖‖rho z‖ + ‖B z‖ + ‖R z‖ + ‖q z‖‖ ≤ A :=
        (hA₀ z hz).trans (le_max_left A₀ 0)
      have hnonneg : 0 ≤ ‖rho z‖ + ‖B z‖ + ‖R z‖ + ‖q z‖ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hsum
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        linarith only [hsum, norm_nonneg (rho z), norm_nonneg (B z),
          norm_nonneg (R z), norm_nonneg (q z)]
    have hBd (z : ℝ × E) (hz : z ∈ K) : ‖B z (d z)‖ ≤ A * D := by
      calc
        ‖B z (d z)‖ ≤ ‖B z‖ * ‖d z‖ := (B z).le_opNorm (d z)
        _ ≤ A * D := mul_le_mul (hbounds z hz).2.1 (hd z hz) (norm_nonneg _) hA
    have hQ (z : ℝ × E) (hz : z ∈ K) : ‖B z (d z) (d z)‖ ≤ A * D * D := by
      calc
        ‖B z (d z) (d z)‖ ≤ ‖B z (d z)‖ * ‖d z‖ :=
          (B z (d z)).le_opNorm (d z)
        _ ≤ A * D * D := mul_le_mul (hBd z hz) (hd z hz)
          (norm_nonneg _) (mul_nonneg hA hD)
    refine ⟨A * (A * D * ‖π‖), A * ((1 / 2 : ℝ) * (A * D * D) +
      (1 / 2 : ℝ) * A + A), ?_, ?_⟩
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hcomp : ‖(B z (d z)).comp π‖ ≤ A * D * ‖π‖ :=
        ((B z (d z)).opNorm_comp_le π).trans
          (mul_le_mul_of_nonneg_right (hBd z hz) (norm_nonneg _))
      change ‖rho z • ((B z (d z)).comp π)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul (hbounds z hz).1 hcomp (norm_nonneg _) hA
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hscalar :
          ‖(1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z‖ ≤
            (1 / 2 : ℝ) * (A * D * D) + (1 / 2 : ℝ) * A + A := by
        calc
          ‖(1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z‖ ≤
              ‖(1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z‖ + ‖q z‖ :=
            norm_add_le _ _
          _ ≤ (‖(1 / 2 : ℝ) * B z (d z) (d z)‖ +
              ‖(1 / 2 : ℝ) * R z‖) + ‖q z‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
          _ = (1 / 2 : ℝ) * ‖B z (d z) (d z)‖ +
              (1 / 2 : ℝ) * ‖R z‖ + ‖q z‖ := by norm_num [norm_mul]
          _ ≤ (1 / 2 : ℝ) * (A * D * D) + (1 / 2 : ℝ) * A + A :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left (hQ z hz) (by norm_num))
                (mul_le_mul_of_nonneg_left (hbounds z hz).2.2.1 (by norm_num)))
              (hbounds z hz).2.2.2
      change ‖rho z * ((1 / 2 : ℝ) * B z (d z) (d z) -
        (1 / 2 : ℝ) * R z + q z)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hbounds z hz).1 hscalar (norm_nonneg _) hA

private theorem integrable_and_integral_weak_log_nonneg_of_smooth_tests
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (rho R q : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hrho : ContinuousOn rho Ω) (hR : ContinuousOn R Ω) (hq : ContinuousOn q Ω)
    (hB : ContinuousOn B Ω)
    (π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (μ : Measure (ℝ × E)) {d : ℕ}
    (e : (ℝ × E) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (he : MeasurePreserving e μ volume)
    (hweak : ∀ ψ : (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∀ z, 0 ≤ ψ z) →
      let df := fun z => π (fderiv ℝ f z)
      0 ≤ ∫ z, rho z *
        (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
          B z (df z) (π (fderiv ℝ ψ z))) ∂μ)
    {ψ : (ℝ × E) → ℝ} (hψ : LocallyLipschitzOn Ω ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω) (hψn : ∀ z, 0 ≤ ψ z) :
    let df := fun z => π (fderiv ℝ f z)
    Integrable (fun z => rho z *
      (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
        B z (df z) (π (fderiv ℝ ψ z)))) μ ∧
    0 ≤ ∫ z, rho z *
      (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
        B z (df z) (π (fderiv ℝ ψ z))) ∂μ := by
  let df := fun z => π (fderiv ℝ f z)
  let b := fun z => rho z • ((B z (df z)).comp π)
  let c := fun z => rho z *
    ((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z)
  obtain ⟨hbm, hcm, hbound⟩ := weak_log_coefficients_measurable_bounded_on_compacts
    hΩ hf rho R q B hrho hR hq hB π μ
  have hidentity (v : (ℝ × E) → ℝ) (z : ℝ × E) :
      b z (fderiv ℝ v z) + c z * v z = rho z *
        (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * v z +
          B z (df z) (π (fderiv ℝ v z))) := by
    simp only [b, c, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    ring
  have hv : ∀ v : (ℝ × E) → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Ω → (∀ z, 0 ≤ v z) →
        0 ≤ ∫ z, b z (fderiv ℝ v z) + c z * v z ∂μ := by
    intro v hv hvc hvs hvn
    simpa only [hidentity] using hweak v hv hvc hvs hvn
  have h := integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving
    e he hΩ b c hbm hcm hbound hv hψ hψc hψs hψn
  simpa only [hidentity] using h

private theorem ae_weak_log_joint_eq_slice
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω) {f ψ : (ℝ × E) → ℝ}
    (hf : LocallyLipschitzOn Ω f) (hψ : LocallyLipschitzOn Ω ψ)
    (hψs : tsupport ψ ⊆ Ω) (rho R q : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :
    let dj := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E)
    let ds := fun z : ℝ × E => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    (fun z => rho z *
      (((1 / 2 : ℝ) * B z (dj z) (dj z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
        B z (dj z) ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ ℝ E))))
      =ᵐ[(volume : Measure ℝ).prod μ]
    (fun z => rho z *
      (((1 / 2 : ℝ) * B z (ds z) (ds z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
        B z (ds z) (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2))) := by
  have hspace {g : ℝ × E → ℝ} {z : ℝ × E} (hg : DifferentiableAt ℝ g z) :
      fderiv ℝ (fun y : E => g (z.1, y)) z.2 =
        (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (hg.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  filter_upwards [hf.ae_differentiableAt_of_isOpen
    (μ := (volume : Measure ℝ).prod μ) hΩ,
    hψ.ae_differentiableAt_of_isOpen (μ := (volume : Measure ℝ).prod μ) hΩ] with z hdf hdψ
  by_cases hz : z ∈ Ω
  · rw [hspace (hdf hz), hspace (hdψ hz)]
  · have hn : z ∉ tsupport ψ := fun h => hz (hψs h)
    have hnx : z.2 ∉ tsupport (fun y : E => ψ (z.1, y)) := by
      intro hy
      apply hn
      exact tsupport_comp_subset_preimage (f := fun y : E => (z.1, y)) ψ
        (continuous_const.prodMk continuous_id) hy
    simp only [image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn,
      fderiv_of_notMem_tsupport ℝ hnx, ContinuousLinearMap.zero_comp, map_zero,
      mul_zero, add_zero]

private theorem integrable_and_integral_weak_log_nonneg_of_smooth_slice_tests
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (rho R q : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hrho : ContinuousOn rho Ω) (hR : ContinuousOn R Ω) (hq : ContinuousOn q Ω)
    (hB : ContinuousOn B Ω)
    {d : ℕ} (e : (ℝ × E) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (he : MeasurePreserving e ((volume : Measure ℝ).prod μ) volume)
    (hweak : ∀ ψ : (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∀ z, 0 ≤ ψ z) →
      let df := fun z : ℝ × E => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      0 ≤ ∫ z, rho z *
        (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
          B z (df z) (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod μ)
    {ψ : (ℝ × E) → ℝ} (hψ : LocallyLipschitzOn Ω ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω) (hψn : ∀ z, 0 ≤ ψ z) :
    let df := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E)
    Integrable (fun z => rho z *
      (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
        B z (df z) ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ ℝ E))))
        ((volume : Measure ℝ).prod μ) ∧
    0 ≤ ∫ z, rho z *
      (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * R z + q z) * ψ z +
        B z (df z) ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ ℝ E)))
        ∂(volume : Measure ℝ).prod μ := by
  let π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ E)
  apply integrable_and_integral_weak_log_nonneg_of_smooth_tests hΩ hf rho R q B
    hrho hR hq hB π ((volume : Measure ℝ).prod μ) e he _ hψ hψc hψs hψn
  intro v hv hvc hvs hvn
  have heq := ae_weak_log_joint_eq_slice (μ := μ) hΩ hf
    (hv.of_le (show (1 : ℕ∞) ≤ ∞ by simp)).locallyLipschitz.locallyLipschitzOn
    hvs rho R q B
  simpa only [π, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ← integral_congr_ae heq] using hweak v hv hvc hvs hvn

private theorem integrable_density_residual
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (w : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hw : ContinuousOn w Ω) (hB : ContinuousOn B Ω)
    (π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (μ : Measure (ℝ × E)) [IsFiniteMeasureOnCompacts μ]
    {ψ : (ℝ × E) → ℝ} (hψ : LocallyLipschitzOn Ω ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω) :
    Integrable (fun z => w z * (fderiv ℝ ψ z (1, 0) +
      B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z)))) μ := by
  let K := tsupport ψ
  have hK : IsCompact K := hψc
  have hKΩ : K ⊆ Ω := hψs
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨C, hLip⟩ := (hψ.mono hLΩ).exists_lipschitzOnWith_of_compact hL
  have hdu : Integrable (fderiv ℝ ψ) (μ.restrict K) := by
    apply IntegrableOn.of_bound hK.measure_lt_top
      (measurable_fderiv ℝ ψ).aestronglyMeasurable (C : ℝ)
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact norm_fderiv_le_of_lipschitzOn ℝ
      (mem_interior_iff_mem_nhds.mp (hKL hz)) hLip
  let d := fun z => π (fderiv ℝ f z)
  let ev : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (1, 0)
  let bs := fun z => w z • ((B z (d z)).comp π)
  let bt := fun z => w z • ev
  let b := fun z => bt z + bs z
  obtain ⟨hbsm, _, hsbounds⟩ := weak_log_coefficients_measurable_bounded_on_compacts
    hΩ hf w (fun _ => 0) (fun _ => 0) B hw continuousOn_const continuousOn_const hB π μ
  have hbt : ContinuousOn bt Ω := hw.smul continuousOn_const
  have hbm (v : (ℝ × E) →L[ℝ] ℝ) :
      AEStronglyMeasurable (fun z => b z v) (μ.restrict K) := by
    have hbΩ : AEStronglyMeasurable (fun z => b z v) (μ.restrict Ω) :=
      ((hbt.clm_apply continuousOn_const).aestronglyMeasurable
        hΩ.measurableSet).add (hbsm v)
    exact hbΩ.mono_measure (Measure.restrict_mono hKΩ le_rfl)
  obtain ⟨M, _, hM, _⟩ := hsbounds K hK hKΩ
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (hbt.mono hKΩ)
  have hb : ∀ᵐ z ∂μ.restrict K, ‖b z‖ ≤ N + M := by
    filter_upwards [hM, ae_restrict_mem hK.measurableSet] with z hz hzK
    exact (norm_add_le (bt z) (bs z)).trans (add_le_add (hN z hzK) hz)
  have hIntK : Integrable (fun z => b z (fderiv ℝ ψ z)) (μ.restrict K) :=
    integrable_clm_apply_of_ae_norm_le b hbm hb hdu
  have hInt : Integrable (fun z => b z (fderiv ℝ ψ z)) μ := by
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero hIntK
    intro z hz
    rw [fderiv_of_notMem_tsupport ℝ hz, map_zero]
  simpa only [b, bt, bs, ev, d, add_apply, smul_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    mul_add] using hInt

private theorem integrable_and_integral_density_residual_nonneg_of_smooth_tests
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (w : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hw : ContinuousOn w Ω) (hB : ContinuousOn B Ω)
    (π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (μ : Measure (ℝ × E)) {d : ℕ}
    (e : (ℝ × E) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (he : MeasurePreserving e μ volume)
    (hweak : ∀ ψ : (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∀ z, 0 ≤ ψ z) →
      0 ≤ ∫ z, w z * (fderiv ℝ ψ z (1, 0) +
        B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z))) ∂μ)
    {ψ : (ℝ × E) → ℝ} (hψ : LocallyLipschitzOn Ω ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω) (hψn : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z => w z * (fderiv ℝ ψ z (1, 0) +
      B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z)))) μ ∧
    0 ≤ ∫ z, w z * (fderiv ℝ ψ z (1, 0) +
      B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z))) ∂μ := by
  let d := fun z => π (fderiv ℝ f z)
  let ev : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (1, 0)
  let bs := fun z => w z • ((B z (d z)).comp π)
  let bt := fun z => w z • ev
  let b := fun z => bt z + bs z
  obtain ⟨hbsm, _, hsbounds⟩ := weak_log_coefficients_measurable_bounded_on_compacts
    hΩ hf w (fun _ => 0) (fun _ => 0) B hw continuousOn_const continuousOn_const hB π μ
  have hbt : ContinuousOn bt Ω := hw.smul continuousOn_const
  have hbm (v : (ℝ × E) →L[ℝ] ℝ) :
      AEStronglyMeasurable (fun z => b z v) (μ.restrict Ω) := by
    exact ((hbt.clm_apply continuousOn_const).aestronglyMeasurable
      hΩ.measurableSet).add (hbsm v)
  have hbound (K : Set (ℝ × E)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ M N : ℝ, (∀ᵐ z ∂μ.restrict K, ‖b z‖ ≤ M) ∧
        (∀ᵐ z ∂μ.restrict K, ‖(0 : ℝ)‖ ≤ N) := by
    obtain ⟨M, _, hM, _⟩ := hsbounds K hK hKΩ
    obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (hbt.mono hKΩ)
    refine ⟨N + M, 0, ?_, Eventually.of_forall (fun _ => by simp)⟩
    filter_upwards [hM, ae_restrict_mem hK.measurableSet] with z hz hzK
    exact (norm_add_le (bt z) (bs z)).trans (add_le_add (hN z hzK) hz)
  have hidentity (v : (ℝ × E) → ℝ) (z : ℝ × E) :
      b z (fderiv ℝ v z) + 0 * v z = w z * (fderiv ℝ v z (1, 0) +
        B z (π (fderiv ℝ f z)) (π (fderiv ℝ v z))) := by
    simp only [b, bt, bs, ev, d, add_apply, smul_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      zero_mul, add_zero, mul_add]
  have hv (v : (ℝ × E) → ℝ) (hv : ContDiff ℝ ∞ v)
      (hvc : HasCompactSupport v) (hvs : tsupport v ⊆ Ω) (hvn : ∀ z, 0 ≤ v z) :
      0 ≤ ∫ z, b z (fderiv ℝ v z) + 0 * v z ∂μ := by
    simpa only [hidentity] using hweak v hv hvc hvs hvn
  have h := integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving
    e he hΩ b (fun _ => 0) hbm aestronglyMeasurable_const hbound hv hψ hψc hψs hψn
  simpa only [hidentity] using h

end DifferentialGeometry.Analysis


noncomputable section

open Filter MeasureTheory Set

private theorem integral_weak_residual_eq_prod_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a a' c' c : ℝ} {W : Set E} (hW : IsOpen W)
    (haa : a < a') (hcc : c' < c)
    {f ψ : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn (Ioo a c ×ˢ W) f)
    (hψ : LocallyLipschitzOn (Ioo a c ×ˢ W) ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ W)
    (w q : ℝ × E → ℝ)
    (H : ℝ × E → (E →L[ℝ] ℝ) → ℝ)
    (B : ℝ × E → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :
    let dj := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E)
    let ds := fun z : ℝ × E => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    (∫ z, w z * (q z * fderiv ℝ ψ z (1, 0) + H z (dj z) * ψ z +
      B z (dj z) ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ ℝ E)))
      ∂(volume : Measure ℝ).prod μ) =
    ∫ z, w z * (q z * deriv (fun t : ℝ => ψ (t, z.2)) z.1 +
      H z (ds z) * ψ z + B z (ds z) (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2))
      ∂(volume.restrict (Ioc a' c')).prod (μ.restrict W) := by
  let ν : Measure (ℝ × E) := (volume : Measure ℝ).prod μ
  let C : Set (ℝ × E) := Ioc a' c' ×ˢ W
  let dj := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E)
  let ds := fun z : ℝ × E => fderiv ℝ (fun y : E => f (z.1, y)) z.2
  let L := fun z => w z * (q z * fderiv ℝ ψ z (1, 0) + H z (dj z) * ψ z +
    B z (dj z) ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ ℝ E)))
  let R := fun z => w z * (q z * deriv (fun t : ℝ => ψ (t, z.2)) z.1 +
    H z (ds z) * ψ z + B z (ds z) (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2))
  have hCΩ : C ⊆ Ioo a c ×ˢ W := fun z hz =>
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans_lt hcc⟩, hz.2⟩
  have hψC : tsupport ψ ⊆ C := fun z hz =>
    ⟨⟨(hψsupp hz).1.1, (hψsupp hz).1.2.le⟩, (hψsupp hz).2⟩
  have hspace {g : ℝ × E → ℝ} {z : ℝ × E} (hg : DifferentiableAt ℝ g z) :
      fderiv ℝ (fun y : E => g (z.1, y)) z.2 =
        (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (hg.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  have htime {g : ℝ × E → ℝ} {z : ℝ × E} (hg : DifferentiableAt ℝ g z) :
      deriv (fun t : ℝ => g (t, z.2)) z.1 = fderiv ℝ g z (1, 0) :=
    (hg.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  have hzero (z : ℝ × E) (hz : z ∉ C) : ψ z = 0 ∧ fderiv ℝ ψ z = 0 ∧
      deriv (fun t : ℝ => ψ (t, z.2)) z.1 = 0 ∧
      fderiv ℝ (fun y : E => ψ (z.1, y)) z.2 = 0 := by
    have hn : z ∉ tsupport ψ := fun h => hz (hψC h)
    have hnt : z.1 ∉ tsupport (fun t : ℝ => ψ (t, z.2)) := by
      intro ht
      apply hn
      exact tsupport_comp_subset_preimage (f := fun t : ℝ => (t, z.2)) ψ
        (continuous_id.prodMk continuous_const) ht
    have hnx : z.2 ∉ tsupport (fun y : E => ψ (z.1, y)) := by
      intro hy
      apply hn
      exact tsupport_comp_subset_preimage (f := fun y : E => (z.1, y)) ψ
        (continuous_const.prodMk continuous_id) hy
    exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn,
      deriv_of_notMem_tsupport hnt, fderiv_of_notMem_tsupport ℝ hnx⟩
  have hLzero (z : ℝ × E) (hz : z ∉ C) : L z = 0 := by
    have hz0 := hzero z hz
    simp only [L, hz0.1, hz0.2.1, zero_apply, ContinuousLinearMap.zero_comp,
      map_zero, mul_zero, add_zero]
  have hRzero (z : ℝ × E) (hz : z ∉ C) : R z = 0 := by
    have hz0 := hzero z hz
    simp only [R, hz0.1, hz0.2.2.1, hz0.2.2.2, map_zero, mul_zero, add_zero]
  have heq : L =ᵐ[ν] R := by
    filter_upwards [hf.ae_differentiableAt_of_isOpen (μ := ν) (isOpen_Ioo.prod hW),
      hψ.ae_differentiableAt_of_isOpen (μ := ν) (isOpen_Ioo.prod hW)] with z hdf hdψ
    by_cases hz : z ∈ C
    · dsimp only [L, R, dj, ds]
      rw [htime (hdψ (hCΩ hz)), hspace (hdψ (hCΩ hz)), hspace (hdf (hCΩ hz))]
    · exact (hLzero z hz).trans (hRzero z hz).symm
  change (∫ z, L z ∂ν) = ∫ z, R z
    ∂(volume.restrict (Ioc a' c')).prod (μ.restrict W)
  calc
    (∫ z, L z ∂ν) = ∫ z, R z ∂ν := integral_congr_ae heq
    _ = ∫ z in C, R z ∂ν :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hRzero).symm
    _ = _ := by rw [Measure.prod_restrict]


private theorem integrable_density_residual_prod_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a a' c' c : ℝ} {W : Set E} (hW : IsOpen W)
    (haa : a < a') (hcc : c' < c)
    {f ψ : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn (Ioo a c ×ˢ W) f)
    (hψ : LocallyLipschitzOn (Ioo a c ×ˢ W) ψ)
    (w : ℝ × E → ℝ)
    (B : ℝ × E → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hInt : Integrable (fun z => w z * (fderiv ℝ ψ z (1, 0) +
      B z ((fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E))
        ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ ℝ E))))
      ((volume : Measure ℝ).prod μ)) :
    Integrable (fun z => w z * (deriv (fun t : ℝ => ψ (t, z.2)) z.1 +
      B z (fderiv ℝ (fun y : E => f (z.1, y)) z.2)
        (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2)))
      ((volume.restrict (Ioc a' c')).prod (μ.restrict W)) := by
  let ν : Measure (ℝ × E) := (volume : Measure ℝ).prod μ
  have hspace {g : ℝ × E → ℝ} {z : ℝ × E}
      (hg : DifferentiableAt ℝ g z) :
      fderiv ℝ (fun y : E => g (z.1, y)) z.2 =
        (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (hg.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  have htime {g : ℝ × E → ℝ} {z : ℝ × E}
      (hg : DifferentiableAt ℝ g z) :
      deriv (fun t : ℝ => g (t, z.2)) z.1 = fderiv ℝ g z (1, 0) :=
    (hg.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  rw [Measure.prod_restrict]
  apply hInt.restrict.congr
  filter_upwards [ae_restrict_of_ae
    (hf.ae_differentiableAt_of_isOpen (μ := ν) (isOpen_Ioo.prod hW)),
    ae_restrict_of_ae
      (hψ.ae_differentiableAt_of_isOpen (μ := ν) (isOpen_Ioo.prod hW)),
    ae_restrict_mem (measurableSet_Ioc.prod hW.measurableSet)] with z hdf hdψ hz
  have hzΩ : z ∈ Ioo a c ×ˢ W :=
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans_lt hcc⟩, hz.2⟩
  rw [htime (hdψ hzΩ), hspace (hdf hzΩ), hspace (hdψ hzΩ)]


noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private theorem exists_measurePreserving_prod_modelHaar_euclidean :
    ∃ d : ℕ, ∃ e : (ℝ × E) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      MeasurePreserving e ((volume : Measure ℝ).prod (modelHaar (E := E))) volume := by
  let Y := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e₀ : (ℝ × E) ≃L[ℝ] (ℝ × Y) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := E))
  have hspace : MeasurePreserving (toEuclidean (E := E)) (modelHaar (E := E)) volume :=
    ⟨(toEuclidean (E := E)).continuous.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  have h₀ : MeasurePreserving e₀
      ((volume : Measure ℝ).prod (modelHaar (E := E))) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod hspace
  let e₁ : (ℝ × Y) ≃L[ℝ] WithLp 2 (ℝ × Y) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ Y).symm
  let basis := stdOrthonormalBasis ℝ (WithLp 2 (ℝ × Y))
  refine ⟨Module.finrank ℝ (WithLp 2 (ℝ × Y)),
    e₀.trans (e₁.trans basis.repr.toContinuousLinearEquiv), ?_⟩
  exact basis.measurePreserving_repr.comp ((WithLp.volume_preserving_toLp ℝ Y).comp h₀)

end DifferentialGeometry.Integral.Measure

noncomputable section

namespace DifferentialGeometry.Analysis

open Filter MeasureTheory Set
open scoped _root_.Topology ContDiff

private theorem integrable_clm_fderiv_of_tsupport_subset
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} (hf : LocallyLipschitzOn Ω f)
    {A : X → (X →L[ℝ] ℝ) →L[ℝ] ℝ}
    (hA : ContinuousOn A Ω) (hAc : HasCompactSupport A) (hAs : tsupport A ⊆ Ω) :
    Integrable (fun z => A z (fderiv ℝ f z)) μ := by
  let covectorNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let covectorNormedSpace : NormedSpace ℝ (X →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let covectorDualNormedAddCommGroup : NormedAddCommGroup ((X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let covectorDualNormedSpace : NormedSpace ℝ ((X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  have hd := (hf.locallyIntegrableOn_fderiv (μ := μ) hΩ).integrableOn_compact_subset hAs hAc
  have hAK := hA.mono hAs
  obtain ⟨M, hM⟩ := hAc.exists_bound_of_continuousOn hAK
  have hint : IntegrableOn (fun z => A z (fderiv ℝ f z)) (tsupport A) μ := by
    apply integrable_clm_apply_of_ae_norm_le A
    · intro v
      exact (hAK.clm_apply continuousOn_const).aestronglyMeasurable
        (isClosed_tsupport A).measurableSet
    · filter_upwards [ae_restrict_mem (isClosed_tsupport A).measurableSet] with z hz
      exact hM z hz
    · exact hd
  apply hint.integrable_of_forall_notMem_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz]
  rfl

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]

private local instance : NormedAddCommGroup (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace ℝ (X →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup ((X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace ℝ ((X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance :
    NormedAddCommGroup ((X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance :
    NormedSpace ℝ ((X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem integrable_weighted_fderiv_bilinear_test
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} (hf : LocallyLipschitzOn Ω f)
    {rho : X → ℝ} (hrho : ContinuousOn rho Ω)
    {B : X → (X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) →L[ℝ] ℝ}
    (hB : ContinuousOn B Ω)
    {ψ : X → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω) :
    Integrable (fun z => rho z * B z (fderiv ℝ f z) (fderiv ℝ ψ z)) μ := by
  let A := fun z => rho z • ((B z).flip (fderiv ℝ ψ z))
  have hflip : ContinuousOn (fun z => (B z).flip) Ω :=
    (ContinuousLinearMap.flipₗᵢ ℝ (X →L[ℝ] ℝ) (X →L[ℝ] ℝ) ℝ).continuous.comp_continuousOn hB
  have hA : ContinuousOn A Ω :=
    hrho.smul (hflip.clm_apply (hψ.continuous_fderiv (by norm_num)).continuousOn)
  have hAs : tsupport A ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro z hz
    by_contra hn
    have hdz := fderiv_of_notMem_tsupport ℝ hn
    exact hz (by simp only [A, hdz, map_zero, smul_zero])
  have hAc : HasCompactSupport A := hψc.of_isClosed_subset (isClosed_tsupport A) hAs
  have h := integrable_clm_fderiv_of_tsupport_subset (μ := μ) hΩ hf hA hAc (hAs.trans hψs)
  simpa only [A, smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul] using h

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
private theorem integrable_continuousOn_mul_test
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set X} {rho ψ : X → ℝ} (hrho : ContinuousOn rho Ω)
    (hψ : ContinuousOn ψ Ω) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    Integrable (fun z => rho z * ψ z) μ := by
  have hi : IntegrableOn (fun z => rho z * ψ z) (tsupport ψ) μ :=
    ((hrho.mono hψs).mul (hψ.mono hψs)).integrableOn_compact hψc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

private theorem integrable_weighted_fderiv_apply_test
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} (hf : LocallyLipschitzOn Ω f)
    {rho ψ : X → ℝ} (hrho : ContinuousOn rho Ω) (hψ : ContinuousOn ψ Ω)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) (v : X) :
    Integrable (fun z => rho z * ψ z * fderiv ℝ f z v) μ := by
  let ev : (X →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  let A := fun z => (rho z * ψ z) • ev
  have hA : ContinuousOn A Ω := (hrho.mul hψ).smul continuousOn_const
  have hAs : tsupport A ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro z hz
    by_contra hn
    exact hz (by simp only [A, image_eq_zero_of_notMem_tsupport hn, mul_zero, zero_smul])
  have hAc : HasCompactSupport A := hψc.of_isClosed_subset (isClosed_tsupport A) hAs
  have h := integrable_clm_fderiv_of_tsupport_subset (μ := μ) hΩ hf hA hAc (hAs.trans hψs)
  simpa only [A, ev, smul_apply, ContinuousLinearMap.apply_apply, smul_eq_mul] using h

omit [FiniteDimensional ℝ X] in
private theorem integrable_weighted_test_fderiv_apply
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set X} {rho : X → ℝ} (hrho : ContinuousOn rho Ω)
    {ψ : X → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω) (v : X) :
    Integrable (fun z => rho z * fderiv ℝ ψ z v) μ := by
  have hs : tsupport (fun z => fderiv ℝ ψ z v) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ v
  apply integrable_continuousOn_mul_test hrho
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn
    (hψc.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hψs)

end

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem continuousOn_time_sub_product
    {V : Type*} [TopologicalSpace V] {a c : ℝ} (ha : 1 < a)
    {W T : Set E} (hWT : W ⊆ T) (f : ℝ × E → V)
    (hf : ContinuousOn f (Iio 0 ×ˢ T)) :
    ContinuousOn (fun z : ℝ × E => f (1 - z.1, z.2)) (Ioo a c ×ˢ W) := by
  have hτ : ContinuousOn (fun z : ℝ × E => (1 - z.1, z.2)) (Ioo a c ×ˢ W) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  exact hf.comp hτ (fun z hz => ⟨sub_neg.mpr (ha.trans hz.1.1), hWT hz.2⟩)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem continuousOn_time_sub_chart_scalar
    {a c : ℝ} (ha : 1 < a) (x : P.M) {W : Set E}
    (hWt : W ⊆ (extChartAt I x).target) (f : ℝ × P.M → ℝ)
    (hf : ContinuousOn f (Iio 0 ×ˢ (univ : Set P.M))) :
    ContinuousOn (fun z : ℝ × E => f (1 - z.1, (extChartAt I x).symm z.2))
      (Ioo a c ×ˢ W) := by
  have hχ : ContinuousOn (fun z : ℝ × E => (extChartAt I x).symm z.2)
      (Ioo a c ×ˢ W) :=
    (continuousOn_extChartAt_symm (I := I) x).comp
      (continuous_snd.continuousOn : ContinuousOn (fun z : ℝ × E => z.2)
        (Ioo a c ×ˢ W)) (fun _ hz => hWt hz.2)
  exact hf.comp ((continuous_const.sub continuous_fst).continuousOn.prodMk hχ)
    (fun z hz => ⟨sub_neg.mpr (ha.trans hz.1.1), mem_univ _⟩)

private theorem continuousOn_time_sub_chart_coefficients
    {X : PointedFlowSeq (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    {a c : ℝ} (ha : 1 < a) (x : P.M) {W : Set E}
    (hWt : W ⊆ (extChartAt I x).target) :
    let Ω := Ioo a c ×ˢ W
    let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
      ((extChartAt I x).symm z.2)
    ContinuousOn ρ Ω ∧ ContinuousOn S Ω ∧ ContinuousOn B Ω := by
  let Ω := Ioo a c ×ˢ W
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
    ((extChartAt I x).symm z.2)
  have hρ : ContinuousOn ρ Ω :=
    continuousOn_time_sub_product ha hWt _ (continuousOn_chartDensity Phi co hregular x)
  have hB : ContinuousOn B Ω :=
    continuousOn_time_sub_product ha hWt _ (continuousOn_chartGradientBilin Phi co hregular x)
  have hscalar : ContinuousOn (fun z : ℝ × P.M => metricScalarAt (co.gInf z.1) z.2)
      (Iio 0 ×ˢ (univ : Set P.M)) :=
    (scalarCont_regular Phi co hcarrier hregular).mono (Set.prod_mono hregular Subset.rfl)
  have hS : ContinuousOn S Ω := continuousOn_time_sub_chart_scalar ha x hWt _ hscalar
  exact ⟨hρ, hS, hB⟩

private theorem poleEndpoint_density_coefficients_continuousOn
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E}
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    let Ω := Ioo a c ×ˢ W
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
      ((extChartAt I x).symm z.2)
    let q₀ := fun z : ℝ × E => ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)
    ContinuousOn ρ Ω ∧ ContinuousOn S Ω ∧ ContinuousOn q₀ Ω ∧ ContinuousOn B Ω := by
  let Ω := Ioo a c ×ˢ W
  let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
    ((extChartAt I x).symm z.2)
  let q₀ := fun z : ℝ × E => ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)
  change ContinuousOn ρ Ω ∧ ContinuousOn S Ω ∧ ContinuousOn q₀ Ω ∧ ContinuousOn B Ω
  obtain ⟨hρ, hS, hB⟩ := continuousOn_time_sub_chart_coefficients Phi R co
    rfl (fun _ ht => ht) ha x hWt
  have hf : ContinuousOn f Ω :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ).continuousOn.mono
        (fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have hq₀ : ContinuousOn q₀ Ω := by
    apply (continuousOn_const.sub hf).div
      (continuousOn_const.mul continuous_fst.continuousOn)
    intro z hz
    apply mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (ha.trans hz.1.1))
  exact ⟨hρ, hS, hq₀, hB⟩


private theorem integral_poleEndpoint_logarithmic_residual_nonneg_of_smooth_tests
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (hlog : ∀ ψ : ℝ × E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ ψ z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * ψ z +
          B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (ψ : ℝ × E → ℝ) (hψ : LocallyLipschitzOn (Ioo a' c' ×ˢ W) ψ)
    (hψc : HasCompactSupport ψ) (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ W)
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
    0 ≤ ∫ z, ρ z *
      ((deriv (fun t => f (t, z.2)) z.1 + B z (d z) (d z) - S z +
          (Module.finrank ℝ E : ℝ) / (2 * z.1)) * ψ z +
        B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W) := by
  let Ω₀ : Set (ℝ × E) := Ioo a c ×ˢ W
  let Ω : Set (ℝ × E) := Ioo a' c' ×ˢ W
  let ν : Measure (ℝ × E) := (volume : Measure ℝ).prod (modelHaar (E := E))
  let μ : Measure E := (modelHaar (E := E)).restrict W
  let ν' : Measure (ℝ × E) := (volume.restrict (Ioc a' c')).prod μ
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let df : ℝ × E → E →L[ℝ] ℝ := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
    ((extChartAt I x).symm z.2)
  let n : ℝ := Module.finrank ℝ E
  let q₀ := fun z : ℝ × E => (n - f z) / (2 * z.1)
  let c₀ : ℝ → ℝ := fun t => n / (2 * t)
  have hΩ₀ : IsOpen Ω₀ := isOpen_Ioo.prod hW
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hΩΩ₀ : Ω ⊆ Ω₀ := fun _ hz =>
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hz.2⟩
  have hfClosed : LocallyLipschitzOn (Icc a c ×ˢ W) f :=
    locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ
  have hf₀ : LocallyLipschitzOn Ω₀ f :=
    hfClosed.mono fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
  have hf : LocallyLipschitzOn Ω f := hf₀.mono hΩΩ₀
  obtain ⟨hρCont₀, hSCont₀, hqCont₀, hBCont₀⟩ :=
    poleEndpoint_density_coefficients_continuousOn F hcar hreg b hbmem tau q hsigma
      Phi R hR co kappa hF p hJ ha hbase rho hrho ell hconv x hWt hWJ
  have hρCont : ContinuousOn ρ Ω := hρCont₀.mono hΩΩ₀
  have hSCont : ContinuousOn S Ω := hSCont₀.mono hΩΩ₀
  have hqCont : ContinuousOn q₀ Ω := hqCont₀.mono hΩΩ₀
  have hBCont : ContinuousOn B Ω := hBCont₀.mono hΩΩ₀
  have hHJ := ae_poleEndpoint_redLength_limit_hamilton_jacobi_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ
  obtain ⟨m, e, he⟩ := Integral.Measure.exists_measurePreserving_prod_modelHaar_euclidean
    (E := E)
  have hweak : ∀ v : ℝ × E → ℝ, LocallyLipschitzOn Ω v →
      HasCompactSupport v → tsupport v ⊆ Ω → (∀ z, 0 ≤ v z) →
      0 ≤ ∫ z, ρ z *
        ((deriv (fun t => f (t, z.2)) z.1 + B z (df z) (df z) - S z + c₀ z.1) * v z +
          B z (df z) (fderiv ℝ (fun y => v (z.1, y)) z.2)) ∂ν' := by
    intro v hv hvc hvs hvn
    have hvAll := hv.locallyLipschitz_of_tsupport_subset hΩ hvs
    have htest := Analysis.integrable_and_integral_weak_log_nonneg_of_smooth_slice_tests
      hΩ hf ρ S q₀ B hρCont hSCont hqCont hBCont e he
      (fun v hv hvc hvs hvn => hlog v hv hvc (hvs.trans hΩΩ₀) hvn)
      hv hvc hvs hvn
    have htransport := integral_weak_residual_eq_prod_restrict
      (μ := modelHaar (E := E)) hW haa hcc hf₀
      hvAll.locallyLipschitzOn hvs ρ (fun _ => 0)
      (fun z d => (1 / 2 : ℝ) * B z d d - (1 / 2 : ℝ) * S z + q₀ z) B
    have hpos : 0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * S z + q₀ z) * v z +
          B z (df z) (fderiv ℝ (fun y => v (z.1, y)) z.2)) ∂ν' := by
      simp only [zero_mul, zero_add] at htransport
      rw [← htransport]
      exact htest.2
    have hEq : (fun z => ρ z *
        ((deriv (fun t => f (t, z.2)) z.1 + B z (df z) (df z) - S z + c₀ z.1) * v z +
          B z (df z) (fderiv ℝ (fun y => v (z.1, y)) z.2))) =ᵐ[ν']
        (fun z => ρ z *
          (((1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * S z + q₀ z) * v z +
            B z (df z) (fderiv ℝ (fun y => v (z.1, y)) z.2))) := by
      rw [show ν' = ν.restrict (Ioc a' c' ×ˢ W) from Measure.prod_restrict _ _]
      filter_upwards [ae_restrict_of_ae hHJ,
        ae_restrict_mem (measurableSet_Ioc.prod hW.measurableSet)] with z hz hzs
      have hz₀ : z ∈ Ω₀ := ⟨⟨haa.trans hzs.1.1, hzs.1.2.trans_lt hcc⟩, hzs.2⟩
      have hj : deriv (fun t => f (t, z.2)) z.1 +
          (1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * S z + f z / (2 * z.1) = 0 :=
        hz hz₀
      have hr : deriv (fun t => f (t, z.2)) z.1 + B z (df z) (df z) - S z + c₀ z.1 =
          (1 / 2 : ℝ) * B z (df z) (df z) - (1 / 2 : ℝ) * S z + q₀ z := by
        dsimp only [c₀, q₀]
        rw [sub_div]
        linarith only [hj]
      rw [hr]
    rw [integral_congr_ae hEq]
    exact hpos
  exact hweak ψ hψ hψc hψsupp hψnonneg


private local instance timeCovectorNormedAddCommGroup : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeCovectorNormedSpace : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeDualNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeDualNormedSpace : NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

open scoped Interval

private theorem poleEndpoint_density_transform_integrable
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ W) :
    let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
    let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
      ((extChartAt I x).symm z.2)
    let n : ℝ := Module.finrank ℝ E
    let w : ℝ → ℝ := fun t => Real.exp (-(n / 2) * Real.log t -
      (n / 2) * Real.log (4 * Real.pi))
    let ν : Measure (ℝ × E) := (volume.restrict (uIoc a' c')).prod
      ((modelHaar (E := E)).restrict W)
    Integrable (fun z => ρ z * (w z.1 * Real.exp (-f z)) *
        B z (fderiv ℝ (fun y : E => f (z.1, y)) z.2)
          (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2)) ν ∧
      Integrable (fun z => ρ z *
        (deriv (fun t => w t * Real.exp (-f (t, z.2))) z.1 +
          S z * (w z.1 * Real.exp (-f z))) * ψ z) ν ∧
      Integrable (fun z => ρ z * (w z.1 * Real.exp (-f z)) *
        deriv (fun t => ψ (t, z.2)) z.1) ν := by
  dsimp only
  let Ω₀ : Set (ℝ × E) := Ioo a c ×ˢ W
  let Ω : Set (ℝ × E) := Ioo a' c' ×ˢ W
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
    ((extChartAt I x).symm z.2)
  let n : ℝ := Module.finrank ℝ E
  let w : ℝ → ℝ := fun t => Real.exp (-(n / 2) * Real.log t -
    (n / 2) * Real.log (4 * Real.pi))
  let u : ℝ × E → ℝ := fun z => w z.1 * Real.exp (-f z)
  let ν₀ : Measure (ℝ × E) := (volume : Measure ℝ).prod (modelHaar (E := E))
  let ν : Measure (ℝ × E) := (volume.restrict (uIoc a' c')).prod
    ((modelHaar (E := E)).restrict W)
  have hΩ₀ : IsOpen Ω₀ := isOpen_Ioo.prod hW
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hΩΩ₀ : Ω ⊆ Ω₀ := fun _ hz =>
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hz.2⟩
  have hf₀ : LocallyLipschitzOn Ω₀ f :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ).mono
        (fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have hf : LocallyLipschitzOn Ω f := hf₀.mono hΩΩ₀
  obtain ⟨hρ₀, hS₀, hB₀⟩ := continuousOn_time_sub_chart_coefficients Phi R co
    rfl (fun _ ht => ht) ha x hWt
  have hρ : ContinuousOn ρ Ω := hρ₀.mono hΩΩ₀
  have hS : ContinuousOn S Ω := hS₀.mono hΩΩ₀
  have hB : ContinuousOn B Ω := hB₀.mono hΩΩ₀
  have hψΩ : tsupport ψ ⊆ Ω := hψsupp
  have hwc : ContinuousOn (fun z : ℝ × E => w z.1) Ω := by
    apply Real.continuous_exp.comp_continuousOn
    apply (continuousOn_const.mul
      (continuous_fst.continuousOn.log fun z hz => ?_)).sub continuousOn_const
    exact ne_of_gt (zero_lt_one.trans ((ha.trans haa).trans hz.1.1))
  have huc : ContinuousOn u Ω :=
    hwc.mul (Real.continuous_exp.comp_continuousOn hf.continuousOn.neg)
  have hρuc : ContinuousOn (fun z => ρ z * u z) Ω := hρ.mul huc
  have hnc : ContinuousOn (fun z : ℝ × E => n / (2 * z.1)) Ω := by
    apply continuousOn_const.div (continuousOn_const.mul continuous_fst.continuousOn)
    intro z hz
    exact mul_ne_zero (by norm_num) (ne_of_gt (zero_lt_one.trans ((ha.trans haa).trans hz.1.1)))
  have hνdiff : ∀ᵐ z ∂ν, DifferentiableAt ℝ f z := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_of_ae (hf₀.ae_differentiableAt_of_isOpen
      (μ := ν₀) hΩ₀),
      ae_restrict_mem (measurableSet_uIoc.prod hW.measurableSet)] with z hz hzs
    have ht : z.1 ∈ Ioc a' c' := by simpa only [uIoc_of_le hac] using hzs.1
    exact hz ⟨⟨haa.trans ht.1, ht.2.trans_lt hcc⟩, hzs.2⟩
  have hνmem : ∀ᵐ z ∂ν, z ∈ Ω₀ := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod hW.measurableSet)] with z hz
    have ht : z.1 ∈ Ioc a' c' := by simpa only [uIoc_of_le hac] using hz.1
    exact ⟨⟨haa.trans ht.1, ht.2.trans_lt hcc⟩, hz.2⟩
  let π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ E)
  have hsliceSpace {g : ℝ × E → ℝ} {z : ℝ × E}
      (hg : DifferentiableAt ℝ g z) :
      fderiv ℝ (fun y : E => g (z.1, y)) z.2 = π (fderiv ℝ g z) :=
    (hg.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  have hsliceTime {g : ℝ × E → ℝ} {z : ℝ × E}
      (hg : DifferentiableAt ℝ g z) :
      deriv (fun t : ℝ => g (t, z.2)) z.1 = fderiv ℝ g z (1, 0) :=
    (hg.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  have hψdiff (z : ℝ × E) : DifferentiableAt ℝ ψ z :=
    (hψ.differentiable (by norm_num)).differentiableAt
  let Cπ : ((E →L[ℝ] ℝ) →L[ℝ] ℝ) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ ((ℝ × E) →L[ℝ] ℝ) (E →L[ℝ] ℝ) ℝ).flip π
  let Aψ : (ℝ × E) → ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ := fun z =>
    (ρ z * u z) • Cπ ((B z).flip (π (fderiv ℝ ψ z)))
  have hBflip : ContinuousOn (fun z => (B z).flip) Ω :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E →L[ℝ] ℝ) (E →L[ℝ] ℝ) ℝ).continuous.comp_continuousOn hB
  have hπdψ : ContinuousOn (fun z => π (fderiv ℝ ψ z)) Ω :=
    π.continuous.comp_continuousOn (hψ.continuous_fderiv (by norm_num)).continuousOn
  have hAψ : ContinuousOn Aψ Ω :=
    hρuc.smul (Cπ.continuous.comp_continuousOn (hBflip.clm_apply hπdψ))
  have hAψs : tsupport Aψ ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro z hz
    by_contra hn
    exact hz (by simp only [Aψ, fderiv_of_notMem_tsupport ℝ hn, map_zero, smul_zero])
  have hAψc : HasCompactSupport Aψ :=
    hψc.of_isClosed_subset (isClosed_tsupport Aψ) hAψs
  have hspaceJoint : Integrable (fun z => ρ z * u z *
      B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z))) ν₀ := by
    have h := DifferentialGeometry.Analysis.integrable_clm_fderiv_of_tsupport_subset
      (μ := ν₀) hΩ hf hAψ hAψc (hAψs.trans hψΩ)
    simpa only [Aψ, Cπ, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul] using h
  have hspace : Integrable (fun z => ρ z * (w z.1 * Real.exp (-f z)) *
      B z (fderiv ℝ (fun y : E => f (z.1, y)) z.2)
        (fderiv ℝ (fun y : E => ψ (z.1, y)) z.2)) ν := by
    have hi : Integrable (fun z => ρ z * u z *
        B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z))) ν := by
      dsimp only [ν]
      rw [Measure.prod_restrict]
      exact hspaceJoint.restrict
    apply hi.congr
    filter_upwards [hνdiff] with z hz
    rw [hsliceSpace hz, hsliceSpace (hψdiff z)]
  have htimeJoint : Integrable (fun z =>
      ρ z * u z * (S z - n / (2 * z.1)) * ψ z -
        ρ z * u z * ψ z * fderiv ℝ f z (1, 0)) ν₀ :=
    (DifferentialGeometry.Analysis.integrable_continuousOn_mul_test
      (μ := ν₀) (hρuc.mul (hS.sub hnc)) hψ.continuous.continuousOn hψc hψΩ).sub
      (DifferentialGeometry.Analysis.integrable_weighted_fderiv_apply_test
        (μ := ν₀) hΩ hf hρuc hψ.continuous.continuousOn hψc hψΩ (1, 0))
  have htime : Integrable (fun z => ρ z *
      (deriv (fun t => w t * Real.exp (-f (t, z.2))) z.1 +
        S z * (w z.1 * Real.exp (-f z))) * ψ z) ν := by
    have hi : Integrable (fun z =>
        ρ z * u z * (S z - n / (2 * z.1)) * ψ z -
          ρ z * u z * ψ z * fderiv ℝ f z (1, 0)) ν := by
      dsimp only [ν]
      rw [Measure.prod_restrict]
      exact htimeJoint.restrict
    apply hi.congr
    filter_upwards [hνdiff, hνmem] with z hz hzΩ
    have hwz : HasDerivAt w (-(n / (2 * z.1)) * w z.1) z.1 :=
      DifferentialGeometry.Analysis.Parabolic.Euclidean.hasDerivAt_gaussian_normalization n
        (zero_lt_one.trans (ha.trans hzΩ.1.1))
    have hfz := hz.hasFDerivAt.comp_hasDerivAt z.1
        ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    have huz := hwz.mul hfz.neg.exp
    change HasDerivAt (fun t => w t * Real.exp (-f (t, z.2))) _ z.1 at huz
    rw [huz.deriv]
    dsimp only [u, Pi.neg_apply, Function.comp_apply, id_eq]
    ring
  have htest : Integrable (fun z => ρ z * (w z.1 * Real.exp (-f z)) *
      deriv (fun t => ψ (t, z.2)) z.1) ν := by
    have hi : Integrable (fun z => ρ z * u z * fderiv ℝ ψ z (1, 0)) ν := by
      have hj := DifferentialGeometry.Analysis.integrable_weighted_test_fderiv_apply
        (μ := ν₀) hρuc hψ hψc hψΩ (1, 0)
      dsimp only [ν]
      rw [Measure.prod_restrict]
      exact hj.restrict
    apply hi.congr
    exact Eventually.of_forall fun z => by
      dsimp only
      rw [hsliceTime (hψdiff z)]
  exact ⟨hspace, htime, htest⟩


private theorem poleEndpoint_density_time_conditions
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c a' c' : ℝ} (ha : 1 < a) (haa : a < a') (hac : a' ≤ c')
    (x : P.M) {W : Set E} (hW : MeasurableSet W)
    (hWt : W ⊆ (extChartAt I x).target) :
    let n : ℝ := Module.finrank ℝ E
    let w : ℝ → ℝ := fun t => Real.exp (-(n / 2) * Real.log t -
      (n / 2) * Real.log (4 * Real.pi))
    let ρ : ℝ × E → ℝ := fun z => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let S : ℝ × E → ℝ := fun z => metricScalarAt (co.gInf (1 - z.1))
      ((extChartAt I x).symm z.2)
    let μ := (modelHaar (E := E)).restrict W
    (∀ᵐ y ∂μ, AbsolutelyContinuousOnInterval (fun t => ρ (t, y)) a' c') ∧
      (∀ᵐ y ∂μ, deriv (fun t => ρ (t, y)) =ᵐ[volume.restrict (uIoc a' c')]
        fun t => S (t, y) * ρ (t, y)) ∧
      (∀ z ∈ Ioo a c ×ˢ W, 0 ≤ w z.1) ∧
      LocallyLipschitzOn (Ioo a c ×ˢ W) (fun z => w z.1) ∧
      LocallyLipschitzOn (uIcc a' c') w ∧
      (∀ᵐ t ∂volume.restrict (uIoc a' c'), HasDerivAt w (-(n / (2 * t)) * w t) t) := by
  let n : ℝ := Module.finrank ℝ E
  let w : ℝ → ℝ := fun t => Real.exp (-(n / 2) * Real.log t -
    (n / 2) * Real.log (4 * Real.pi))
  let ρ : ℝ × E → ℝ := fun z => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S : ℝ × E → ℝ := fun z => metricScalarAt (co.gInf (1 - z.1))
    ((extChartAt I x).symm z.2)
  let μ := (modelHaar (E := E)).restrict W
  have hregY : Iio (0 : ℝ) ⊆ (Y).D.regular := fun _ ht => ht
  have hchart (y : E) (hy : y ∈ W) :
      (extChartAt I x).symm y ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet (I := I) x (hWt hy)
  have hrhoSmooth (y : E) (hy : y ∈ W) :
      ContDiffOn ℝ 1 (fun t => ρ (t, y)) (Icc a' c') := by
    have hs := contDiffOn_chartDensity Phi co hregY x (hchart y hy)
    exact (hs.comp (contDiffOn_const.sub contDiffOn_id) fun t ht =>
      sub_neg.mpr ((ha.trans haa).trans_le ht.1)).of_le (by simp)
  have hrho : ∀ᵐ y ∂μ,
      AbsolutelyContinuousOnInterval (fun t => ρ (t, y)) a' c' := by
    filter_upwards [ae_restrict_mem hW] with y hy
    apply LocallyLipschitzOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hac] using
      (hrhoSmooth y hy).locallyLipschitzOn (convex_Icc a' c')
  have hrhoDeriv : ∀ᵐ y ∂μ,
      deriv (fun t => ρ (t, y)) =ᵐ[volume.restrict (uIoc a' c')]
        fun t => S (t, y) * ρ (t, y) := by
    filter_upwards [ae_restrict_mem hW] with y hy
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htmem : t ∈ Ioc a' c' := by simpa only [uIoc_of_le hac] using ht
    exact (hasDerivAt_chartDensity_time_sub Phi co hregY (a := 1)
      ((ha.trans haa).trans htmem.1) x (hchart y hy)).deriv
  have hwAt {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 1 w t :=
    ((contDiffAt_const.mul (Real.contDiffAt_log.mpr ht.ne')).sub contDiffAt_const).exp
  have hw : ∀ z ∈ Ioo a c ×ˢ W, 0 ≤ w z.1 := fun _ _ => (Real.exp_pos _).le
  have hwLip : LocallyLipschitzOn (Ioo a c ×ˢ W) (fun z => w z.1) := by
    intro z hz
    have hzpos : 0 < z.1 := zero_lt_one.trans (ha.trans hz.1.1)
    have hs : ContDiffAt ℝ 1 (fun z : ℝ × E => w z.1) z :=
      (hwAt hzpos).comp z contDiffAt_fst
    obtain ⟨K, V, hV, hLip⟩ := hs.exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  have hwTime : LocallyLipschitzOn (uIcc a' c') w := by
    rw [uIcc_of_le hac]
    apply ContDiffOn.locallyLipschitzOn (convex_Icc a' c')
    intro t ht
    exact (hwAt (zero_lt_one.trans ((ha.trans haa).trans_le ht.1))).contDiffWithinAt
  have hwDeriv : ∀ᵐ t ∂volume.restrict (uIoc a' c'),
      HasDerivAt w (-(n / (2 * t)) * w t) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htmem : t ∈ Ioc a' c' := by simpa only [uIoc_of_le hac] using ht
    exact Analysis.Parabolic.Euclidean.hasDerivAt_gaussian_normalization n
      (zero_lt_one.trans ((ha.trans haa).trans htmem.1))
  exact ⟨hrho, hrhoDeriv, hw, hwLip, hwTime, hwDeriv⟩


theorem integral_poleEndpoint_redDensity_limit_subsolution_of_logarithmic_inequality
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (hlog : ∀ ψ : ℝ × E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ ψ z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * ψ z +
          B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ W) (hψnonneg : ∀ z, 0 ≤ ψ z) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let density := fun z => Real.exp (-f z - (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    0 ≤ ∫ z, ρ z * density z * (deriv (fun t => ψ (t, z.2)) z.1 +
      B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W) := by
  let Ω₀ : Set (ℝ × E) := Ioo a c ×ˢ W
  let Ω : Set (ℝ × E) := Ioo a' c' ×ˢ W
  let μ : Measure E := (modelHaar (E := E)).restrict W
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E => metricScalarAt (co.gInf (1 - z.1))
    ((extChartAt I x).symm z.2)
  let n : ℝ := Module.finrank ℝ E
  let w : ℝ → ℝ := fun t => Real.exp (-(n / 2) * Real.log t -
    (n / 2) * Real.log (4 * Real.pi))
  let c₀ : ℝ → ℝ := fun t => n / (2 * t)
  have hΩΩ₀ : Ω ⊆ Ω₀ := fun _ hz =>
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hz.2⟩
  have hf₀ : LocallyLipschitzOn Ω₀ f :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ).mono
        (fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have hfTime : ∀ᵐ y ∂μ, LocallyLipschitzOn (uIcc a' c') (fun t => f (t, y)) := by
    simpa only [uIcc_of_le hac] using
      ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice
        F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
        rho hrho ell hconv x hW.measurableSet hWt hWJ haa.le hcc.le
  have hfDiff : ∀ᵐ z ∂(volume.restrict (uIoc a' c')).prod μ,
      DifferentiableAt ℝ (fun t => f (t, z.2)) z.1 ∧
      DifferentiableAt ℝ (fun y => f (z.1, y)) z.2 := by
    simpa only [uIoc_of_le hac] using
      ae_differentiableAt_poleEndpoint_redLength_limit_slices
        F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
        rho hrho ell hconv x hW hWt hWJ haa hcc
  obtain ⟨hρTime, hρDeriv, hw, hwLip, hwTime, hwDeriv⟩ :=
    poleEndpoint_density_time_conditions F hcar hreg b hbmem tau q hsigma
      Phi R co (c := c) ha haa hac x hW.measurableSet hWt
  obtain ⟨hspace, htime, htest⟩ := poleEndpoint_density_transform_integrable
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha hbase
    rho hrho ell hconv x hW hWt hWJ haa hac hcc ψ hψ hψc hψsupp
  have hψBoundary : ∀ᵐ y ∂μ, ψ (a', y) = 0 ∧ ψ (c', y) = 0 := by
    apply Eventually.of_forall
    intro y
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a') (hψsupp h).1.1),
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl c') (hψsupp h).1.2)⟩
  have hweak (v : ℝ × E → ℝ) (hv : LocallyLipschitzOn Ω v)
      (hvc : HasCompactSupport v) (hvs : tsupport v ⊆ Ω) (hvn : ∀ z, 0 ≤ v z) :
      0 ≤ ∫ z, ρ z *
        ((deriv (fun t => f (t, z.2)) z.1 +
          B z (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2) - S z + c₀ z.1) * v z +
          B z (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => v (z.1, y)) z.2))
        ∂(volume.restrict (uIoc a' c')).prod μ := by
    simpa only [uIoc_of_le hac] using
      integral_poleEndpoint_logarithmic_residual_nonneg_of_smooth_tests
        F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
        hcomplete hboundary kappa hF p hJ ha hbase rho hrho ell hconv
        x hW hWt hWJ hlog haa hcc v hv hvc hvs hvn
  have hfinal := Analysis.integral_exp_neg_mul_time_deriv_add_cometric_nonneg
    (mu := μ) hac w c₀ f ρ S ψ B (fun z hz => hw z (hΩΩ₀ hz))
    (hwLip.mono hΩΩ₀) (hf₀.mono hΩΩ₀) hwTime hfTime hwDeriv hfDiff
    hρTime hρDeriv hψ hψc hψsupp hψnonneg hψBoundary
    (fun v hv hvc hvs hvn _ => hweak v hv hvc hvs hvn) hspace htime htest
  have hnorm (z : ℝ × E) : w z.1 * Real.exp (-f z) =
      Real.exp (-f z - n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi)) := by
    dsimp only [w]
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [uIoc_of_le hac, hnorm] using hfinal

theorem integrable_and_integral_poleEndpoint_redDensity_limit_subsolution_of_logarithmic_inequality
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (hlog : ∀ ψ : ℝ × E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ ψ z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * ψ z +
          B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (ψ : ℝ × E → ℝ) (hψ : LocallyLipschitzOn (Ioo a' c' ×ˢ W) ψ) (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ W) (hψnonneg : ∀ z, 0 ≤ ψ z) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let density := fun z => Real.exp (-f z - (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    Integrable (fun z => ρ z * density z * (deriv (fun t => ψ (t, z.2)) z.1 +
      B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2)))
      ((volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W)) ∧
    0 ≤ ∫ z, ρ z * density z * (deriv (fun t => ψ (t, z.2)) z.1 +
      B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W) := by
  let Ω₀ : Set (ℝ × E) := Ioo a c ×ˢ W
  let Ω : Set (ℝ × E) := Ioo a' c' ×ˢ W
  let ν₀ : Measure (ℝ × E) := (volume : Measure ℝ).prod (modelHaar (E := E))
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let density : ℝ × E → ℝ := fun z =>
    Real.exp (-f z - (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let w := fun z => ρ z * density z
  let π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ E)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hΩΩ₀ : Ω ⊆ Ω₀ := fun _ hz =>
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hz.2⟩
  have hf₀ : LocallyLipschitzOn Ω₀ f :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ).mono
        (fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have hf : LocallyLipschitzOn Ω f := hf₀.mono hΩΩ₀
  obtain ⟨hρ₀, _, hB₀⟩ := continuousOn_time_sub_chart_coefficients Phi R co
    rfl (fun _ ht => ht) ha x hWt
  have hρ : ContinuousOn ρ Ω := hρ₀.mono hΩΩ₀
  have hB : ContinuousOn B Ω := hB₀.mono hΩΩ₀
  have hdensity : ContinuousOn density Ω := by
    apply Real.continuous_exp.comp_continuousOn
    apply (hf.continuousOn.neg.sub
      (continuousOn_const.mul (continuous_fst.continuousOn.log fun z hz => ?_))).sub
        continuousOn_const
    exact ne_of_gt (zero_lt_one.trans ((ha.trans haa).trans hz.1.1))
  have hw : ContinuousOn w Ω := hρ.mul hdensity
  have hweak (v : ℝ × E → ℝ) (hv : ContDiff ℝ ∞ v)
      (hvc : HasCompactSupport v) (hvs : tsupport v ⊆ Ω) (hvn : ∀ z, 0 ≤ v z) :
      0 ≤ ∫ z, w z * (fderiv ℝ v z (1, 0) +
        B z (π (fderiv ℝ f z)) (π (fderiv ℝ v z))) ∂ν₀ := by
    have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
    have h := integral_poleEndpoint_redDensity_limit_subsolution_of_logarithmic_inequality
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
      hcomplete hboundary kappa hF p hJ ha hbase rho hrho ell hconv
      x hW hWt hWJ hlog haa hac hcc v hv1 hvc hvs hvn
    have heq := integral_weak_residual_eq_prod_restrict (μ := modelHaar (E := E))
      hW haa hcc hf₀ hv1.locallyLipschitz.locallyLipschitzOn hvs w
      (fun _ => 1) (fun _ _ => 0) B
    have heq' : (∫ z, w z * (fderiv ℝ v z (1, 0) +
        B z (π (fderiv ℝ f z)) (π (fderiv ℝ v z))) ∂ν₀) =
        ∫ z, w z * (deriv (fun t => v (t, z.2)) z.1 +
          B z (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => v (z.1, y)) z.2))
          ∂(volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W) := by
      simpa only [π, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
        one_mul, zero_mul, add_zero] using heq
    exact heq'.symm ▸ h
  obtain ⟨d, e, he⟩ := exists_measurePreserving_prod_modelHaar_euclidean (E := E)
  obtain ⟨hInt, hnonneg⟩ :=
    Analysis.integrable_and_integral_density_residual_nonneg_of_smooth_tests
      hΩ hf w B hw hB π ν₀ e he hweak hψ hψc hψsupp hψnonneg
  have hψ₀ : LocallyLipschitzOn Ω₀ ψ :=
    (hψ.locallyLipschitz_of_tsupport_subset hΩ hψsupp).locallyLipschitzOn
  refine ⟨?_, ?_⟩
  · exact integrable_density_residual_prod_restrict hW haa hcc hf₀ hψ₀ w B hInt
  · have heq := integral_weak_residual_eq_prod_restrict (μ := modelHaar (E := E))
      hW haa hcc hf₀ hψ₀ hψsupp w (fun _ => 1) (fun _ _ => 0) B
    have heq' : (∫ z, w z * (fderiv ℝ ψ z (1, 0) +
        B z (π (fderiv ℝ f z)) (π (fderiv ℝ ψ z))) ∂ν₀) =
        ∫ z, w z * (deriv (fun t => ψ (t, z.2)) z.1 +
          B z (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
          ∂(volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W) := by
      simpa only [π, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
        one_mul, zero_mul, add_zero] using heq
    exact heq' ▸ hnonneg

theorem integrable_poleEndpoint_redDensity_limit_chart_residual
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (ψ : ℝ × E → ℝ) (hψ : LocallyLipschitzOn (Ioo a' c' ×ˢ W) ψ) (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ W) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
      ((extChartAt I x).symm z.2)
    let density := fun z => Real.exp (-f z - (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    Integrable (fun z => ρ z * density z * (deriv (fun t => ψ (t, z.2)) z.1 +
      B z (d z) (fderiv ℝ (fun y => ψ (z.1, y)) z.2)))
      ((volume.restrict (Ioc a' c')).prod ((modelHaar (E := E)).restrict W)) := by
  let Ω₀ : Set (ℝ × E) := Ioo a c ×ˢ W
  let Ω : Set (ℝ × E) := Ioo a' c' ×ˢ W
  let ν₀ : Measure (ℝ × E) := (volume : Measure ℝ).prod (modelHaar (E := E))
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let ρ := fun z : ℝ × E => chartDensity (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let density : ℝ × E → ℝ := fun z =>
    Real.exp (-f z - (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let w := fun z => ρ z * density z
  let π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ E)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hΩΩ₀ : Ω ⊆ Ω₀ := fun _ hz =>
    ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hz.2⟩
  have hf₀ : LocallyLipschitzOn Ω₀ f :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ).mono
        (fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have hf : LocallyLipschitzOn Ω f := hf₀.mono hΩΩ₀
  obtain ⟨hρ₀, _, hB₀⟩ := continuousOn_time_sub_chart_coefficients Phi R co
    rfl (fun _ ht => ht) ha x hWt
  have hρ : ContinuousOn ρ Ω := hρ₀.mono hΩΩ₀
  have hB : ContinuousOn B Ω := hB₀.mono hΩΩ₀
  have hdensity : ContinuousOn density Ω := by
    apply Real.continuous_exp.comp_continuousOn
    apply (hf.continuousOn.neg.sub
      (continuousOn_const.mul (continuous_fst.continuousOn.log fun z hz => ?_))).sub
        continuousOn_const
    exact ne_of_gt (zero_lt_one.trans ((ha.trans haa).trans hz.1.1))
  have hw : ContinuousOn w Ω := hρ.mul hdensity
  have hInt := Analysis.integrable_density_residual
    hΩ hf w B hw hB π ν₀ hψ hψc hψsupp
  have hψ₀ : LocallyLipschitzOn Ω₀ ψ :=
    (hψ.locallyLipschitz_of_tsupport_subset hΩ hψsupp).locallyLipschitzOn
  exact integrable_density_residual_prod_restrict hW haa hcc hf₀ hψ₀ w B hInt

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
