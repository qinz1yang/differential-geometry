import DifferentialGeometry.Analysis.Parabolic.WeakEquation.GaussianCoordinates
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.WeightedFlux
import DifferentialGeometry.Analysis.Sobolev.Euclidean.GaussianSpatialDerivative
import DifferentialGeometry.Analysis.Calculus.GaussianNormalization
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.WeightedSpatialLp
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "V" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
private theorem deriv_time_slice_eq_fderiv
    {φ : ℝ × V → ℝ} {q : ℝ × V} (hφ : DifferentiableAt ℝ φ q) :
    deriv (fun t => φ (t, q.2)) q.1 = fderiv ℝ φ q (1, 0) := by
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using
    (hφ.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)).hasDerivAt.deriv

omit [FiniteDimensional ℝ E] in
private theorem fderiv_spatial_slice_eq_fderiv
    {φ : ℝ × V → ℝ} {q : ℝ × V} (hφ : DifferentiableAt ℝ φ q) (v : V) :
    fderiv ℝ (fun y => φ (q.1, y)) q.2 v = fderiv ℝ φ q (0, v) := by
  have heq : fderiv ℝ (fun y => φ (q.1, y)) q.2 =
      (fderiv ℝ φ q).comp (ContinuousLinearMap.inr ℝ ℝ V) :=
    (hφ.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)).fderiv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
    congrArg (fun L : V →L[ℝ] ℝ => L v) heq

theorem integral_time_derivative_eq_weighted_flux_of_chartGaussianResidual_eq_zero
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    (f u : ℝ × E → ℝ) {Ω : Set V} (hΩ : MeasurableSet Ω)
    (hΩt : Ω ⊆ chartTargetEuclid (I := I) α)
    (a b : ℝ) (φ : ℝ × V → ℝ) (hφ : Differentiable ℝ φ) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    let ψ : ℝ × E → ℝ := fun z => φ (z.1, (toEuclidean (E := E)) z.2)
    let fV : ℝ × V → ℝ := fun q => f (q.1, (toEuclidean (E := E)).symm q.2)
    let uV : ℝ × V → ℝ := fun q => u (q.1, (toEuclidean (E := E)).symm q.2)
    (∀ i, (fun q => fderiv ℝ (fun y => uV (q.1, y)) q.2
      (EuclideanSpace.single i 1)) =ᵐ[ν] fun q => -uV q *
        fderiv ℝ (fun y => fV (q.1, y)) q.2 (EuclideanSpace.single i 1)) →
    Integrable (fun q => densityOnEuclid (g q.1) α q.2 * uV q *
      fderiv ℝ φ q (1, 0)) ν →
    (∀ j, Integrable (fun q => (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 *
      fderiv ℝ (fun y => uV (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1)) ν) →
    (∫ z, chartDensity (g z.1) α ((extChartAt I α).symm z.2) * u z *
      (deriv (fun t => ψ (t, z.2)) z.1 +
        chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume.restrict (Ioc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0 →
    (∫ q, densityOnEuclid (g q.1) α q.2 * uV q * fderiv ℝ φ q (1, 0) ∂ν) =
      ∑ j, ∫ q, (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 *
        fderiv ℝ (fun y => uV (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
  intro ν ψ fV uV hgradient htime hflux hzero
  have hzeroV :=
    (integral_chartGaussianResidual_eq_toEuclidean g α f u Ω a b φ).symm.trans hzero
  have hmem : ∀ᵐ q ∂ν, q.2 ∈ Ω := by
    exact (Measure.ae_prod_iff_ae_ae (p := fun q : ℝ × V => q.2 ∈ Ω)
      (hΩ.preimage measurable_snd)).2 (Filter.Eventually.of_forall fun _ =>
        ae_restrict_mem hΩ)
  have hresidual :
      (∫ q, densityOnEuclid (g q.1) α q.2 * uV q *
        (fderiv ℝ φ q (1, 0) + ∑ j, ∑ i, invGramOnEuclid (g q.1) α i j q.2 *
          fderiv ℝ (fun y => fV (q.1, y)) q.2 (EuclideanSpace.single i 1) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1)) ∂ν) = 0 := by
    calc
      _ = ∫ q, densityOnEuclid (g q.1) α q.2 * uV q *
          (deriv (fun t => φ (t, q.2)) q.1 +
            ∑ j, ∑ i, invGramOnEuclid (g q.1) α j i q.2 *
              fderiv ℝ (fun y => fV (q.1, y)) q.2 (EuclideanSpace.single i 1) *
              fderiv ℝ (fun y => φ (q.1, y)) q.2 (EuclideanSpace.single j 1)) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hmem] with q hq
        rw [deriv_time_slice_eq_fderiv (hφ q)]
        congr 2
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [fderiv_spatial_slice_eq_fderiv (hφ q),
          invGramOnEuclid_symm_of_mem (g q.1) α j i (hΩt hq)]
      _ = 0 := hzeroV
  simpa only [weightedInvGramOnEuclid] using
    (integral_weighted_flux_eq_of_residual_eq_zero (μ := ν)
      (u := uV) (w := fun q => densityOnEuclid (g q.1) α q.2)
      (timeDerivative := fun q => fderiv ℝ φ q (1, 0))
      (A := fun q i j => invGramOnEuclid (g q.1) α i j q.2)
      (du := fun i q => fderiv ℝ (fun y => uV (q.1, y)) q.2
        (EuclideanSpace.single i 1))
      (df := fun i q => fderiv ℝ (fun y => fV (q.1, y)) q.2
        (EuclideanSpace.single i 1))
      (testGradient := fun j q => fderiv ℝ φ q (0, EuclideanSpace.single j 1))
      (ae_all_iff.mpr hgradient) htime
      (by simpa only [weightedInvGramOnEuclid] using hflux) hresidual)


theorem exists_lp_weak_equation_exp_gaussian_of_chartResidual_eq_zero
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (α : M)
    {a b : ℝ} (ha : 0 < a) (hreg : Icc a b ⊆ D.regular)
    {Ω : Set V} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : closure Ω ⊆ chartTargetEuclid (I := I) α)
    (f : ℝ × E → ℝ) (n : ℝ)
    (hf : LocallyLipschitzOn (Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => f (q.1, (toEuclidean (E := E)).symm q.2))) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    let u : ℝ × E → ℝ := fun z => Real.exp (-f z - n / 2 * Real.log z.1 -
      n / 2 * Real.log (4 * Real.pi))
    let uV : ℝ × V → ℝ := fun q => u (q.1, (toEuclidean (E := E)).symm q.2)
    (∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) →
      (∫ z, chartDensity (g z.1) α ((extChartAt I α).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume.restrict (Ioc a b)).prod
          ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0) →
    ∃ U : Lp ℝ 2 ν, ∃ K : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν,
      (U =ᵐ[ν] uV) ∧
      (∀ i, K i =ᵐ[ν] fun q => fderiv ℝ (fun y => uV (q.1, y)) q.2
        (EuclideanSpace.single i 1)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Icc a b),
        DeGiorgi.HasWeakPartialDeriv i (fun y => K i (t, y)) (fun y => U (t, y)) Ω) ∧
      ∀ φ : ℝ × V → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, densityOnEuclid (g q.1) α q.2 * U q * fderiv ℝ φ q (1, 0) ∂ν) =
          ∑ j, ∫ q, (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
  intro ν u uV hresidual
  let fV : ℝ × V → ℝ := fun q => f (q.1, (toEuclidean (E := E)).symm q.2)
  have hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) uV :=
    locallyLipschitzOn_exp_gaussian_normalization ha hf n
  have hgradient (i : Fin (Module.finrank ℝ E)) :
      (fun q => fderiv ℝ (fun y => uV (q.1, y)) q.2
        (EuclideanSpace.single i 1)) =ᵐ[ν]
      fun q => -uV q * fderiv ℝ (fun y => fV (q.1, y)) q.2
        (EuclideanSpace.single i 1) :=
    spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn ha hΩ hΩc hf n i
  let G : MetricConnectionFamilyOn (I := I) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContinuousOn (fun q : ℝ × V => densityOnEuclid (g q.1) α q.2)
      (Icc a b ×ˢ closure Ω) :=
    (densityOnEuclid_family_continuousOn (G := G) hg hreg α).mono
      (prod_mono Subset.rfl hΩt)
  have hA (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun q : ℝ × V => invGramOnEuclid (g q.1) α i j q.2)
        (Icc a b ×ˢ closure Ω) :=
    (invGramOnEuclid_family_continuousOn (G := G) hg hreg α i j).mono
      (prod_mono Subset.rfl hΩt)
  obtain ⟨U, K, hU, hK, hspatial⟩ :=
    exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn hΩ hΩc hu 2
  refine ⟨U, K, hU, hK, hspatial, ?_⟩
  intro φ hφ hφc hφs
  let T : (ℝ × E) ≃L[ℝ] (ℝ × V) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := E))
  let ψ : ℝ × E → ℝ := φ ∘ T
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp T.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph T.toHomeomorph
  have hψs : tsupport ψ ⊆ Ioo a b ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) := by
    intro z hz
    exact hφs (tsupport_comp_subset_preimage φ T.continuous hz)
  obtain ⟨htime, hflux⟩ :=
    integrable_weighted_fderiv_pairings_of_locallyLipschitzOn hΩ hΩc hu hρ hA
      (hφ.of_le (by simp))
  have hweak :=
    integral_time_derivative_eq_weighted_flux_of_chartGaussianResidual_eq_zero g α f u
      hΩ.measurableSet (fun y hy => hΩt (subset_closure hy)) a b φ
      (hφ.differentiable (by simp)) hgradient htime
      (by simpa only [weightedInvGramOnEuclid] using hflux)
      (hresidual ψ hψ hψc hψs)
  calc
    _ = ∫ q, densityOnEuclid (g q.1) α q.2 * uV q * fderiv ℝ φ q (1, 0) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hU] with q hq
      rw [hq]
    _ = ∑ j, ∫ q, (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 *
        fderiv ℝ (fun y => uV (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := hweak
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hK] with q hq
      simp only [hq]

end DifferentialGeometry.Analysis.Parabolic
