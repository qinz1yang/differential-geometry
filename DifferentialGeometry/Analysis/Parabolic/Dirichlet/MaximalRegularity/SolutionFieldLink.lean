import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.OperatorEquation

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Dirichlet
namespace MaximalRegularity

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
  (perModeConvL2_eq_toFunL2)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}
variable {a T : ℝ}

private theorem solModeCoeff_eq_integral (hT : 0 ≤ T)
    (f : timeL2 (dirichletHs g a) T)
    (i : DirichletLaplacianEigenindex g) :
    (fun t => solModeCoeff (a := a) hT f i t) =ᵐ[timeMeasure T]
      fun t => ∫ s in (0 : ℝ)..t, derivModeCoeff (a := a) hT f i s := by
  have hsol : solModeCoeff (a := a) hT f i =
      TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ)
          (derivModeCoeff (a := a) hT f i)) := by
    rw [solModeCoeff, derivModeCoeff,
      perModeConvL2_eq_toFunL2 (dirichletLaplacianEigenvalue i)
        (dirichletLaplacianEigenvalue_nonneg i) hT
        (timeModeCoeff f i)]
  rw [hsol]
  have hcoe := TimeSobolev.coeFn_ofContinuousOn
    (TimeSobolev.timeH1.mk (0 : ℝ)
      (derivModeCoeff (a := a) hT f i)).continuousOn_toFun
  refine hcoe.trans ?_
  filter_upwards [] with t
  rw [TimeSobolev.timeH1.toFun_apply, TimeSobolev.timeH1.init_mk,
    TimeSobolev.timeH1.deriv_mk, zero_add]

private theorem maximalRegularityOp_deriv_coeff_ae
    (hT : 0 < T)
    (f : timeL2 (dirichletHs g a) T)
    (i : DirichletLaplacianEigenindex g) :
    (fun s => ((maximalRegularityOp a hT f).deriv s).coeff i)
      =ᵐ[timeMeasure T]
        fun s => derivModeCoeff (a := a) hT.le f i s := by
  have hcoe := timeModeCoeff_coeFn
    (maximalRegularityOp a hT f).deriv i
  have hmode : timeModeCoeff
      (maximalRegularityOp a hT f).deriv i =
        derivModeCoeff (a := a) hT.le f i := by
    rw [show (maximalRegularityOp a hT f).deriv =
        maximalRegularityDerivField a hT.le f from rfl,
      maximalRegularityDerivField_timeModeCoeff
        (a := a) hT.le f i]
  filter_upwards [hcoe] with s hs
  rw [← hs, hmode]

private theorem maximalRegularitySolField_coeff_ae
    (hT : 0 < T)
    (f : timeL2 (dirichletHs g a) T)
    (i : DirichletLaplacianEigenindex g) :
    (fun t => (maximalRegularitySolField a hT.le f t).coeff i)
      =ᵐ[timeMeasure T]
        fun t => ∫ s in (0 : ℝ)..t,
          ((maximalRegularityOp a hT f).deriv s).coeff i := by
  have hfield := timeModeCoeff_coeFn
    (maximalRegularitySolField a hT.le f) i
  have hsol := solModeCoeff_eq_integral (a := a) hT.le f i
  have hderiv := maximalRegularityOp_deriv_coeff_ae
    (a := a) hT f i
  filter_upwards [hfield, hsol,
    ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t htfield htsol htmem
  rw [← htfield,
    maximalRegularitySolField_timeModeCoeff
      (a := a) hT.le f i, htsol]
  refine intervalIntegral.integral_congr_ae ?_
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_rfl, htmem.1.trans htmem.2⟩
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 htmem)
  have hae := ae_restrict_of_ae_restrict_of_subset
    (μ := volume) hsub hderiv
  rw [ae_restrict_iff' measurableSet_uIoc] at hae
  filter_upwards [hae] with s hs hsmem
  rw [hs hsmem]

private theorem maximalRegularitySolFieldHa1_coeff_ae
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (dirichletHs g a) T)
    (i : DirichletLaplacianEigenindex g) :
    (fun t => (maximalRegularitySolFieldHa1 a hT f t).coeff i)
      =ᵐ[timeMeasure T]
        fun t => ∫ s in (0 : ℝ)..t,
          ((maximalRegularityOp a hT f).deriv s).coeff i := by
  have hfield := timeModeCoeff_coeFn
    (maximalRegularitySolFieldHa1 a hT f) i
  have hsol := solModeCoeff_eq_integral (a := a) hT.le f i
  have hderiv := maximalRegularityOp_deriv_coeff_ae
    (a := a) hT f i
  filter_upwards [hfield, hsol,
    ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t htfield htsol htmem
  rw [← htfield,
    maximalRegularitySolFieldHa1_timeModeCoeff
      (a := a) hT hT1 f i, htsol]
  refine intervalIntegral.integral_congr_ae ?_
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_rfl, htmem.1.trans htmem.2⟩
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 htmem)
  have hae := ae_restrict_of_ae_restrict_of_subset
    (μ := volume) hsub hderiv
  rw [ae_restrict_iff' measurableSet_uIoc] at hae
  filter_upwards [hae] with s hs hsmem
  rw [hs hsmem]

theorem maximalRegularitySolField_toFun_ae
    (hT : 0 < T)
    (f : timeL2 (dirichletHs g a) T) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 2 by linarith)
        (maximalRegularitySolField a hT.le f t))
      =ᵐ[timeMeasure T]
        (maximalRegularityOp a hT f).toFun := by
  set u := maximalRegularityOp a hT f with hu_def
  have hper : ∀ i : DirichletLaplacianEigenindex g,
      ∀ᵐ t ∂(timeMeasure T),
        (maximalRegularitySolField a hT.le f t).coeff i =
          (u.toFun t).coeff i := by
    intro i
    have hfield := maximalRegularitySolField_coeff_ae
      (a := a) hT f i
    filter_upwards [hfield,
      ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htfield htmem
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_rfl, htmem.1.trans htmem.2⟩
    have hcomm :
        dirichletHsCoeffL i (∫ τ in (0 : ℝ)..t, u.deriv τ) =
          ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (dirichletHsCoeffL i)
        (u.intervalIntegrable_deriv h0 htmem)]
      rfl
    have hval : (u.toFun t).coeff i =
        u.init.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i =
          dirichletHsCoeffL i (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.init.coeff i = 0 := by
      rw [hu_def]
      rfl
    rw [htfield, hval, hinit, zero_add]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine dirichletHs.ext ?_
  funext i
  rw [dirichletHs.dirichletHsInclusion_coeff]
  exact ht i

theorem maximalRegularitySolFieldHa1_toFun_ae
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (dirichletHs g a) T) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 1 by linarith)
        (maximalRegularitySolFieldHa1 a hT f t))
      =ᵐ[timeMeasure T]
        (maximalRegularityOp a hT f).toFun := by
  set u := maximalRegularityOp a hT f with hu_def
  have hper : ∀ i : DirichletLaplacianEigenindex g,
      ∀ᵐ t ∂(timeMeasure T),
        (maximalRegularitySolFieldHa1 a hT f t).coeff i =
          (u.toFun t).coeff i := by
    intro i
    have hfield := maximalRegularitySolFieldHa1_coeff_ae
      (a := a) hT hT1 f i
    filter_upwards [hfield,
      ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htfield htmem
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_rfl, htmem.1.trans htmem.2⟩
    have hcomm :
        dirichletHsCoeffL i (∫ τ in (0 : ℝ)..t, u.deriv τ) =
          ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (dirichletHsCoeffL i)
        (u.intervalIntegrable_deriv h0 htmem)]
      rfl
    have hval : (u.toFun t).coeff i =
        u.init.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i =
          dirichletHsCoeffL i (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.init.coeff i = 0 := by
      rw [hu_def]
      rfl
    rw [htfield, hval, hinit, zero_add]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine dirichletHs.ext ?_
  funext i
  rw [dirichletHs.dirichletHsInclusion_coeff]
  exact ht i

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
