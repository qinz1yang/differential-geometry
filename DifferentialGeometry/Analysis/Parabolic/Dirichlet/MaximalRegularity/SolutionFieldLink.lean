import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.SolutionSpace

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
  (perModeConvolutionL2_eq_toFunL2)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}
variable {a T : ℝ}

private theorem solModeCoeff_eq_integral (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    (fun t => solModeCoeff (a := a) hT f i t) =ᵐ[timeMeasure T]
      fun t => ∫ s in (0 : ℝ)..t, derivModeCoeff (a := a) hT f i s := by
  have hsol : solModeCoeff (a := a) hT f i =
      TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ)
          (derivModeCoeff (a := a) hT f i)) := by
    rw [solModeCoeff, derivModeCoeff,
      perModeConvolutionL2_eq_toFunL2 (dirichletLaplacianEigenvalue i)
        (dirichletLaplacianEigenvalue_nonneg i) hT
        (timeModeCoeff f i)]
  rw [hsol]
  have hcoe := TimeSobolev.coeFn_ofContinuousOn
    (TimeSobolev.timeH1.mk (0 : ℝ)
      (derivModeCoeff (a := a) hT f i)).continuousOn_toFun
  refine hcoe.trans ?_
  filter_upwards [] with t
  rw [TimeSobolev.timeH1.toFun_apply, TimeSobolev.timeH1.initial_mk,
    TimeSobolev.timeH1.deriv_mk, zero_add]

private theorem maximalRegularityOp_deriv_coeff_ae
    (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
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
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
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
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
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
    (f : timeL2 (DirichletHs g a) T) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 2 by linarith)
        (maximalRegularitySolField a hT.le f t))
      =ᵐ[timeMeasure T]
        (maximalRegularityOp a hT f).toFun := by
  set u := maximalRegularityOp a hT f with hu_def
  have hper : ∀ i : DirichletLaplacianEigenIndex g,
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
        u.initial.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i =
          dirichletHsCoeffL i (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.initial.coeff i = 0 := by
      rw [hu_def]
      rfl
    rw [htfield, hval, hinit, zero_add]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine DirichletHs.ext ?_
  funext i
  rw [DirichletHs.dirichletHsInclusion_coeff]
  exact ht i

theorem maximalRegularitySolFieldHa1_toFun_ae
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (DirichletHs g a) T) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 1 by linarith)
        (maximalRegularitySolFieldHa1 a hT f t))
      =ᵐ[timeMeasure T]
        (maximalRegularityOp a hT f).toFun := by
  set u := maximalRegularityOp a hT f with hu_def
  have hper : ∀ i : DirichletLaplacianEigenIndex g,
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
        u.initial.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i =
          dirichletHsCoeffL i (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.initial.coeff i = 0 := by
      rw [hu_def]
      rfl
    rw [htfield, hval, hinit, zero_add]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine DirichletHs.ext ?_
  funext i
  rw [DirichletHs.dirichletHsInclusion_coeff]
  exact ht i

private theorem homogeneousModeCoeff_eq_init_add_integral
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    (fun t => homogeneousModeCoeff (a := a) (T := T) u₀ i t)
      =ᵐ[timeMeasure T] fun t => u₀.coeff i +
        ∫ s in (0 : ℝ)..t,
          homogeneousDerivModeCoeff (a := a) (T := T) u₀ i s := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  set c := u₀.coeff i with hc_def
  have hmode : homogeneousModeCoeff (a := a) (T := T) u₀ i
      =ᵐ[timeMeasure T] fun t => Real.exp (-lam * t) * c :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hderiv : homogeneousDerivModeCoeff (a := a) (T := T) u₀ i
      =ᵐ[timeMeasure T] fun t =>
        -lam * (Real.exp (-lam * t) * c) :=
    TimeSobolev.coeFn_ofContinuousOn _
  filter_upwards [hmode,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht htmem
  rw [ht]
  have hint_congr :
      (∫ s in (0 : ℝ)..t,
          homogeneousDerivModeCoeff (a := a) (T := T) u₀ i s) =
        ∫ s in (0 : ℝ)..t,
          -lam * (Real.exp (-lam * s) * c) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans
        (uIcc_subset_Icc ⟨le_rfl, htmem.1.trans htmem.2⟩ htmem)
    have hae := ae_restrict_of_ae_restrict_of_subset
      (μ := volume) hsub hderiv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with s hs using hs
  rw [hint_congr]
  have hF : ∀ s : ℝ, HasDerivAt (fun s => Real.exp (-lam * s) * c)
      (Real.exp (-lam * s) * (-lam) * c) s := by
    intro s
    have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) s := by
      simpa using (hasDerivAt_id s).const_mul (-lam)
    exact hlin.exp.mul_const c
  have hderivFun : (fun s : ℝ => -lam * (Real.exp (-lam * s) * c)) =
      fun s => Real.exp (-lam * s) * (-lam) * c := by
    funext s
    ring
  rw [hderivFun,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hF s) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero, one_mul]
  ring

private theorem maximalRegularityHomogeneousDerivField_coeff_ae
    (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    (fun s =>
      ((maximalRegularityHomogeneous a T u₀).deriv s).coeff i)
      =ᵐ[timeMeasure T] fun s =>
        homogeneousDerivModeCoeff (a := a) (T := T) u₀ i s := by
  have hcoe := timeModeCoeff_coeFn
    (maximalRegularityHomogeneous a T u₀).deriv i
  have hmode : timeModeCoeff
      (maximalRegularityHomogeneous a T u₀).deriv i =
        homogeneousDerivModeCoeff (a := a) (T := T) u₀ i := by
    rw [maximalRegularityHomogeneous_deriv,
      maximalRegularityHomogeneousDerivField_timeModeCoeff hT u₀ i]
  filter_upwards [hcoe] with s hs
  rw [← hs, hmode]

private theorem maximalRegularityHomogeneousSolField_coeff_ae
    (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    (fun t => (maximalRegularityHomogeneousSolField a T u₀ t).coeff i)
      =ᵐ[timeMeasure T] fun t => u₀.coeff i +
        ∫ s in (0 : ℝ)..t,
          ((maximalRegularityHomogeneous a T u₀).deriv s).coeff i := by
  have hfield := timeModeCoeff_coeFn
    (maximalRegularityHomogeneousSolField a T u₀) i
  have hsol := homogeneousModeCoeff_eq_init_add_integral
    (a := a) (T := T) u₀ i
  have hderiv := maximalRegularityHomogeneousDerivField_coeff_ae
    (a := a) (T := T) hT.le u₀ i
  filter_upwards [hfield, hsol,
    ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t htfield htsol htmem
  rw [← htfield,
    maximalRegularityHomogeneousSolField_timeModeCoeff hT.le u₀ i,
    htsol]
  refine congrArg (fun z => u₀.coeff i + z)
    (intervalIntegral.integral_congr_ae ?_)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_rfl, htmem.1.trans htmem.2⟩
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 htmem)
  have hae := ae_restrict_of_ae_restrict_of_subset
    (μ := volume) hsub hderiv
  rw [ae_restrict_iff' measurableSet_uIoc] at hae
  filter_upwards [hae] with s hs hsmem
  rw [hs hsmem]

private theorem maximalRegularityHomogeneousSolFieldHa1_coeff_ae
    (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    (fun t => (maximalRegularityHomogeneousSolFieldHa1 a T u₀ t).coeff i)
      =ᵐ[timeMeasure T] fun t => u₀.coeff i +
        ∫ s in (0 : ℝ)..t,
          ((maximalRegularityHomogeneous a T u₀).deriv s).coeff i := by
  have hfield := timeModeCoeff_coeFn
    (maximalRegularityHomogeneousSolFieldHa1 a T u₀) i
  have hsol := homogeneousModeCoeff_eq_init_add_integral
    (a := a) (T := T) u₀ i
  have hderiv := maximalRegularityHomogeneousDerivField_coeff_ae
    (a := a) (T := T) hT.le u₀ i
  filter_upwards [hfield, hsol,
    ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t htfield htsol htmem
  rw [← htfield,
    maximalRegularityHomogeneousSolFieldHa1_timeModeCoeff hT.le u₀ i,
    htsol]
  refine congrArg (fun z => u₀.coeff i + z)
    (intervalIntegral.integral_congr_ae ?_)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_rfl, htmem.1.trans htmem.2⟩
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 htmem)
  have hae := ae_restrict_of_ae_restrict_of_subset
    (μ := volume) hsub hderiv
  rw [ae_restrict_iff' measurableSet_uIoc] at hae
  filter_upwards [hae] with s hs hsmem
  rw [hs hsmem]

theorem maximalRegularityHomogeneousSolField_toFun_ae
    (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1)) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 2 by linarith)
        (maximalRegularityHomogeneousSolField a T u₀ t))
      =ᵐ[timeMeasure T]
        (maximalRegularityHomogeneous a T u₀).toFun := by
  set u := maximalRegularityHomogeneous a T u₀ with hu_def
  have hper : ∀ i : DirichletLaplacianEigenIndex g,
      ∀ᵐ t ∂(timeMeasure T),
        (maximalRegularityHomogeneousSolField a T u₀ t).coeff i =
          (u.toFun t).coeff i := by
    intro i
    have hfield := maximalRegularityHomogeneousSolField_coeff_ae
      (a := a) hT u₀ i
    filter_upwards [hfield,
      ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htfield htmem
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_rfl, htmem.1.trans htmem.2⟩
    have hcomm :
        dirichletHsCoeffL i (∫ τ in (0 : ℝ)..t, u.deriv τ) =
          ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (dirichletHsCoeffL i) (u.intervalIntegrable_deriv h0 htmem)]
      rfl
    have hval : (u.toFun t).coeff i =
        u.initial.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i = dirichletHsCoeffL i (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.initial.coeff i = u₀.coeff i := by
      rw [hu_def, maximalRegularityHomogeneous_init]
      rfl
    rw [htfield, hval, hinit]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine DirichletHs.ext ?_
  funext i
  rw [DirichletHs.dirichletHsInclusion_coeff]
  exact ht i

theorem maximalRegularityHomogeneousSolFieldHa1_toFun_ae
    (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1)) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 1 by linarith)
        (maximalRegularityHomogeneousSolFieldHa1 a T u₀ t))
      =ᵐ[timeMeasure T]
        (maximalRegularityHomogeneous a T u₀).toFun := by
  set u := maximalRegularityHomogeneous a T u₀ with hu_def
  have hper : ∀ i : DirichletLaplacianEigenIndex g,
      ∀ᵐ t ∂(timeMeasure T),
        (maximalRegularityHomogeneousSolFieldHa1 a T u₀ t).coeff i =
          (u.toFun t).coeff i := by
    intro i
    have hfield := maximalRegularityHomogeneousSolFieldHa1_coeff_ae
      (a := a) hT u₀ i
    filter_upwards [hfield,
      ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htfield htmem
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_rfl, htmem.1.trans htmem.2⟩
    have hcomm :
        dirichletHsCoeffL i (∫ τ in (0 : ℝ)..t, u.deriv τ) =
          ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (dirichletHsCoeffL i) (u.intervalIntegrable_deriv h0 htmem)]
      rfl
    have hval : (u.toFun t).coeff i =
        u.initial.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i = dirichletHsCoeffL i (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.initial.coeff i = u₀.coeff i := by
      rw [hu_def, maximalRegularityHomogeneous_init]
      rfl
    rw [htfield, hval, hinit]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine DirichletHs.ext ?_
  funext i
  rw [DirichletHs.dirichletHsInclusion_coeff]
  exact ht i

theorem maximalRegularityDuhamelSolField_toFun_ae
    (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolField a hT u₀ f t))
      =ᵐ[timeMeasure T]
        (maximalRegularityDuhamelMap a hT u₀ f).toFun := by
  have hhom := maximalRegularityHomogeneousSolField_toFun_ae
    (a := a) hT u₀
  have hforce := maximalRegularitySolField_toFun_ae
    (a := a) hT f
  have hadd := Lp.coeFn_add
    (maximalRegularityHomogeneousSolField a T u₀)
    (maximalRegularitySolField a hT.le f)
  filter_upwards [hhom, hforce, hadd,
    ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t hhomt hforcet haddt htmem
  rw [maximalRegularityDuhamelSolField, haddt, Pi.add_apply, map_add,
    maximalRegularityDuhamelMap,
    TimeSobolev.timeH1.toFun_add _ _ htmem, hhomt, hforcet]

theorem maximalRegularityDuhamelSolFieldHa1_toFun_ae
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    (fun t => dirichletHsInclusion
        (show a ≤ a + 1 by linarith)
        (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f t))
      =ᵐ[timeMeasure T]
        (maximalRegularityDuhamelMap a hT u₀ f).toFun := by
  have hhom := maximalRegularityHomogeneousSolFieldHa1_toFun_ae
    (a := a) hT u₀
  have hforce := maximalRegularitySolFieldHa1_toFun_ae
    (a := a) hT hT1 f
  have hadd := Lp.coeFn_add
    (maximalRegularityHomogeneousSolFieldHa1 a T u₀)
    (maximalRegularitySolFieldHa1 a hT f)
  filter_upwards [hhom, hforce, hadd,
    ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t hhomt hforcet haddt htmem
  rw [maximalRegularityDuhamelSolFieldHa1, haddt, Pi.add_apply, map_add,
    maximalRegularityDuhamelMap,
    TimeSobolev.timeH1.toFun_add _ _ htmem, hhomt, hforcet]

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
