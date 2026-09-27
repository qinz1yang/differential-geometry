import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

omit [NeZero (Module.finrank ℝ E)] in
theorem homModeCoeff_eq_initial_add_integral
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) t) =ᵐ[timeMeasure T]
      fun t => u₀.coeff i + ∫ s in (0 : ℝ)..t,
        (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set c := u₀.coeff i with hc_def
  have hmode : ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-lam * t) * c :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hderiv : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => -lam * (Real.exp (-lam * t) * c) :=
    TimeSobolev.coeFn_ofContinuousOn _
  filter_upwards [hmode, ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht htmem
  rw [ht]
  have hint_congr : (∫ s in (0 : ℝ)..t,
        (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s) =
      ∫ s in (0 : ℝ)..t, -lam * (Real.exp (-lam * s) * c) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc ⟨le_rfl, htmem.1.trans htmem.2⟩ htmem)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with s hs using hs
  rw [hint_congr]
  have hF : ∀ s : ℝ, HasDerivAt (fun s => Real.exp (-lam * s) * c)
      (Real.exp (-lam * s) * (-lam) * c) s := by
    intro s
    have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) s := by
      simpa using (hasDerivAt_id s).const_mul (-lam)
    have hexp : HasDerivAt (fun s => Real.exp (-lam * s))
        (Real.exp (-lam * s) * (-lam)) s := hlin.exp
    exact hexp.mul_const c
  have hderivFun : (fun s : ℝ => -lam * (Real.exp (-lam * s) * c)) =
      fun s : ℝ => Real.exp (-lam * s) * (-lam) * c := by
    funext s
    ring
  rw [hderivFun]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
    (by
      apply Continuous.intervalIntegrable
      fun_prop)]
  simp only [mul_zero, Real.exp_zero, one_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem solutionModeCoeff_eq_integral (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => (solutionModeCoeff (I := I) (M := M) (a := a) hT f i) t) =ᵐ[timeMeasure T]
      fun t => ∫ s in (0 : ℝ)..t,
        (derivModeCoeff (I := I) (M := M) (a := a) hT f i) s := by
  have hsol : solutionModeCoeff (I := I) (M := M) (a := a) hT f i =
      TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ)
          (derivModeCoeff (I := I) (M := M) (a := a) hT f i)) := by
    rw [solutionModeCoeff, derivModeCoeff,
      perModeConvolutionL2_eq_toFunL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
        (tensor_lambda_nonneg (I := I) (M := M) i) hT
        (timeModeCoeff (I := I) (M := M) f i)]
  rw [hsol]
  have hcoe := TimeSobolev.coeFn_ofContinuousOn
    (TimeSobolev.timeH1.mk (0 : ℝ)
      (derivModeCoeff (I := I) (M := M) (a := a) hT f i)).continuousOn_toFun
  refine hcoe.trans ?_
  filter_upwards [] with t
  rw [TimeSobolev.timeH1.toFun_apply, TimeSobolev.timeH1.initial_mk,
    TimeSobolev.timeH1.deriv_mk, zero_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelMap_deriv_coeff_ae (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun s => ((maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv s).coeff i)
        =ᵐ[timeMeasure T]
      fun s => (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s +
        (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s := by
  have hderiv := maximalRegularityDuhamelMap_deriv (I := I) (M := M) (a := a) (T := T)
    hT u₀ gforce
  have hcoe := timeModeCoeff_coeFn (I := I) (M := M)
    (maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv i
  have hhom := timeModeCoeff_coeFn (I := I) (M := M)
    (maximalRegularityHomogeneousDerivField (I := I) (M := M) a T u₀) i
  have hduh := timeModeCoeff_coeFn (I := I) (M := M)
    (maximalRegularityDerivField (I := I) (M := M) a hT.le gforce) i
  have hsum : timeModeCoeff (I := I) (M := M)
      (maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv i =
        homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i +
          derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i := by
    rw [hderiv, timeModeCoeff_add (I := I) (M := M),
      maximalRegularityHomogeneousDerivField_timeModeCoeff (I := I) (M := M) (a := a)
        (T := T) hT.le u₀ i,
      maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
        (h_compact := h_compact) (a := a) hT.le gforce i]
  have haddcoe := Lp.coeFn_add
    (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
    (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)
  filter_upwards [hcoe, haddcoe] with s hs1 hs2
  rw [← hs1, hsum, hs2, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelSolutionField_coeff_ae (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce t).coeff i)
        =ᵐ[timeMeasure T]
      fun t => u₀.coeff i + ∫ s in (0 : ℝ)..t,
        ((maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv s).coeff i := by
  have hfield_coe := timeModeCoeff_coeFn (I := I) (M := M)
    (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce) i
  have hsplit : timeModeCoeff (I := I) (M := M)
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce) i =
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i +
          solutionModeCoeff (I := I) (M := M) (a := a) hT.le gforce i := by
    rw [maximalRegularityDuhamelSolutionField, timeModeCoeff_add (I := I) (M := M),
      maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a)
        (T := T) hT.le u₀ i,
      maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
        (h_compact := h_compact) (a := a) hT.le gforce i]
  have haddcoe := Lp.coeFn_add
    (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
    (solutionModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)
  have hA := homModeCoeff_eq_initial_add_integral (I := I) (M := M) (a := a) (T := T) u₀ i
  have hB := solutionModeCoeff_eq_integral (I := I) (M := M) (a := a) hT.le gforce i
  have hderiv_coe := maximalRegularityDuhamelMap_deriv_coeff_ae (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT u₀ gforce i
  filter_upwards [hfield_coe, haddcoe, hA, hB,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht1 ht2 htA htB htmem
  rw [← ht1, hsplit, ht2, Pi.add_apply, htA, htB]
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have hh0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, htmem.1.trans htmem.2⟩
  have hint_hom : IntervalIntegrable
      (fun s => (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s)
      volume 0 t := by
    have := (TimeSobolev.integrableOn
      (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)).mono_set
      (uIcc_subset_Icc hh0 htmem')
    exact this.intervalIntegrable
  have hint_duhamel : IntervalIntegrable
      (fun s => (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s)
      volume 0 t := by
    have := (TimeSobolev.integrableOn
      (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)).mono_set
      (uIcc_subset_Icc hh0 htmem')
    exact this.intervalIntegrable
  rw [add_assoc, ← intervalIntegral.integral_add hint_hom hint_duhamel]
  have hcongr : (∫ s in (0 : ℝ)..t,
        ((homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s +
          (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s)) =
      ∫ s in (0 : ℝ)..t,
        ((maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv s).coeff i := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc hh0 htmem')
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_coe
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with s hs hsmem
    rw [hs hsmem]
  rw [hcongr]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelSolutionFieldHa1_coeff_ae (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce t).coeff i)
        =ᵐ[timeMeasure T]
      fun t => u₀.coeff i + ∫ s in (0 : ℝ)..t,
        ((maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv s).coeff i := by
  have hHa1 := timeModeCoeff_coeFn (I := I) (M := M)
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce) i
  have hHa1mode : timeModeCoeff (I := I) (M := M)
      (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce) i =
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i +
          solutionModeCoeff (I := I) (M := M) (a := a) hT.le gforce i := by
    rw [maximalRegularityDuhamelSolutionFieldHa1, timeModeCoeff_add (I := I) (M := M),
      maximalRegularityHomogeneousSolutionFieldHa1_timeModeCoeff (I := I) (M := M) (a := a)
        (T := T) hT.le u₀ i,
      maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
        (h_compact := h_compact) (a := a) hT hT1 gforce i]
  have haddcoe := Lp.coeFn_add
    (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
    (solutionModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)
  have hA := homModeCoeff_eq_initial_add_integral (I := I) (M := M) (a := a) (T := T) u₀ i
  have hB := solutionModeCoeff_eq_integral (I := I) (M := M) (a := a) hT.le gforce i
  have hderiv_coe := maximalRegularityDuhamelMap_deriv_coeff_ae (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT u₀ gforce i
  filter_upwards [hHa1, haddcoe, hA, hB,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t htHa1 htadd htA htB htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have hh0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, htmem.1.trans htmem.2⟩
  rw [← htHa1, hHa1mode, htadd, Pi.add_apply, htA, htB]
  have hint_hom : IntervalIntegrable
      (fun s => (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s)
      volume 0 t :=
    ((TimeSobolev.integrableOn _).mono_set (uIcc_subset_Icc hh0 htmem')).intervalIntegrable
  have hint_duhamel : IntervalIntegrable
      (fun s => (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s)
      volume 0 t :=
    ((TimeSobolev.integrableOn _).mono_set (uIcc_subset_Icc hh0 htmem')).intervalIntegrable
  rw [add_assoc, ← intervalIntegral.integral_add hint_hom hint_duhamel]
  have hcongr : (∫ s in (0 : ℝ)..t,
        ((homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s +
          (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s)) =
      ∫ s in (0 : ℝ)..t,
        ((maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).deriv s).coeff i := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc hh0 htmem')
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_coe
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with s hs hsmem
    rw [hs hsmem]
  rw [hcongr]

omit [NeZero (Module.finrank ℝ E)] in
theorem solutionField_toFun_ae (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (fun t =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce t))
      =ᵐ[timeMeasure T]
        (maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).toFun := by
  have : Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g) (r := r) (s := s) h_compact
  set u := maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce with hu_def
  have hper : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ t ∂(timeMeasure T),
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce t).coeff i =
          (u.toFun t).coeff i := by
    intro i
    have hfield := maximalRegularityDuhamelSolutionField_coeff_ae (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT u₀ gforce i
    filter_upwards [hfield, ae_restrict_mem (μ := volume) measurableSet_Icc] with t htfield htmem
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, htmem.1.trans htmem.2⟩
    have hcomm :
        (tensorHsCoeffL (I := I) (M := M) (g := g) (r := r) (s := s) (a := a) i)
            (∫ τ in (0 : ℝ)..t, u.deriv τ) =
          ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (tensorHsCoeffL (I := I) (M := M) (g := g) (r := r) (s := s) (a := a) i)
        (u.intervalIntegrable_deriv h0 htmem)]
      rfl
    have hval : (u.toFun t).coeff i =
        u.initial.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i =
          (tensorHsCoeffL (I := I) (M := M) (g := g) (r := r) (s := s) (a := a) i)
            (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.initial.coeff i = u₀.coeff i := by
      rw [hu_def, maximalRegularityDuhamelMap_initial]
      rfl
    rw [htfield, hval, hinit]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine TensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply]
  exact ht i

omit [NeZero (Module.finrank ℝ E)] in
theorem solutionFieldHa1_toFun_ae (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (fun t =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith)
        (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce t))
      =ᵐ[timeMeasure T]
        (maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce).toFun := by
  have : Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g) (r := r) (s := s) h_compact
  set u := maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce with hu_def
  have hper : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ t ∂(timeMeasure T),
        (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce t).coeff i =
          (u.toFun t).coeff i := by
    intro i
    have hfield := maximalRegularityDuhamelSolutionFieldHa1_coeff_ae (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u₀ gforce i
    filter_upwards [hfield, ae_restrict_mem (μ := volume) measurableSet_Icc] with t htfield htmem
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, htmem.1.trans htmem.2⟩
    have hcomm :
        (tensorHsCoeffL (I := I) (M := M) (g := g) (r := r) (s := s) (a := a) i)
            (∫ τ in (0 : ℝ)..t, u.deriv τ) =
          ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (tensorHsCoeffL (I := I) (M := M) (g := g) (r := r) (s := s) (a := a) i)
        (u.intervalIntegrable_deriv h0 htmem)]
      rfl
    have hval : (u.toFun t).coeff i =
        u.initial.coeff i + ∫ τ in (0 : ℝ)..t, (u.deriv τ).coeff i := by
      have he : (u.toFun t).coeff i =
          (tensorHsCoeffL (I := I) (M := M) (g := g) (r := r) (s := s) (a := a) i)
            (u.toFun t) := rfl
      rw [he, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
      rfl
    have hinit : u.initial.coeff i = u₀.coeff i := by
      rw [hu_def, maximalRegularityDuhamelMap_initial]
      rfl
    rw [htfield, hval, hinit]
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine TensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply]
  exact ht i

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
