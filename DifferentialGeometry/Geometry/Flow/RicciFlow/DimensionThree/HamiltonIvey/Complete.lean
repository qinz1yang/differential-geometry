import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution
import DifferentialGeometry.Analysis.Spectral.CurvatureOperatorSpectrum
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorTracePullback
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Geometry.Connection.ModelNorm
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HamiltonIvey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLowerBound
import DifferentialGeometry.Bundle.Hom.Trace
import DifferentialGeometry.Analysis.Spectral.BundleLowerKyFan

noncomputable section
open Bundle CovariantDerivative Filter Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology InnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow

section Endomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem exists_pos_cutoff_scale (T R B L C : ℝ) :
    ∃ a : ℝ, 0 < a ∧ a * R < 1 ∧ T * (B * (a * L + a ^ 2) + 2 * (C * a ^ 2)) < 1 := by
  have hmul : ContinuousAt (fun a : ℝ => a * R) 0 := by fun_prop
  have herror : ContinuousAt (fun a : ℝ => T * (B * (a * L + a ^ 2) + 2 * (C * a ^ 2))) 0 := by
    fun_prop
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0,
      0 < a ∧ a * R < 1 ∧ T * (B * (a * L + a ^ 2) + 2 * (C * a ^ 2)) < 1 := by
    have hmul' := hmul.eventually (Iio_mem_nhds (by simp : (0 : ℝ) * R < 1))
    have herror' := herror.eventually (Iio_mem_nhds (by
      simp : T * (B * ((0 : ℝ) * L + 0 ^ 2) + 2 * (C * 0 ^ 2)) < 1))
    filter_upwards [self_mem_nhdsWithin, hmul'.filter_mono nhdsWithin_le_nhds,
      herror'.filter_mono nhdsWithin_le_nhds] with a ha haR haerror
    exact ⟨ha, haR, haerror⟩
  exact hsmall.exists

private theorem hamilton_ivey_of_complete_endomorphism_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Ioc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdimE : Module.finrank ℝ E = 3) (hdim : ∀ x, Module.finrank ℝ (V x) = 3)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞] (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hPDE : ∀ t ∈ Ioc 0 T, ∀ x,
      letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (S.base.metric t) (cov t) (fun y => A t y) x +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t)
    (hA : ∀ t x, (A t x).toLinearMap.IsSymmetric)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc 0 T ×ˢ (univ : Set M)))
    (htrace : ∀ t ∈ Icc 0 T, ∀ x,
      LinearMap.trace ℝ (V x) (A t x).toLinearMap = S.scalar t x)
    (O : M) (hneg : (⨅ v : {v : V O // v ≠ 0}, (A T O).rayleighQuotient v) < 0) :
    (-(⨅ v : {v : V O // v ≠ 0}, (A T O).rayleighQuotient v)) *
      (Real.log (T * (-(⨅ v : {v : V O // v ≠ 0}, (A T O).rayleighQuotient v))) - 3) ≤
      S.scalar T O := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨K, hK, hRic⟩ := exists_ricci_bound_on_distance_ball_on_compact
    S hS isCompact_Icc hslab hcomplete O 1
  obtain ⟨C, hC, hprofile⟩ := Analysis.CutoffProfile.exists_deriv_sq
  let B := Analysis.CutoffProfile.derivBound
  obtain ⟨a, ha, haR, haerror⟩ := exists_pos_cutoff_scale T 1 B
    (2 * (Module.finrank ℝ E - 1 : ℝ) * B ^ 2 / 1 + K * 1) C
  let χ : ℝ → M → ℝ := fun s y => Analysis.CutoffProfile.evalue
    (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y)
  let δ := B * (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * B ^ 2 / 1 + K * 1) + a ^ 2)
  let ε := C * a ^ 2
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    rw [hdimE]
    have hB : 0 ≤ B := Analysis.CutoffProfile.derivBound_nonneg
    norm_num
    positivity
  have hε : 0 ≤ ε := mul_nonneg hC (sq_nonneg a)
  obtain ⟨L, hL, hsupport⟩ := exists_compact_distance_cutoff_support S.base.metric
    hS.smoothMetric.metricTensor_cont isCompact_Icc hslab hcomplete O ha
  have hχcont := continuousOn_distance_cutoff S.base.metric ordConnected_Icc
    (hS.smoothMetric.metricTensor_cont.mono hslab) hcomplete O a
  let : IsContinuousRiemannianBundle F V := by
    obtain ⟨g, hg, hinner⟩ := IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := F) (E := V)
    exact ⟨g, hg.continuous, hinner⟩
  have hQcont := hAcont.iInf_rayleighQuotient_bundle.neg.sup (continuousOn_const (c := (0 : ℝ)))
  have hscalar (t : ℝ) (ht : t ∈ Ioc 0 T) (x : M) :
      -3 ≤ t * LinearMap.trace ℝ (V x) (A t x).toLinearMap := by
    rw [htrace t ⟨ht.1.le, ht.2⟩ x]
    have h := scalar_curvature_lower_bound_of_complete S hS ht.1.le
      (fun s hs => hslab ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hregular ⟨hs.1, hs.2.le.trans ht.2⟩)
      (fun s hs => hcomplete s ⟨hs.1, hs.2.trans ht.2⟩) x
    rw [hdimE] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hcut (t : ℝ) (ht : t ∈ Ioc 0 T) (x : M) :=
    distance_cutoff_lower_support_with_gradient_ratio S hS (hregular ht) ht.1
      (hcomplete t ⟨ht.1.le, ht.2⟩) O (show (0 : ℝ) < 1 by norm_num) hK
      (fun y hy v => (le_abs_self _).trans (hRic t ⟨ht.1.le, ht.2⟩ y hy.le v))
      ha.le haR hprofile x
  have hself : χ T O = 1 := by
    simp only [χ, riemannianEDistOf_self, mul_zero]
    exact Analysis.CutoffProfile.evalue_one_of_le (by norm_num)
  rw [← htrace T ⟨hT.le, le_rfl⟩ O]
  apply hamilton_ivey_inequality_of_compactly_supported_cutoff
    (flowG (I := I) S) cov hcov A (fun _ y => (0 : TangentSpace I y))
    (fun t ht => rfl) hdim
    (fun t ht x => by simpa only [flowG, map_zero, zero_apply, add_zero] using hPDE t ht x)
    (fun t ht x => hA t x) χ hL
    (hχcont.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ L)))
    (hAcont.trace_bundle.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ L)))
    (hQcont.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ L)))
    (fun t ht x => Analysis.CutoffProfile.evalue_mem_Icc _) hsupport hscalar hδ hε haerror
    (fun t ht x _ => by
      obtain ⟨φ, heq, hle, htime, hspace, hgrad, hP, hG⟩ := hcut t ht x
      exact ⟨φ, hle, heq, htime, hspace, hgrad, hP, hG⟩)
    ⟨hT, le_rfl⟩ O hself hneg

end Endomorphism

section FixedInnerProduct
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

variable [SigmaCompactSpace M]

omit [I.Boundaryless] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] [SigmaCompactSpace M] in
private theorem actual_curvature_operator_minimum {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι x v) (ι x w) = ⟪v, w⟫_ℝ)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    (⨅ v : {v : ⋀[ℝ]^2 (V x) // v ≠ 0},
      (exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
        ((mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric t) x)).compContinuousLinearMap
            (ι x).toContinuousLinearMap)).rayleighQuotient v) =
      2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  exact traceNormalizedCurvatureEndomorphism_metric_pullback_iInf_rayleighQuotient
    (I := I) (M := M) (E := E) (V := V) (S.family.metric t)
    (RiemannianMetric.ofInnerProductSpace V) ι hmetric x hdim
    ⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩

private theorem hamilton_ivey_of_complete_fixed_inner_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Icc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdimE : Module.finrank ℝ E = 3) (hdim : Module.finrank ℝ F = 3)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric 0).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫_ℝ)
    (O : M)
    (hneg : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩ < 0) :
    let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩
    (-ν) * (Real.log (T * (-ν)) - 3) ≤ S.scalar T O := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨ι, hinit, hmetric, A, hAeq, hAsym, hAsmooth, hAcont, hPDE⟩ :=
    exists_uhlenbeck_curvatureOperator_sections_evolution
      (F := F) (V := V) S hS ordConnected_Icc (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
      hregular hdim ι₀ hι₀ h₀
  classical
  have hcov (t : Icc (0 : ℝ) T) := hPDE t.val t.property
  choose covJ hcovsmooth hcovmetric hcovPDE using hcov
  let cov : ℝ → CovariantDerivative I (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
    fun t => if ht : t ∈ Icc 0 T then covJ ⟨t, ht⟩ else covJ ⟨0, le_rfl, hT.le⟩
  have hsmooth (t : ℝ) : ContMDiffCovariantDerivative (cov t) ∞ := by
    dsimp only [cov]
    split_ifs <;> exact hcovsmooth _
  have hmetriccov (t : ℝ) : (cov t).IsMetricCompatible := by
    dsimp only [cov]
    split_ifs <;> exact hcovmetric _
  have hPDEcov (t : ℝ) (ht : t ∈ Ioc 0 T) (x : M) :=
    (hcovPDE ⟨t, ht.1.le, ht.2⟩ x).mono
      (show Icc 0 t ⊆ Icc 0 T from fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  have htrace (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      LinearMap.trace ℝ (⋀[ℝ]^2 (V x)) (A t x).toLinearMap = S.scalar t x := by
    rw [hAeq t ht x]
    exact trace_traceNormalizedCurvatureEndomorphism_metric_pullback (S.family.metric t)
      (RiemannianMetric.ofInnerProductSpace V) (ι t) (hmetric t ht) x
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim)
  have hmin : (⨅ v : {v : ⋀[ℝ]^2 (V O) // v ≠ 0}, (A T O).rayleighQuotient v) =
      2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
        ⟨metricRm04At (S.family.metric T) O,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩ := by
    rw [hAeq T ⟨hT.le, le_rfl⟩ O]
    exact actual_curvature_operator_minimum (F := F) S T (ι T)
      (hmetric T ⟨hT.le, le_rfl⟩) O ((VectorBundle.finrank_eq ℝ F V O).trans hdim)
  let _ : ∀ t, ContMDiffCovariantDerivative (cov t) ∞ := hsmooth
  have hdimext (x : M) : Module.finrank ℝ (⋀[ℝ]^2 (V x)) = 3 := by
    rw [exteriorPower.finrank_eq, VectorBundle.finrank_eq ℝ F V x, hdim]
    norm_num
  have hp (t : ℝ) (ht : t ∈ Ioc 0 T) (x : M) :
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (S.base.metric t) (cov t) (fun y => A t y) x +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t := by
    have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    change HasDerivWithinAt (fun s => A s x)
      (rawBundleEndomorphismConnLap (I := I) (S.base.metric t)
        (if h : t ∈ Icc 0 T then covJ ⟨t, h⟩ else covJ ⟨0, le_rfl, hT.le⟩)
        (fun y => A t y) x +
        (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) _ _
    rw [dif_pos htcc]
    exact hPDEcov t ht x
  have hbound := hamilton_ivey_of_complete_endomorphism_evolution
    (I := I) (M := M) (F := ⋀[ℝ]^2 F) (V := fun x => ⋀[ℝ]^2 (V x))
    S hS hT hslab (fun _ ht => hregular ⟨ht.1.le, ht.2⟩) hcomplete hdimE hdimext
    cov hmetriccov A hp hAsym hAcont htrace O (by rw [hmin]; linarith)
  simpa only [hmin] using hbound

end FixedInnerProduct


section FixedMetric
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

variable [SigmaCompactSpace M]

private theorem hamilton_ivey_of_complete_fixed_metric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Icc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdimE : Module.finrank ℝ E = 3) (hdim : Module.finrank ℝ F = 3)
    (h : ContMDiffRiemannianMetric I ∞ F V)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric 0).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (O : M)
    (hneg : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩ < 0) :
    let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩
    (-ν) * (Real.log (T * (-ν)) - 3) ≤ S.scalar T O := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let : ∀ y, NormedAddCommGroup (V y) := sourceNorm
  let : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  let m := MetricFiberData.ofFiniteDimensional F
  have hιwithin := fun y =>
    (contMDiffWithinAt_hom_totalSpace_domain_model_metric_iff
      (IA := I) (IB := I) (F := E) (V := TangentSpace I) (W := V) m
      (n := ∞) (f := fun z => TotalSpace.mk' (F →L[ℝ] E) z (ι₀ z).toContinuousLinearMap)
      (s := Set.univ) (x := y)).mpr ((hι₀ y).contMDiffWithinAt (s := Set.univ))
  let vb := vector_bundle_model_metric (V := V) m
  let svb := contMDiffVectorBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let rm := isContMDiffRiemannianBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let : NormedAddCommGroup F := m.toNormedAddCommGroupOfTopology
  let : InnerProductSpace ℝ F := @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ m
  let : VectorBundle ℝ F V := vb
  let : ContMDiffVectorBundle ∞ F V I := svb
  let : IsContMDiffRiemannianBundle I ∞ F V := rm
  have hιnew : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap) :=
    fun y => contMDiffWithinAt_univ.mp (hιwithin y)
  exact hamilton_ivey_of_complete_fixed_inner_product S hS hT hslab hregular hcomplete
    hdimE hdim ι₀ hιnew h₀ O hneg

end FixedMetric

section Intrinsic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private theorem hamilton_ivey_of_complete_regular_slab
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Icc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdim : Module.finrank ℝ E = 3) (O : M)
    (hneg : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩ < 0) :
    let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩
    (-ν) * (Real.log (T * (-ν)) - 3) ≤ S.scalar T O := by
  exact hamilton_ivey_of_complete_fixed_metric (F := E) (V := TangentSpace I)
    S hS hT hslab hregular hcomplete hdim hdim (S.family.metric 0)
    (fun x => ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace I x))) from
      (contMDiff_id : ContMDiff I I ∞ (fun x : M => x)).clm_bundle_id)
    (fun _ _ _ => rfl) O hneg

private theorem logarithmic_bound_of_time_shifts {T q r : ℝ} (hT : 0 < T) (hq : 0 < q)
    (hbound : ∀ σ ∈ Ioo 0 T, q * (Real.log ((T - σ) * q) - 3) ≤ r) :
    q * (Real.log (T * q) - 3) ≤ r := by
  have harg : ContinuousAt (fun σ : ℝ => (T - σ) * q) 0 := by fun_prop
  have hlog : ContinuousAt (fun σ : ℝ => Real.log ((T - σ) * q)) 0 :=
    harg.log (by simpa only [sub_zero] using (mul_pos hT hq).ne')
  have hcont : ContinuousAt (fun σ : ℝ => q * (Real.log ((T - σ) * q) - 3)) 0 :=
    continuousAt_const.mul (hlog.sub continuousAt_const)
  have hlim : Tendsto (fun σ : ℝ => q * (Real.log ((T - σ) * q) - 3))
      (𝓝[>] 0) (𝓝 (q * (Real.log (T * q) - 3))) := by
    simpa only [sub_zero] using
      (hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hT] with σ hσ
  exact hbound σ hσ


private theorem hamilton_ivey_of_complete_regular_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Ioc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdim : Module.finrank ℝ E = 3) (O : M)
    (hneg : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩ < 0) :
    let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩
    (-ν) * (Real.log (T * (-ν)) - 3) ≤ S.scalar T O := by
  let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
    ⟨metricRm04At (S.family.metric T) O,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩
  have hν : 0 < -ν := by dsimp only [ν]; linarith
  change (-ν) * (Real.log (T * (-ν)) - 3) ≤ S.scalar T O
  apply logarithmic_bound_of_time_shifts hT hν
  intro σ hσ
  have hslab' : Icc 0 (T - σ) ⊆ (D.timeShift σ).carrier := by
    intro t ht
    change t + σ ∈ D.carrier
    apply hslab
    constructor <;> linarith [ht.1, ht.2, hσ.1, hσ.2]
  have hregular' : Icc 0 (T - σ) ⊆ (D.timeShift σ).regular := by
    intro t ht
    change t + σ ∈ D.regular
    apply hregular
    constructor <;> linarith [ht.1, ht.2, hσ.1, hσ.2]
  have hcomplete' : ∀ t ∈ Icc 0 (T - σ),
      RiemannianMetricComplete (I := I) ((S.timeShift σ).base.metric t) := by
    intro t ht
    change RiemannianMetricComplete (I := I) (S.base.metric (t + σ))
    apply hcomplete
    constructor <;> linarith [ht.1, ht.2, hσ.1, hσ.2]
  have hneg' : leastCurvatureOperatorEigenvalueAt (I := I) ((S.timeShift σ).family.metric (T - σ)) O
      ⟨metricRm04At ((S.timeShift σ).family.metric (T - σ)) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule ((S.timeShift σ).family.metric (T - σ)) O⟩ < 0 := by
    simpa only [SolutionOn.timeShift_family_metric, sub_add_cancel] using hneg
  have hbound := hamilton_ivey_of_complete_regular_slab (S.timeShift σ) (isSolutionOn_timeShift hS σ)
    (sub_pos.mpr hσ.2) hslab' hregular' hcomplete' hdim O hneg'
  simpa only [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar, sub_add_cancel, ν] using hbound

private theorem endpoint_logarithmic_estimate {T : ℝ} {q r : ℝ → ℝ}
    (hT : 0 < T) (hqcont : ContinuousOn q (Icc 0 T))
    (hrcont : ContinuousOn r (Icc 0 T)) (hqT : 0 < q T)
    (hbound : ∀ t ∈ Ioo 0 T, 0 < q t → q t * (Real.log (t * q t) - 3) ≤ r t) :
    q T * (Real.log (T * q T) - 3) ≤ r T := by
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hqTcont : ContinuousWithinAt q (Icc 0 T) T := hqcont T hTmem
  have hrTcont : ContinuousWithinAt r (Icc 0 T) T := hrcont T hTmem
  have hqIoo : ContinuousWithinAt q (Ioo 0 T) T :=
    hqTcont.mono Ioo_subset_Icc_self
  have harg : ContinuousWithinAt (fun t : ℝ => t * q t) (Ioo 0 T) T :=
    continuousWithinAt_id.mul hqIoo
  have hlog : ContinuousWithinAt (fun t : ℝ => Real.log (t * q t)) (Ioo 0 T) T :=
    harg.log (by simpa using (mul_pos hT hqT).ne')
  have hrIoo : ContinuousWithinAt r (Ioo 0 T) T :=
    hrTcont.mono Ioo_subset_Icc_self
  have hF : ContinuousWithinAt (fun t : ℝ => q t * (Real.log (t * q t) - 3))
      (Ioo 0 T) T := hqIoo.mul (hlog.sub_const 3)
  have hlim : Tendsto (fun t : ℝ => q t * (Real.log (t * q t) - 3))
      (𝓝[Ioo 0 T] T) (𝓝 (q T * (Real.log (T * q T) - 3))) := by
    exact hF.tendsto
  let : (𝓝[Ioo 0 T] T).NeBot := right_nhdsWithin_Ioo_neBot hT
  apply le_of_tendsto_of_tendsto hlim hrIoo.tendsto
  filter_upwards [self_mem_nhdsWithin, hqIoo.tendsto.eventually (Ioi_mem_nhds hqT)] with t ht hqt
  exact hbound t ht hqt


omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem continuousOn_least_curvature_eigenvalue_on_slab
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Ioo 0 T ⊆ D.regular) (hdim : Module.finrank ℝ E = 3) (O : M) :
    ContinuousOn (fun t => leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric t) O
      ⟨metricRm04At (S.family.metric t) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) O⟩) (Icc 0 T) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hclosed : IsSolutionOn (S.timeRestrict (RealTimeInterval.closed 0 T hT.le)) :=
    isSolutionOn_timeRestrict hS hslab hregular
  exact continuousOn_leastCurvatureOperatorEigenvalueAt_rm04_time hT
    (S.timeRestrict (RealTimeInterval.closed 0 T hT.le)) hclosed
    (fun x => (VectorBundle.finrank_eq ℝ E (TangentSpace I) x).trans hdim) O

private theorem continuousOn_time_slice
    {M : Type*} [TopologicalSpace M] (u : ℝ → M → ℝ) {J : Set ℝ}
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (J ×ˢ (univ : Set M)))
    {T : ℝ} (hslab : Icc 0 T ⊆ J) (O : M) :
    ContinuousOn (fun t => u t O) (Icc 0 T) := by
  have hmap : Continuous (fun t : ℝ => (t, O)) := continuous_id.prodMk continuous_const
  exact hu.comp hmap.continuousOn (fun t ht => ⟨hslab ht, Set.mem_univ O⟩)

theorem hamilton_ivey_inequality_of_complete
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Ioo 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdim : Module.finrank ℝ E = 3) (O : M)
    (hneg : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩ < 0) :
    let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric T) O
      ⟨metricRm04At (S.family.metric T) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric T) O⟩
    (-ν) * (Real.log (T * (-ν)) - 3) ≤ S.scalar T O := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let ν : ℝ → ℝ := fun t => 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric t) O
    ⟨metricRm04At (S.family.metric t) O,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) O⟩
  have hνcont : ContinuousOn ν (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_least_curvature_eigenvalue_on_slab
      S hS hT hslab hregular hdim O)
  have hrcont := continuousOn_time_slice S.scalar hS.scalarCont hslab O
  change (-ν T) * (Real.log (T * (-ν T)) - 3) ≤ S.scalar T O
  apply endpoint_logarithmic_estimate (q := fun t => -ν t) (r := fun t => S.scalar t O)
    hT hνcont.neg hrcont (by dsimp only [ν]; linarith)
  intro t ht hq
  have hnt : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric t) O
      ⟨metricRm04At (S.family.metric t) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) O⟩ < 0 := by
    dsimp only [ν] at hq
    linarith
  have hbound := hamilton_ivey_of_complete_regular_endpoint (I := I) (M := M) S hS ht.1
    (fun s hs => hslab ⟨hs.1, hs.2.trans ht.2.le⟩)
    (fun s hs => hregular ⟨hs.1, hs.2.trans_lt ht.2⟩)
    (fun s hs => hcomplete s ⟨hs.1, hs.2.trans ht.2.le⟩) hdim O hnt
  exact hbound

theorem hamilton_ivey_inequality_on_interval_of_complete
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc a b, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hdim : Module.finrank ℝ E = 3) (O : M)
    (hneg : leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric b) O
      ⟨metricRm04At (S.family.metric b) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric b) O⟩ < 0) :
    let ν := 2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric b) O
      ⟨metricRm04At (S.family.metric b) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric b) O⟩
    (-ν) * (Real.log ((b - a) * (-ν)) - 3) ≤ S.scalar b O := by
  have hslab' : Icc 0 (b - a) ⊆ (D.timeShift a).carrier := by
    intro t ht
    change t + a ∈ D.carrier
    apply hslab
    constructor <;> linarith [ht.1, ht.2]
  have hregular' : Ioo 0 (b - a) ⊆ (D.timeShift a).regular := by
    intro t ht
    change t + a ∈ D.regular
    apply hregular
    constructor <;> linarith [ht.1, ht.2]
  have hcomplete' : ∀ t ∈ Icc 0 (b - a),
      RiemannianMetricComplete (I := I) ((S.timeShift a).base.metric t) := by
    intro t ht
    change RiemannianMetricComplete (I := I) (S.base.metric (t + a))
    apply hcomplete
    constructor <;> linarith [ht.1, ht.2]
  have hneg' : leastCurvatureOperatorEigenvalueAt (I := I) ((S.timeShift a).family.metric (b - a)) O
      ⟨metricRm04At ((S.timeShift a).family.metric (b - a)) O,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule ((S.timeShift a).family.metric (b - a)) O⟩ < 0 := by
    simpa only [SolutionOn.timeShift_family_metric, sub_add_cancel] using hneg
  have h := hamilton_ivey_inequality_of_complete (I := I) (M := M)
    (S.timeShift a) (isSolutionOn_timeShift hS a) (sub_pos.mpr hab)
    hslab' hregular' hcomplete' hdim O hneg'
  simpa only [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar, sub_add_cancel] using h


theorem curvatureOperator_nonnegative_of_complete_ancient
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {t : ℝ}
    (hcarrier : Iic t ⊆ D.carrier) (hregular : Iio t ⊆ D.regular)
    (hcomplete : ∀ s ∈ Iic t,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hdim : Module.finrank ℝ E = 3) (x : M) :
    (⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hnonneg : 0 ≤ leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A := by
    by_contra h
    have hneg := lt_of_not_ge h
    let q := -(2 * leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)
    have hq : 0 < q := by dsimp [q]; linarith
    let a := t - Real.exp (S.scalar t x / q + 4) / q
    have ha : 0 < t - a := by
      dsimp [a]
      rw [sub_sub_cancel]
      exact div_pos (Real.exp_pos _) hq
    have hat : a < t := sub_pos.mp ha
    have hslab : Icc a t ⊆ D.carrier := by
      intro r hr
      exact hcarrier hr.2
    have hreg : Ioo a t ⊆ D.regular := by
      intro r hr
      exact hregular hr.2
    have hcomplete' : ∀ s ∈ Icc a t,
        RiemannianMetricComplete (I := I) (S.base.metric s) := by
      intro s hs
      exact hcomplete s hs.2
    have hpinch := hamilton_ivey_inequality_on_interval_of_complete
      (I := I) (M := M) S hS hat hslab hreg hcomplete' hdim x
      (by change leastCurvatureOperatorEigenvalueAt (I := I) (S.family.metric t) x A < 0
          exact hneg)
    change q * (Real.log ((t - a) * q) - 3) ≤ S.scalar t x at hpinch
    have harg : (t - a) * q = Real.exp (S.scalar t x / q + 4) := by
      dsimp [a]
      rw [sub_sub_cancel]
      exact div_mul_cancel₀ _ hq.ne'
    rw [harg, Real.log_exp] at hpinch
    have hcancel : q * (S.scalar t x / q) = S.scalar t x :=
      mul_div_cancel₀ _ hq.ne'
    nlinarith [hpinch]
  exact (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
    (I := I) (M := M) (S.base.metric t) hdim).mp hnonneg


end Intrinsic
end DifferentialGeometry.PDE.RicciFlow

end
