import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SmoothPathHs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.StrongSolutionUniqueness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDiffJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothEmbedInj

/-!
# Smooth geometric Ricci--DeTurck paths as strong Sobolev pairs

This file packages a classically smooth tensor path satisfying a geometric
Ricci--DeTurck equation as the zero-trace `timeH1`/`timeL2` strong pair used by
the maximal-regularity uniqueness theorem.  The construction is direct: the
continuous strong time derivative is put in `timeL2`, the path is recovered by
the Banach-space fundamental theorem of calculus, and all cross-scale and PDE
identities are then proved as equalities of `Lp` classes.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The spectral embedding sends the zero smooth tensor to zero at every
Sobolev order. -/
theorem smoothHs_zero (g : SmoothRiemannianMetric I M) (sigma : ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g sigma
        (0 : SmoothCcTensor g 0 2) = 0 := by
  refine tensorHs.ext ?_
  funext i
  rw [smoothCcToTensorHs_coeff,
    show SmoothCcTensor.toL2 (0 : SmoothCcTensor g 0 2) = 0 from map_zero _,
    tensorL2Coeff_eq_inner, inner_zero_right, tensorHs.zero_coeff]

/-- A jointly smooth tensor path which vanishes at zero stays in any positive
high-Sobolev ball on some positive closed window contained in its open
parameter set. -/
theorem exists_pathBall
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (Phi : ℝ → SmoothCcTensor g 0 2) {S : Set ℝ}
    (hS : IsOpen S) (h0S : (0 : ℝ) ∈ S)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hPhi0 : Phi 0 = 0) {R : ℝ} (hR : 0 < R) :
    ∃ T : ℝ, 0 < T ∧ Icc (0 : ℝ) T ⊆ S ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi t)‖ ≤ R := by
  let F : ℝ → tensorHs (I := I) (M := M) g 0 2 (n : ℝ) := fun t =>
    smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi t)
  have hFcont : ContinuousAt F 0 :=
    (smoothHs_path_cd (I := I) (M := M) g n Phi hS hPhi).continuousOn.continuousAt
      (hS.mem_nhds h0S)
  have hF0 : F 0 = 0 := by
    simp only [F, hPhi0, smoothHs_zero]
  obtain ⟨rF, hrF, hclose⟩ := Metric.continuousAt_iff.mp hFcont R hR
  obtain ⟨rS, hrS, hballS⟩ := Metric.isOpen_iff.mp hS 0 h0S
  set T : ℝ := min rF rS / 2 with hTdef
  have hmin : 0 < min rF rS := lt_min hrF hrS
  have hT : 0 < T := by rw [hTdef]; positivity
  have hTF : T < rF := by
    rw [hTdef]
    have hle := min_le_left rF rS
    nlinarith
  have hTS : T < rS := by
    rw [hTdef]
    have hle := min_le_right rF rS
    nlinarith
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    apply hballS
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hTS
  · intro t ht
    have hdist : dist t (0 : ℝ) < rF := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt ht.2 hTF
    have h := hclose hdist
    rw [hF0, dist_zero_right] at h
    exact h.le

/-- A continuous high-Sobolev path with a continuous strong derivative and a
pointwise semilinear parabolic equation determines the exact zero-trace strong
pair consumed by reverse Duhamel uniqueness. -/
theorem smoothPath_strong
    (g : SmoothRiemannianMetric I M) (a : ℝ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g 0 2 (a + 2) →
      tensorHs (I := I) (M := M) g 0 2 a}
    (hLip : LipschitzWith L Nfun) {T : ℝ}
    (Fhi : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (Flow D : ℝ → tensorHs (I := I) (M := M) g 0 2 a)
    (hhi : ContinuousOn Fhi (Icc (0 : ℝ) T))
    (hD : ContinuousOn D (Icc (0 : ℝ) T))
    (hincl : ∀ t ∈ Icc (0 : ℝ) T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show a ≤ a + 2 by linarith) (Fhi t) = Flow t)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Flow (D t) t)
    (hzero : Flow 0 = 0)
    (hpde : ∀ t ∈ Icc (0 : ℝ) T,
      D t = tensorScaleLaplacian (I := I) (M := M) a (Fhi t) + Nfun (Fhi t)) :
    ∃ force : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T,
      ∃ u : timeH1 (tensorHs (I := I) (M := M) g 0 2 a) T,
        ∃ field : timeL2 (tensorHs (I := I) (M := M) g 0 2 (a + 2)) T,
          timeH1.trace0 _ T u = 0 ∧
          timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show a ≤ a + 2 by linarith) field =
            timeH1.toTimeL2 (tensorHs (I := I) (M := M) g 0 2 a) T u ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a field + force ∧
          force = nemytskii (I := I) (M := M) hLip field ∧
          (field : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2))
            =ᵐ[timeMeasure T] Fhi ∧
          (force : ℝ → tensorHs (I := I) (M := M) g 0 2 a)
            =ᵐ[timeMeasure T] fun t => Nfun (Fhi t) ∧
          ∀ t ∈ Icc (0 : ℝ) T, u.toFun t = Flow t := by
  have hNcont : ContinuousOn (fun t => Nfun (Fhi t)) (Icc (0 : ℝ) T) :=
    hLip.continuous.comp_continuousOn hhi
  let field : timeL2 (tensorHs (I := I) (M := M) g 0 2 (a + 2)) T :=
    TimeSobolev.ofContinuousOn hhi
  let force : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T :=
    TimeSobolev.ofContinuousOn hNcont
  let derivL2 : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T :=
    TimeSobolev.ofContinuousOn hD
  let u : timeH1 (tensorHs (I := I) (M := M) g 0 2 a) T :=
    timeH1.mk (Flow 0) derivL2
  have htoFun : ∀ t ∈ Icc (0 : ℝ) T, u.toFun t = Flow t := by
    intro t ht
    have hzeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) T :=
      ⟨le_rfl, le_trans ht.1 ht.2⟩
    have hrep : (derivL2 : ℝ → tensorHs (I := I) (M := M) g 0 2 a)
        =ᵐ[timeMeasure T] D := by
      simpa only [derivL2] using TimeSobolev.coeFn_ofContinuousOn hD
    have hrepVol : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) T → derivL2 s = D s :=
      (ae_restrict_iff' measurableSet_Icc).1 hrep
    have hintEq : (∫ s in (0 : ℝ)..t, derivL2 s) = ∫ s in (0 : ℝ)..t, D s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hrepVol] with s hs hsI
      exact hs ((Set.uIoc_subset_uIcc).trans
        (uIcc_subset_Icc hzeroMem ht) hsI)
    have hDint : IntegrableOn D (Icc (0 : ℝ) T) volume :=
      (TimeSobolev.memLp_of_continuousOn hD).integrable (by norm_num)
    have hint : IntervalIntegrable D volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable
        (hDint.mono_set (uIcc_subset_Icc hzeroMem ht))
    have hFTC : (∫ s in (0 : ℝ)..t, D s) = Flow t - Flow 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hderiv s ((uIcc_subset_Icc hzeroMem ht) hs)) hint
    simp only [u, timeH1.toFun_apply, timeH1.init_mk, timeH1.deriv_mk]
    rw [hintEq, hFTC]
    abel
  have hfieldRep : (field : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2))
      =ᵐ[timeMeasure T] Fhi := by
    simpa only [field] using TimeSobolev.coeFn_ofContinuousOn hhi
  have hforceRep : (force : ℝ → tensorHs (I := I) (M := M) g 0 2 a)
      =ᵐ[timeMeasure T] fun t => Nfun (Fhi t) := by
    simpa only [force] using TimeSobolev.coeFn_ofContinuousOn hNcont
  refine ⟨force, u, field, ?_, ?_, ?_, ?_, hfieldRep, hforceRep, htoFun⟩
  · simpa only [u, timeH1.trace0_mk] using hzero
  · refine Lp.ext ?_
    have hinclAE :
        ⇑(timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show a ≤ a + 2 by linarith) field) =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show a ≤ a + 2 by linarith) (field t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show a ≤ a + 2 by linarith)).coeFn_compLpL
          (p := 2) (μ := timeMeasure T) field
    have huAE :
        ⇑(timeH1.toTimeL2 (tensorHs (I := I) (M := M) g 0 2 a) T u)
            =ᵐ[timeMeasure T] u.toFun := by
      simpa only [timeH1.toTimeL2_apply] using
        TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hinclAE, hfieldRep, huAE, hmem] with t hit hft hut ht
    rw [hit, hft, hut, hincl t ht, htoFun t ht]
  · refine Lp.ext ?_
    have hderivAE :
        ⇑(timeH1.timeDeriv (tensorHs (I := I) (M := M) g 0 2 a) T u)
            =ᵐ[timeMeasure T] D := by
      simpa only [u, derivL2, timeH1.timeDeriv_mk] using
        TimeSobolev.coeFn_ofContinuousOn hD
    have hLap := timeScaleLaplacian_coeFn (I := I) (M := M) (τ := a) field
    have hadd := Lp.coeFn_add
      (timeScaleLaplacian (I := I) (M := M) a field) force
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hderivAE, hfieldRep, hforceRep, hLap, hadd, hmem]
      with t hdt hft hnft hLapt haddt ht
    rw [hdt, haddt, hLapt, hft, hnft, hpde t ht]
  · refine Lp.ext ?_
    have hNemy := nemytskii_coeFn (I := I) (M := M) hLip field
    filter_upwards [hforceRep, hfieldRep, hNemy] with t hft hhit hNt
    rw [hft, hNt, hhit]

/-- The Ricci--DeTurck right-hand side, recast into the fixed-background
`SmoothCcTensor` carrier.  Only the carrier metric changes; the underlying
mixed tensor section is unchanged. -/
def deTurckRHSBase (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport

/-- The geometric metric equation for a smooth path gives the exact
unit-model equation for its fixed-background metric-difference tensor.  The
realized metric in `deTurckRHSBase` is eliminated by `realize_metricDiff`. -/
theorem metricDiff_pde
    (q g_bg : SmoothRiemannianMetric I M)
    (G : ℝ → SmoothRiemannianMetric I M) {T δ : ℝ} (hδ_lt : δ < 1)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T,
      gFibreOpBound (I := I) (M := M) q
        (ccTensorBilinSymm (I := I) q
          (metricDifferenceCcTensor (I := I) (M := M) q (G t))) δ)
    (hPDE : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivAt (fun tau => (G tau).inner x v w)
          (deTurckRicciRHS (I := I) g_bg (G t) x v w) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ slots : Fin 2 → E,
      HasDerivAt
        (fun tau => unitModel (I := I) (M := M) q 2
          (metricDifferenceCcTensor (I := I) (M := M) q (G tau)) x slots)
        (unitModel (I := I) (M := M) q 2
          (deTurckRHSBase (I := I) (M := M) q g_bg
            (metricDifferenceCcTensor (I := I) (M := M) q (G t)) hδ_lt
            (hsmall t ‹t ∈ Icc (0 : ℝ) T›)) x slots) t := by
  intro t ht x slots
  have hder := (hPDE t ht x (slots 0) (slots 1)).sub_const
    (q.inner x (slots 0) (slots 1))
  have hrhs :
      unitModel (I := I) (M := M) q 2
          (deTurckRHSBase (I := I) (M := M) q g_bg
            (metricDifferenceCcTensor (I := I) (M := M) q (G t)) hδ_lt
            (hsmall t ht)) x slots =
        deTurckRicciRHS (I := I) g_bg (G t) x (slots 0) (slots 1) := by
    have hunit := unitModel_of_deTurckRHSSection_realize
      (I := I) (M := M) q g_bg
      (metricDifferenceCcTensor (I := I) (M := M) q (G t)) hδ_lt
      (hsmall t ht)
      (deTurckRHSBase (I := I) (M := M) q g_bg
        (metricDifferenceCcTensor (I := I) (M := M) q (G t)) hδ_lt
        (hsmall t ht)) rfl x slots
    rw [realize_metricDiff (I := I) (M := M) q (G t) hδ_lt
      (hsmall t ht)] at hunit
    exact hunit
  rw [hrhs]
  simpa only [metricDiff_unit] using hder

/-- The fixed-background Ricci--DeTurck right-hand side splits exactly into
the rough connection Laplacian and the smooth DeTurck remainder. -/
theorem rhsBase_eq_lap_rem (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckRHSBase (I := I) (M := M) g₀ g_bg T hδ_lt hδ =
      rawTensorConnLapSmooth (I := I) g₀ 0 2 T +
        deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ := by
  unfold deTurckRHSBase deTurckSmoothRemainder
  abel

/-- Spectral coefficients of the smooth rough connection Laplacian. -/
theorem smoothLap_coeff (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T).coeff i := by
  classical
  have hdiag := tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
    (I := I) (M := M) g₀
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) T i 1
  have hiter1 : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 1 T =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 T := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero]
  have hsub : SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 T) =
      SmoothCcTensor.toL2 T -
        SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T) := by
    unfold oneMinusConnLapSmooth
    exact map_sub _ _ _
  rw [hiter1, hsub] at hdiag
  rw [tensorL2Coeff_eq_inner, inner_sub_right, ← tensorL2Coeff_eq_inner,
    ← tensorL2Coeff_eq_inner] at hdiag
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [pow_one] at hdiag
  linear_combination -hdiag

/-- The smooth rough connection Laplacian is the loss-two spectral
Laplacian. -/
theorem smoothLap_eq_scale (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    tensorScaleLaplacian (I := I) (M := M) σ
        (smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorScaleLaplacian_coeff, smoothLap_coeff]
  rfl

/-- The smooth DeTurck nonlinearity is exactly the spectral embedding of the
smooth remainder. -/
theorem smoothRem_eq_N (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  refine tensorHs.ext ?_
  funext i
  rfl

/-- A smooth geometric Ricci--DeTurck perturbation on a closed time window is
an exact strong pair for the live symmetric Sobolev nonlinearity. -/
theorem smoothGeom_strong
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {L : ℝ≥0}
    (hLip : LipschitzWith L
      (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a))
    {T : ℝ} (Phi : ℝ → SmoothCcTensor g₀ 0 2) {S : Set ℝ}
    (hS : IsOpen S) (hIcc : Icc (0 : ℝ) T ⊆ S)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hPhi0 : Phi 0 = 0) {δ : ℝ} (hδ_lt : δ < 1)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T,
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (Phi t)) δ)
    (hsymm : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        ccTensorBilin (I := I) g₀ (Phi t) x v w =
          ccTensorBilin (I := I) g₀ (Phi t) x w v)
    (hball : ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t)‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1)
    (hPDE : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ slots : Fin 2 → E,
        HasDerivAt
          (fun tau => unitModel (I := I) (M := M) g₀ 2 (Phi tau) x slots)
          (unitModel (I := I) (M := M) g₀ 2
            (deTurckRHSBase (I := I) (M := M) g₀ g_bg (Phi t) hδ_lt
              (hsmall t ‹t ∈ Icc (0 : ℝ) T›)) x slots) t) :
    ∃ force : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T,
      ∃ u : timeH1 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T,
        ∃ field : timeL2
            (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T,
          timeH1.trace0 _ T u = 0 ∧
          timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) field =
            timeH1.toTimeL2
              (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T u ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (a : ℝ) field + force ∧
          force = nemytskii (I := I) (M := M) hLip field ∧
          (field : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            =ᵐ[timeMeasure T] fun t => smoothCcToTensorHs (I := I) (M := M)
              g₀ ((a : ℝ) + 2) (Phi t) ∧
          (force : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
            =ᵐ[timeMeasure T] fun t =>
              deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
                (smoothCcToTensorHs (I := I) (M := M) g₀
                  ((a : ℝ) + 2) (Phi t)) ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            u.toFun t = smoothCcToTensorHs (I := I) (M := M)
              g₀ (a : ℝ) (Phi t) := by
  obtain ⟨dPhi, hdPhi, hcomp, hHs⟩ :=
    smoothHs_deriv (I := I) (M := M) g₀ Phi hS hPhi
  have hdPhi_eq : ∀ t ∈ Icc (0 : ℝ) T,
      dPhi t = deTurckRHSBase (I := I) (M := M) g₀ g_bg (Phi t)
        hδ_lt (hsmall t ‹t ∈ Icc (0 : ℝ) T›) := by
    intro t ht
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    apply ContinuousMultilinearMap.ext
    intro slots
    change unitModel (I := I) (M := M) g₀ 2 (dPhi t) x slots =
      unitModel (I := I) (M := M) g₀ 2
        (deTurckRHSBase (I := I) (M := M) g₀ g_bg (Phi t) hδ_lt
          (hsmall t ht)) x slots
    exact (hcomp t (hIcc ht) x (unitTensor (I := I) (M := M) x) slots).unique
      (hPDE t ht x slots)
  have hhi : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀
        ((a : ℝ) + 2) (Phi t)) (Icc (0 : ℝ) T) := by
    have hcd := smoothHs_path_cd (I := I) (M := M) g₀ (a + 2) Phi hS hPhi
    have hcast : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hcd
    exact hcd.continuousOn.mono hIcc
  have hD : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (dPhi t))
      (Icc (0 : ℝ) T) :=
    (smoothHs_path_cd (I := I) (M := M) g₀ a dPhi hS hdPhi).continuousOn.mono hIcc
  have hincl : ∀ t ∈ Icc (0 : ℝ) T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith)
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t)) =
        smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t) := by
    intro t _
    exact tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (Phi t)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun tau => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi tau))
        (smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (dPhi t)) t := by
    intro t ht
    exact hHs a t (hIcc ht)
  have hzero : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi 0) = 0 := by
    rw [hPhi0]
    refine tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff,
      show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
      tensorL2Coeff_eq_inner, inner_zero_right, tensorHs.zero_coeff]
  have hpde : ∀ t ∈ Icc (0 : ℝ) T,
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (dPhi t) =
        tensorScaleLaplacian (I := I) (M := M) (a : ℝ)
            (smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + 2) (Phi t)) +
          deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + 2) (Phi t)) := by
    intro t ht
    have hN := deTurckSobolevNHa2Symm_eq_smoothN_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super (Phi t) hδ_lt (hsmall t ht)
        (hsymm t ht) (hball t ht)
    calc
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (dPhi t) =
          smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
            (deTurckRHSBase (I := I) (M := M) g₀ g_bg (Phi t)
              hδ_lt (hsmall t ht)) := by rw [hdPhi_eq t ht]
      _ = smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (Phi t) +
              deTurckSmoothRemainder (I := I) g₀ g_bg (Phi t)
                hδ_lt (hsmall t ht)) := by rw [rhsBase_eq_lap_rem]
      _ = smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (Phi t)) +
          smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (Phi t)
              hδ_lt (hsmall t ht)) :=
        smoothCcToTensorHs_add (I := I) (M := M) g₀ (a : ℝ) _ _
      _ = tensorScaleLaplacian (I := I) (M := M) (a : ℝ)
            (smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + 2) (Phi t)) +
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a (Phi t)
            hδ_lt (hsmall t ht) := by
        rw [← smoothLap_eq_scale, smoothRem_eq_N]
      _ = tensorScaleLaplacian (I := I) (M := M) (a : ℝ)
            (smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + 2) (Phi t)) +
          deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + 2) (Phi t)) := by rw [hN]
  exact smoothPath_strong (I := I) (M := M) g₀ (a : ℝ) hLip
    (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t))
    (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t))
    (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (dPhi t))
    hhi hD hincl hderiv hzero hpde

/-- A continuous high-Sobolev path has a finite uniform bound for its
Lipschitz nonlinearity on a nonempty closed time window. -/
theorem exists_pathNBound
    (g : SmoothRiemannianMetric I M) (a : ℝ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g 0 2 (a + 2) →
      tensorHs (I := I) (M := M) g 0 2 a}
    (hLip : LipschitzWith L Nfun) {T : ℝ} (hT : 0 ≤ T)
    (Fhi : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (hFhi : ContinuousOn Fhi (Icc (0 : ℝ) T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖Nfun (Fhi t)‖ ≤ B := by
  have hcont : ContinuousOn (fun t => ‖Nfun (Fhi t)‖) (Icc (0 : ℝ) T) :=
    (hLip.continuous.comp_continuousOn hFhi).norm
  obtain ⟨t₀, _ht₀, ht₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hcont
  exact ⟨‖Nfun (Fhi t₀)‖, norm_nonneg _, fun t ht => ht₀max ht⟩

/-- The mixed Ricci--DeTurck contraction and force-ball budgets are available
on a positive horizon depending only on the two mixed constants and a
pointwise forcing bound. -/
theorem exists_mixBudget (C₁ C₂ : ℝ≥0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ ρ T₀ : ℝ, 0 < ρ ∧ 0 < T₀ ∧
      ∀ {T : ℝ}, 0 < T → T ≤ T₀ →
        T ≤ 1 ∧ Real.sqrt T * B ≤ ρ ∧
          (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
              (C₂ : ℝ) * (2 * Real.sqrt T) < 1 := by
  set ρ : ℝ := 1 / (16 * ((C₁ : ℝ) + 1)) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  set T₀ : ℝ := min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
    ((ρ / (2 * (B + 1))) ^ 2)) with hT₀def
  have hT₀pos : 0 < T₀ := by
    refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · have : 0 < ρ / (2 * (B + 1)) := by positivity
      positivity
  refine ⟨ρ, T₀, hρpos, hT₀pos, ?_⟩
  intro T hT hTT₀
  have hT1 : T ≤ 1 := le_trans hTT₀ (by rw [hT₀def]; exact min_le_left _ _)
  have hTlo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTT₀ (by
      rw [hT₀def]
      exact le_trans (min_le_right _ _) (min_le_left _ _))
  have hTstay : T ≤ (ρ / (2 * (B + 1))) ^ 2 :=
    le_trans hTT₀ (by
      rw [hT₀def]
      exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hsqrtTstay : Real.sqrt T ≤ ρ / (2 * (B + 1)) := by
    rw [show ρ / (2 * (B + 1)) =
      Real.sqrt ((ρ / (2 * (B + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hTstay
  have hforce : Real.sqrt T * B ≤ ρ := by
    calc
      Real.sqrt T * B ≤ (ρ / (2 * (B + 1))) * B :=
        mul_le_mul_of_nonneg_right hsqrtTstay hB
      _ ≤ (ρ / (2 * (B + 1))) * (B + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
        have hne : B + 1 ≠ 0 := by positivity
        field_simp
      _ ≤ ρ := by linarith
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T : Real.sqrt (1 + T) ≤ 1 + T := by
    have h1le : (1 : ℝ) ≤ 1 + T := by linarith
    calc
      Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
      _ = 1 + T := Real.sqrt_sq (by linarith)
  have harm1 :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) ≤ 1 / 4 := by
    have hle :
        (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) ≤
          (C₁ : ℝ) * 2 * ρ * 2 := by
      have hsqrt2 : Real.sqrt (1 + T) ≤ 2 := le_trans hsqrt1T h1T
      have h0 : (0 : ℝ) ≤ 1 + T := by linarith
      have hC₁ : (0 : ℝ) ≤ (C₁ : ℝ) := C₁.coe_nonneg
      gcongr
    refine le_trans hle ?_
    rw [hρdef]
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
      (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [C₁.coe_nonneg]
    nlinarith [hfrac,
      div_nonneg C₁.coe_nonneg (by positivity : (0 : ℝ) ≤ (C₁ : ℝ) + 1)]
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
      Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTlo ?_)
    rw [div_pow, one_pow, mul_pow]
    norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hC₂ : (0 : ℝ) ≤ (C₂ : ℝ) := C₂.coe_nonneg
    calc
      (C₂ : ℝ) * (2 * Real.sqrt T) = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
        have hne : (C₂ : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      _ ≤ 1 / 4 := by
        have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        nlinarith [hfrac,
          div_nonneg hC₂ (by positivity : (0 : ℝ) ≤ (C₂ : ℝ) + 1)]
  exact ⟨hT1, hforce, by linarith⟩

/-- Local uniqueness of two smooth geometric Ricci--DeTurck perturbations on
one closed, already time-translated interior window.  Both paths use the same
fixed initial carrier `g₀`, the same DeTurck background `g_bg`, the same
Sobolev truncation radius, and zero perturbation at the left endpoint.

The numerical hypotheses are precisely the force-ball and mixed-contraction
budgets of `deTurckStrong_unique`.  The pointwise bound `B` implies the force
ball bound by the honest `sqrt T` estimate.  This theorem intentionally does
not start a window from merely `C0` data at the original flow edge. -/
theorem smoothGeom_unique
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {L C₁ C₂ : ℝ≥0}
    (hLip : LipschitzWith L
      (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a))
    (hsingle : ∀ (v v' :
      tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a v -
          deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a v'‖ ≤
        (C₁ : ℝ) * max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v'‖ * ‖v - v'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (v - v')‖)
    {T ρ B : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hρ : 0 ≤ ρ)
    (hB : 0 ≤ B) (hforceBudget : Real.sqrt T * B ≤ ρ)
    (hcontract :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    (Phi₁ Phi₂ : ℝ → SmoothCcTensor g₀ 0 2) {S : Set ℝ}
    (hS : IsOpen S) (hIcc : Icc (0 : ℝ) T ⊆ S)
    (hPhi₁ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi₁ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hPhi₂ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi₂ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hPhi₁0 : Phi₁ 0 = 0) (hPhi₂0 : Phi₂ 0 = 0)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hsmall₁ : ∀ t ∈ Icc (0 : ℝ) T,
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (Phi₁ t)) δ)
    (hsmall₂ : ∀ t ∈ Icc (0 : ℝ) T,
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (Phi₂ t)) δ)
    (hsymm₁ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        ccTensorBilin (I := I) g₀ (Phi₁ t) x v w =
          ccTensorBilin (I := I) g₀ (Phi₁ t) x w v)
    (hsymm₂ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        ccTensorBilin (I := I) g₀ (Phi₂ t) x v w =
          ccTensorBilin (I := I) g₀ (Phi₂ t) x w v)
    (hball₁ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi₁ t)‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1)
    (hball₂ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi₂ t)‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1)
    (hPDE₁ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ slots : Fin 2 → E,
        HasDerivAt
          (fun tau => unitModel (I := I) (M := M) g₀ 2 (Phi₁ tau) x slots)
          (unitModel (I := I) (M := M) g₀ 2
            (deTurckRHSBase (I := I) (M := M) g₀ g_bg (Phi₁ t) hδ_lt
              (hsmall₁ t ‹t ∈ Icc (0 : ℝ) T›)) x slots) t)
    (hPDE₂ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ slots : Fin 2 → E,
        HasDerivAt
          (fun tau => unitModel (I := I) (M := M) g₀ 2 (Phi₂ tau) x slots)
          (unitModel (I := I) (M := M) g₀ 2
            (deTurckRHSBase (I := I) (M := M) g₀ g_bg (Phi₂ t) hδ_lt
              (hsmall₂ t ‹t ∈ Icc (0 : ℝ) T›)) x slots) t)
    (hNbound₁ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀
          ((a : ℝ) + 2) (Phi₁ t))‖ ≤ B)
    (hNbound₂ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀
          ((a : ℝ) + 2) (Phi₂ t))‖ ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) T, Phi₁ t = Phi₂ t := by
  rcases smoothGeom_strong (I := I) (M := M) g₀ g_bg a ha_super hLip
      Phi₁ hS hIcc hPhi₁ hPhi₁0 hδ_lt hsmall₁ hsymm₁ hball₁ hPDE₁ with
    ⟨force₁, u₁, field₁, htrace₁, hlink₁, heq₁, hforce₁,
      _hfieldRep₁, hforceRep₁, hpath₁⟩
  rcases smoothGeom_strong (I := I) (M := M) g₀ g_bg a ha_super hLip
      Phi₂ hS hIcc hPhi₂ hPhi₂0 hδ_lt hsmall₂ hsymm₂ hball₂ hPDE₂ with
    ⟨force₂, u₂, field₂, htrace₂, hlink₂, heq₂, hforce₂,
      _hfieldRep₂, hforceRep₂, hpath₂⟩
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hforceBall₁ : ‖force₁‖ ≤ ρ := by
    refine le_trans (timeL2_norm_le_of_ae_bound force₁ hB ?_) hforceBudget
    filter_upwards [hforceRep₁, hmem] with t hrep ht
    rw [hrep]
    exact hNbound₁ t ht
  have hforceBall₂ : ‖force₂‖ ≤ ρ := by
    refine le_trans (timeL2_norm_le_of_ae_bound force₂ hB ?_) hforceBudget
    filter_upwards [hforceRep₂, hmem] with t hrep ht
    rw [hrep]
    exact hNbound₂ t ht
  have huniq := deTurckStrong_unique (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρ hcontract force₁ force₂ u₁ u₂ field₁ field₂
    htrace₁ htrace₂ hlink₁ hlink₂ heq₁ heq₂ hforce₁ hforce₂
    hforceBall₁ hforceBall₂
  intro t ht
  have hu := congrArg
    (fun v : timeH1 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T =>
      v.toFun t) huniq.2.2
  rw [hpath₁ t ht, hpath₂ t ht] at hu
  apply ccToHs_injective (I := I) (M := M) g₀ 2 (a : ℝ)
  simpa only [ccHs_eq_smoothHs] using hu

/-- Local uniqueness of two smooth Ricci--DeTurck metric families on one
already translated regular-time window.  The common carrier `q` is their
actual metric at the left endpoint.  Joint tensor regularity, symmetry, the
zero initial perturbation, and the realization identity are all derived from
the metric-difference construction rather than supplied as extra inputs. -/
theorem metricRD_unique
    {D : RealTimeInterval}
    (G₁ G₂ : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG₁ : MetricFamilySmoothOn (I := I) (M := M) D G₁)
    (hG₂ : MetricFamilySmoothOn (I := I) (M := M) D G₂)
    (q g_bg : SmoothRiemannianMetric I M) (c : ℝ)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {L C₁ C₂ : ℝ≥0}
    (hLip : LipschitzWith L
      (deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a))
    (hsingle : ∀ (v v' :
      tensorHs (I := I) (M := M) q 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a v -
          deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a v'‖ ≤
        (C₁ : ℝ) * max
            ‖tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v‖
            ‖tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v'‖ * ‖v - v'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (v - v')‖)
    {T ρ B : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hρ : 0 ≤ ρ)
    (hB : 0 ≤ B) (hforceBudget : Real.sqrt T * B ≤ ρ)
    (hcontract :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    {S : Set ℝ} (hS : IsOpen S) (hIcc : Icc (0 : ℝ) T ⊆ S)
    (hmap₁ : ∀ t ∈ S, c + t ∈ D.regular)
    (hmap₂ : ∀ t ∈ S, c + t ∈ D.regular)
    (hG₁0 : G₁.metric c = q) (hG₂0 : G₂.metric c = q)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hsmall₁ : ∀ t ∈ Icc (0 : ℝ) T,
      gFibreOpBound (I := I) (M := M) q
        (ccTensorBilinSymm (I := I) q
          (metricDifferenceCcTensor (I := I) (M := M) q
            (G₁.metric (c + t)))) δ)
    (hsmall₂ : ∀ t ∈ Icc (0 : ℝ) T,
      gFibreOpBound (I := I) (M := M) q
        (ccTensorBilinSymm (I := I) q
          (metricDifferenceCcTensor (I := I) (M := M) q
            (G₂.metric (c + t)))) δ)
    (hball₁ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) q ((a : ℝ) + 2)
        (metricDifferenceCcTensor (I := I) (M := M) q
          (G₁.metric (c + t)))‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) q a ha_super)).1)
    (hball₂ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) q ((a : ℝ) + 2)
        (metricDifferenceCcTensor (I := I) (M := M) q
          (G₂.metric (c + t)))‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) q a ha_super)).1)
    (hPDE₁ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivAt (fun tau => (G₁.metric (c + tau)).inner x v w)
          (deTurckRicciRHS (I := I) g_bg (G₁.metric (c + t)) x v w) t)
    (hPDE₂ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivAt (fun tau => (G₂.metric (c + tau)).inner x v w)
          (deTurckRicciRHS (I := I) g_bg (G₂.metric (c + t)) x v w) t)
    (hNbound₁ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a
        (smoothCcToTensorHs (I := I) (M := M) q ((a : ℝ) + 2)
          (metricDifferenceCcTensor (I := I) (M := M) q
            (G₁.metric (c + t))))‖ ≤ B)
    (hNbound₂ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a
        (smoothCcToTensorHs (I := I) (M := M) q ((a : ℝ) + 2)
          (metricDifferenceCcTensor (I := I) (M := M) q
            (G₂.metric (c + t))))‖ ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) T, G₁.metric (c + t) = G₂.metric (c + t) := by
  let Phi₁ : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G₁.metric (c + t))
  let Phi₂ : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G₂.metric (c + t))
  have hPhi₁ := metricDiff_shift (I := I) (M := M) G₁ hG₁ q c hmap₁
  have hPhi₂ := metricDiff_shift (I := I) (M := M) G₂ hG₂ q c hmap₂
  have hPhi₁0 : Phi₁ 0 = 0 := by
    simp only [Phi₁, add_zero, hG₁0, metricDifferenceCcTensor_self]
  have hPhi₂0 : Phi₂ 0 = 0 := by
    simp only [Phi₂, add_zero, hG₂0, metricDifferenceCcTensor_self]
  have hsymm₁ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        ccTensorBilin (I := I) q (Phi₁ t) x v w =
          ccTensorBilin (I := I) q (Phi₁ t) x w v := by
    intro t _ x v w
    exact metricDiff_symm (I := I) (M := M) q (G₁.metric (c + t)) x v w
  have hsymm₂ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace I x,
        ccTensorBilin (I := I) q (Phi₂ t) x v w =
          ccTensorBilin (I := I) q (Phi₂ t) x w v := by
    intro t _ x v w
    exact metricDiff_symm (I := I) (M := M) q (G₂.metric (c + t)) x v w
  have hunit₁ := metricDiff_pde (I := I) (M := M) q g_bg
    (fun t => G₁.metric (c + t)) hδ_lt hsmall₁ hPDE₁
  have hunit₂ := metricDiff_pde (I := I) (M := M) q g_bg
    (fun t => G₂.metric (c + t)) hδ_lt hsmall₂ hPDE₂
  have hPhiEq := smoothGeom_unique (I := I) (M := M) q g_bg a ha_super
    hLip hsingle hT hT1 hρ hB hforceBudget hcontract Phi₁ Phi₂ hS hIcc
    hPhi₁ hPhi₂ hPhi₁0 hPhi₂0 hδ_lt hsmall₁ hsmall₂ hsymm₁ hsymm₂
    hball₁ hball₂ hunit₁ hunit₂ hNbound₁ hNbound₂
  intro t ht
  calc
    G₁.metric (c + t) = tensorSectionRealizeMetric (I := I) q (Phi₁ t)
        hδ_lt (hsmall₁ t ht) :=
      (realize_metricDiff (I := I) (M := M) q (G₁.metric (c + t))
        hδ_lt (hsmall₁ t ht)).symm
    _ = tensorSectionRealizeMetric (I := I) q (Phi₂ t)
        hδ_lt (hsmall₂ t ht) := by rw [hPhiEq t ht]
    _ = G₂.metric (c + t) :=
      realize_metricDiff (I := I) (M := M) q (G₂.metric (c + t))
        hδ_lt (hsmall₂ t ht)

/-- Automatic positive-window continuation for two smooth Ricci--DeTurck
metric families which already agree at one regular interior time.  All
spectral truncation, fibre-smallness, forcing-ball, and mixed-contraction
budgets are chosen from continuity at the zero metric difference. -/
theorem metricRD_local
    {D : RealTimeInterval}
    (G₁ G₂ : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG₁ : MetricFamilySmoothOn (I := I) (M := M) D G₁)
    (hG₂ : MetricFamilySmoothOn (I := I) (M := M) D G₂)
    (q g_bg : SmoothRiemannianMetric I M) (c : ℝ)
    {S : Set ℝ} (hS : IsOpen S) (h0S : (0 : ℝ) ∈ S)
    (hmap : ∀ t ∈ S, c + t ∈ D.regular)
    (hG₁0 : G₁.metric c = q) (hG₂0 : G₂.metric c = q)
    (hPDE₁ : ∀ t ∈ S, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (G₁.metric (c + tau)).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (G₁.metric (c + t)) x v w) t)
    (hPDE₂ : ∀ t ∈ S, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (G₂.metric (c + tau)).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (G₂.metric (c + t)) x v w) t) :
    ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Icc (0 : ℝ) T, G₁.metric (c + t) = G₂.metric (c + t) := by
  classical
  let a : ℕ := 2 * Module.finrank ℝ E + 10
  have ha : 2 * Module.finrank ℝ E + 10 ≤ a := le_rfl
  let Phi₁ : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G₁.metric (c + t))
  let Phi₂ : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G₂.metric (c + t))
  have hPhi₁ := metricDiff_shift (I := I) (M := M) G₁ hG₁ q c hmap
  have hPhi₂ := metricDiff_shift (I := I) (M := M) G₂ hG₂ q c hmap
  have hPhi₁0 : Phi₁ 0 = 0 := by
    simp only [Phi₁, add_zero, hG₁0, metricDifferenceCcTensor_self]
  have hPhi₂0 : Phi₂ 0 = 0 := by
    simp only [Phi₂, add_zero, hG₂0, metricDifferenceCcTensor_self]
  let hex := deTurckSobolevNHa2_exists_of_super
    (I := I) (M := M) q a ha
  let R₀ : ℝ := (Classical.choose hex).1
  let δ₀ : ℝ := (Classical.choose hex).2
  have hR₀ : 0 < R₀ := by
    simpa only [R₀, hex] using (Classical.choose_spec hex).1
  have hδ₀_lt : δ₀ < 1 := by
    exact lt_of_le_of_lt (Classical.choose_spec hex).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨T₁, hT₁, hIcc₁, hball₁⟩ :=
    exists_pathBall (I := I) (M := M) q (a + 2) Phi₁ hS h0S hPhi₁ hPhi₁0 hR₀
  obtain ⟨T₂, hT₂, hIcc₂, hball₂⟩ :=
    exists_pathBall (I := I) (M := M) q (a + 2) Phi₂ hS h0S hPhi₂ hPhi₂0 hR₀
  set Tpre : ℝ := min T₁ T₂ with hTpre_def
  have hTpre : 0 < Tpre := by rw [hTpre_def]; exact lt_min hT₁ hT₂
  have hTpre₁ : Tpre ≤ T₁ := by rw [hTpre_def]; exact min_le_left _ _
  have hTpre₂ : Tpre ≤ T₂ := by rw [hTpre_def]; exact min_le_right _ _
  have hsub₁ : Icc (0 : ℝ) Tpre ⊆ Icc (0 : ℝ) T₁ :=
    Set.Icc_subset_Icc le_rfl hTpre₁
  have hsub₂ : Icc (0 : ℝ) Tpre ⊆ Icc (0 : ℝ) T₂ :=
    Set.Icc_subset_Icc le_rfl hTpre₂
  have hIccpre : Icc (0 : ℝ) Tpre ⊆ S := fun _ ht => hIcc₁ (hsub₁ ht)
  have hcast : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  have hball₁pre : ∀ t ∈ Icc (0 : ℝ) Tpre,
      ‖smoothCcToTensorHs (I := I) (M := M) q ((a : ℝ) + 2) (Phi₁ t)‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) q a ha)).1 := by
    intro t ht
    have h := hball₁ t (hsub₁ ht)
    simpa only [hcast, R₀, hex] using h
  have hball₂pre : ∀ t ∈ Icc (0 : ℝ) Tpre,
      ‖smoothCcToTensorHs (I := I) (M := M) q ((a : ℝ) + 2) (Phi₂ t)‖ ≤
        (Classical.choose
          (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) q a ha)).1 := by
    intro t ht
    have h := hball₂ t (hsub₂ ht)
    simpa only [hcast, R₀, hex] using h
  have hsmall₁pre : ∀ t ∈ Icc (0 : ℝ) Tpre,
      gFibreOpBound (I := I) (M := M) q
        (ccTensorBilinSymm (I := I) q (Phi₁ t)) δ₀ := by
    intro t ht
    exact (Classical.choose_spec hex).2.2 _ (hball₁pre t ht)
  have hsmall₂pre : ∀ t ∈ Icc (0 : ℝ) Tpre,
      gFibreOpBound (I := I) (M := M) q
        (ccTensorBilinSymm (I := I) q (Phi₂ t)) δ₀ := by
    intro t ht
    exact (Classical.choose_spec hex).2.2 _ (hball₂pre t ht)
  let L := deTurckLipConstSymm
    (I := I) (M := M) (g₀ := q) (g_bg := g_bg) a ha
  have hLip : LipschitzWith L
      (deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a) :=
    deTurckSobolevNHa2Symm_lipschitzWith_lipConst
      (I := I) (M := M) (g₀ := q) (g_bg := g_bg) a ha
  have hcont₁ : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) q
        ((a : ℝ) + 2) (Phi₁ t)) (Icc (0 : ℝ) Tpre) := by
    have h := (smoothHs_path_cd (I := I) (M := M) q (a + 2)
      Phi₁ hS hPhi₁).continuousOn.mono hIccpre
    rwa [hcast] at h
  have hcont₂ : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) q
        ((a : ℝ) + 2) (Phi₂ t)) (Icc (0 : ℝ) Tpre) := by
    have h := (smoothHs_path_cd (I := I) (M := M) q (a + 2)
      Phi₂ hS hPhi₂).continuousOn.mono hIccpre
    rwa [hcast] at h
  obtain ⟨B₁, hB₁, hN₁⟩ := exists_pathNBound
    (I := I) (M := M) q (a : ℝ) hLip hTpre.le _ hcont₁
  obtain ⟨B₂, hB₂, hN₂⟩ := exists_pathNBound
    (I := I) (M := M) q (a : ℝ) hLip hTpre.le _ hcont₂
  set B : ℝ := max B₁ B₂ with hBdef
  have hB : 0 ≤ B := le_trans hB₁ (by rw [hBdef]; exact le_max_left _ _)
  have hN₁B : ∀ t ∈ Icc (0 : ℝ) Tpre,
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a
        (smoothCcToTensorHs (I := I) (M := M) q
          ((a : ℝ) + 2) (Phi₁ t))‖ ≤ B := by
    intro t ht
    exact le_trans (hN₁ t ht) (by rw [hBdef]; exact le_max_left _ _)
  have hN₂B : ∀ t ∈ Icc (0 : ℝ) Tpre,
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) q g_bg a
        (smoothCcToTensorHs (I := I) (M := M) q
          ((a : ℝ) + 2) (Phi₂ t))‖ ≤ B := by
    intro t ht
    exact le_trans (hN₂ t ht) (by rw [hBdef]; exact le_max_right _ _)
  obtain ⟨C₁, C₂, hmix⟩ :=
    deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise
      (I := I) (M := M) (g₀ := q) (g_bg := g_bg) a ha
  obtain ⟨rho, Tmix, hrho, hTmix, hbudget⟩ :=
    exists_mixBudget C₁ C₂ hB
  set T : ℝ := min Tpre Tmix with hTdef
  have hT : 0 < T := by rw [hTdef]; exact lt_min hTpre hTmix
  have hTpre' : T ≤ Tpre := by rw [hTdef]; exact min_le_left _ _
  have hTmix' : T ≤ Tmix := by rw [hTdef]; exact min_le_right _ _
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) Tpre :=
    Set.Icc_subset_Icc le_rfl hTpre'
  have hIcc : Icc (0 : ℝ) T ⊆ S := fun _ ht => hIccpre (hsub ht)
  obtain ⟨hT1, hforce, hcontract⟩ := hbudget hT hTmix'
  refine ⟨T, hT, ?_⟩
  exact metricRD_unique (I := I) (M := M) G₁ G₂ hG₁ hG₂ q g_bg c a ha
    hLip hmix hT hT1 hrho.le hB hforce hcontract hS hIcc hmap hmap
    hG₁0 hG₂0 hδ₀_lt
    (fun t ht => hsmall₁pre t (hsub ht))
    (fun t ht => hsmall₂pre t (hsub ht))
    (fun t ht => hball₁pre t (hsub ht))
    (fun t ht => hball₂pre t (hsub ht))
    (fun t ht => hPDE₁ t (hIcc ht))
    (fun t ht => hPDE₂ t (hIcc ht))
    (fun t ht => hN₁B t (hsub ht))
    (fun t ht => hN₂B t (hsub ht))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
