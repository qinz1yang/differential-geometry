import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Data.EReal.Basic
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed

import DifferentialGeometry.Analysis.Sobolev.Intrinsic.SmoothEntropyNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyCutoff

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

structure EntropyTest (g : SmoothRiemannianMetric I M) where
  value : M → ℝ
  gradient : M → E
  value_memLp : MemLp value 2 (riemannianVolumeMeasure I M g)
  weak_gradient : HasWeakRiemannianGradLp g value gradient
  gradient_memLp : MemLp (fun x => Real.sqrt (g.inner x (gradient x) (gradient x))) 2
    (riemannianVolumeMeasure I M g)
  nonnegative : ∀ᵐ x ∂(riemannianVolumeMeasure I M g), 0 ≤ value x
  normalized : (∫ x, value x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1


def entropyValue (g : SmoothRiemannianMetric I M) (tau : ℝ) (w : EntropyTest g) : ℝ :=
  (∫ x, 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
      tau * metricScalarAt g x * w.value x ^ 2 -
      w.value x ^ 2 * Real.log (w.value x ^ 2)
      ∂(riemannianVolumeMeasure I M g)) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * tau) - Module.finrank ℝ E

def muSobolev (g : SmoothRiemannianMetric I M) (tau : ℝ) : EReal :=
  ⨅ w : EntropyTest g, (entropyValue g tau w : EReal)

def muSmooth (g : SmoothRiemannianMetric I M) (tau : ℝ) : EReal :=
  ⨅ (w : EntropyTest g) (_ : ContMDiff I 𝓘(ℝ, ℝ) ∞ w.value)
    (_ : ∀ x, 0 < w.value x), (entropyValue g tau w : EReal)

omit [CompleteSpace E] in
private lemma hasWeakRiemannianGradLp_gradFun_of_contMDiff [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u
      (fun x => DifferentialGeometry.Geometry.Operator.gradFun g u x) := by
  let G₀ : M → E := fun x =>
    ((DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨u, hu⟩ :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)
  have hbase : HasWeakRiemannianGradLp (I := I) (M := M) g u G₀ :=
    hasWeakRiemannianGradLp_of_smooth (I := I) (M := M)
      (DifferentialGeometry.Analysis.Sobolev.Intrinsic.hasWeakRiemannianGrad_grad_g_of_contMDiff
        (I := I) (M := M) g hu)
  refine DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp.hasWeakRiemannianGradLp_congr_ae
    (I := I) (M := M) (g := g) (u := u) (u' := u) (G := G₀)
    (G' := fun x => DifferentialGeometry.Geometry.Operator.gradFun g u x)
    (Filter.EventuallyEq.refl _ u) ?_ hbase
  filter_upwards with x
  exact DifferentialGeometry.Geometry.Operator.grad_g_apply (I := I) g ⟨u, hu⟩ x

private lemma exists_entropyTest_approx [I.Boundaryless] [Nonempty M]
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 ≤ Module.finrank ℝ E) {tau : ℝ} (htau : 0 < tau)
    (hRc : Continuous (fun x : M => metricScalarAt g x))
    (w : EntropyTest g) {eps : ℝ} (heps : 0 < eps) :
    ∃ W' : EntropyTest g, ContMDiff I 𝓘(ℝ, ℝ) ∞ W'.value ∧
      (∀ x : M, 0 < W'.value x) ∧
      entropyValue g tau W' ≤ entropyValue g tau w + eps := by

  obtain ⟨v, hv, hmass, hbound⟩ :=
    HasWeakRiemannianGradLp.exists_smooth_normalized_wform_le (I := I) (M := M)
      (g := g) hdim w.weak_gradient w.value_memLp w.gradient_memLp w.normalized
      hRc tau (by linarith : 0 < eps / 2)
  have hvgradi : Integrable (fun x => g.inner x
      (DifferentialGeometry.Geometry.Operator.gradientFun (I := I) g v x)
      (DifferentialGeometry.Geometry.Operator.gradientFun (I := I) g v x))
      (riemannianVolumeMeasure I M g) :=
    integrable_metric_energy_of_memLp (I := I) (M := M) g
      (DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
        (I := I) (M := M) g 2 hv)
  obtain ⟨v', hv', hv'pos, hv'mass, hbound'⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Entropy.exists_pos_wform (I := I) (M := M) g
      hv hmass hvgradi hRc (C := 0) (tau := tau) (δ := eps / 2) htau.le
      (by linarith : 0 < eps / 2)
  have hv'2 : MemLp v' 2 (riemannianVolumeMeasure I M g) :=
    (MemW1pIntrinsicLp_of_contMDiff (I := I) (M := M) g 2 hv').1
  have hgrad2 : MemLp (fun x => Real.sqrt
      (g.inner x (DifferentialGeometry.Geometry.Operator.gradFun g v' x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v' x))) 2
      (riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_g_norm_gradFun_smooth
      (I := I) (M := M) g 2 hv'
  let W' : EntropyTest g :=
    { value := v'
      gradient := fun x => DifferentialGeometry.Geometry.Operator.gradFun g v' x
      value_memLp := hv'2
      weak_gradient := hasWeakRiemannianGradLp_gradFun_of_contMDiff (I := I) (M := M) hv'
      gradient_memLp := hgrad2
      nonnegative := Filter.Eventually.of_forall fun x => (hv'pos x).le
      normalized := hv'mass }
  refine ⟨W', hv', hv'pos, ?_⟩
  have hF' : entropyValue g tau W' =
      (∫ x, 4 * tau * g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun g v' x)
          (DifferentialGeometry.Geometry.Operator.gradFun g v' x) +
        tau * metricScalarAt g x * v' x ^ 2 - v' x ^ 2 * Real.log (v' x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * tau) -
        Module.finrank ℝ E := rfl
  have hFw : entropyValue g tau w =
      (∫ x, 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
        tau * metricScalarAt g x * w.value x ^ 2 - w.value x ^ 2 * Real.log (w.value x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * tau) -
        Module.finrank ℝ E := rfl
  have hb' : (∫ x, 4 * tau * g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun g v' x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v' x) +
      tau * metricScalarAt g x * v' x ^ 2 - v' x ^ 2 * Real.log (v' x ^ 2)
      ∂(riemannianVolumeMeasure I M g)) ≤
      (∫ x, 4 * tau * g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun g v x)
          (DifferentialGeometry.Geometry.Operator.gradFun g v x) +
        tau * metricScalarAt g x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) + eps / 2 := by
    simpa only [zero_mul, add_zero,
      DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun] using hbound'
  have hb : (∫ x, 4 * tau * g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun g v x)
        (DifferentialGeometry.Geometry.Operator.gradFun g v x) +
      tau * metricScalarAt g x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2)
      ∂(riemannianVolumeMeasure I M g)) ≤
      (∫ x, 4 * tau * g.inner x (w.gradient x) (w.gradient x) +
        tau * metricScalarAt g x * w.value x ^ 2 - w.value x ^ 2 * Real.log (w.value x ^ 2)
        ∂(riemannianVolumeMeasure I M g)) + eps / 2 := hbound
  rw [hF', hFw]
  linarith
theorem mu_sobolev_relaxation [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    {tau : ℝ} (htau : 0 < tau) :
    (∀ w : EntropyTest g, Integrable (fun x => w.value x ^ 2 * Real.log (w.value x ^ 2))
      (riemannianVolumeMeasure I M g)) ∧ muSobolev g tau = muSmooth g tau := by
  refine ⟨?_, ?_⟩
  · intro w
    exact (show MemW1pIntrinsicLp (I := I) (M := M) g 2 w.value from
      ⟨w.value_memLp, w.gradient, w.weak_gradient, w.gradient_memLp⟩)
      |>.integrable_sq_mul_log_sq hdim
  · have hRc : Continuous (fun x : M => metricScalarAt g x) :=
      (metricScalar_smooth (I := I) (M := M) g).continuous
    have hle : muSobolev g tau ≤ muSmooth g tau := by
      unfold muSobolev muSmooth
      refine le_iInf fun w => le_iInf fun h1 => le_iInf fun h2 => ?_
      exact iInf_le (fun w : EntropyTest g => (entropyValue g tau w : EReal)) w
    by_cases hM : Nonempty M
    · have hMne : Nonempty M := hM
      have hge : muSmooth g tau ≤ muSobolev g tau := by
        unfold muSobolev muSmooth
        refine le_iInf fun w : EntropyTest g => ?_
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
        have hwlt : entropyValue g tau w < r := EReal.coe_lt_coe_iff.mp hr1
        obtain ⟨W', hW'smooth, hW'pos, hW'le⟩ :=
          exists_entropyTest_approx (I := I) (M := M) g hdim htau hRc w
            (eps := (r - entropyValue g tau w) / 2) (by linarith)
        have hW'r : entropyValue g tau W' < r := by linarith
        have hchain : (r : EReal) < (entropyValue g tau W' : EReal) :=
          lt_of_lt_of_le hr2 (le_trans (iInf_le _ W')
            (le_trans (iInf_le _ hW'smooth) (iInf_le _ hW'pos)))
        exact absurd hchain (not_lt_of_ge (EReal.coe_le_coe hW'r.le))
      exact le_antisymm hle hge
    · have hMempty : IsEmpty M := not_nonempty_iff.mp hM
      have hempty : IsEmpty (EntropyTest g) := ⟨fun w => by
        have hμ : riemannianVolumeMeasure I M g = 0 :=
          MeasureTheory.Measure.eq_zero_of_isEmpty (riemannianVolumeMeasure I M g)
        have hz : (∫ x, w.value x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 0 := by
          rw [hμ]
          simp
        have hnorm := w.normalized
        rw [hz] at hnorm
        exact zero_ne_one hnorm⟩
      have h1 : muSobolev g tau = ⊤ := by
        unfold muSobolev
        exact iInf_of_empty _
      have h2 : muSmooth g tau = ⊤ := by
        unfold muSmooth
        exact iInf_of_empty _
      rw [h1, h2]

theorem mu_monotone [I.Boundaryless] {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E) {t1 t2 tau : ℝ}
    (h1 : t1 ∈ D.carrier) (h2 : t2 ∈ D.carrier) (hle : t1 ≤ t2) (htau : 0 < tau) :
    muSmooth (S.base.metric t1) (tau + t2 - t1) ≤ muSmooth (S.base.metric t2) tau := by
  sorry


theorem mu_compact_scale_lower [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ, ∀ tau ∈ Set.Icc a b, (L : EReal) ≤ muSmooth g tau := by
  sorry


def cutoffEntropyConstant (n : ℕ) (D b : ℝ) : ℝ :=
  36 * D + b + D / Real.exp 1 - (n : ℝ) / 2 * Real.log (4 * Real.pi) - n

theorem cutoff_entropy_doubling [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    (x : M) {r D b : ℝ} (hr : 0 < r) (hD : 1 ≤ D) (hb : 0 ≤ b)
    (hdoubling : (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal ≤
      D * (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x (r / 2))).toReal)
    (hscalar : ∀ y ∈ riemannianBallOf (I := I) g x r, metricScalarAt g y ≤ b * r⁻¹ ^ 2) :
    muSobolev g (r ^ 2) ≤
      ((Real.log ((riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal /
        r ^ Module.finrank ℝ E) + cutoffEntropyConstant (Module.finrank ℝ E) D b : ℝ) : EReal) := by
  let _ := hdim
  let _ := hb
  let μ := riemannianVolumeMeasure I M g
  let U : Set M := riemannianBallOf (I := I) g x r
  have hVpos : 0 < (μ U).toReal := by
    simpa only [μ, U, riemannianBallOf] using
      DifferentialGeometry.Geometry.Riemannian.VolumeComparison.edist_vol_pos
        (I := I) (M := M) g x hr
  obtain ⟨w, G, _hwcont, hw2, hwweak, hwgrad2, hwpos, hwmass, hwbound⟩ :=
    exists_normalized_cutoff_wform (I := I) (M := M) g x hr hD hdoubling
      (R := fun y => metricScalarAt (I := I) (M := M) g y)
      (metricScalar_smooth (I := I) (M := M) g).continuous
      (fun y hy => hscalar y hy)
  let W : EntropyTest g :=
    { value := w
      gradient := G
      value_memLp := hw2
      weak_gradient := hwweak
      gradient_memLp := hwgrad2
      nonnegative := Filter.Eventually.of_forall hwpos
      normalized := hwmass }
  refine (iInf_le (fun w : EntropyTest g => (entropyValue g (r ^ 2) w : EReal)) W).trans ?_
  have hbound : (∫ y, 4 * r ^ 2 * g.inner y (G y) (G y) +
        r ^ 2 * metricScalarAt g y * w y ^ 2 -
        w y ^ 2 * Real.log (w y ^ 2) ∂μ) ≤
      36 * D + b + Real.log (μ U).toReal := by
    simpa only [μ, U] using hwbound
  have hlog4 : Real.log (4 * Real.pi * r ^ 2) =
      Real.log (4 * Real.pi) + 2 * Real.log r := by
    rw [Real.log_mul (by positivity) (pow_ne_zero 2 hr.ne'), Real.log_pow]
    norm_num
  have hkey : entropyValue g (r ^ 2) W ≤
      Real.log ((μ U).toReal / r ^ Module.finrank ℝ E) +
        cutoffEntropyConstant (Module.finrank ℝ E) D b := by
    have hE : entropyValue g (r ^ 2) W =
        (∫ y, 4 * r ^ 2 * g.inner y (G y) (G y) +
          r ^ 2 * metricScalarAt g y * w y ^ 2 -
          w y ^ 2 * Real.log (w y ^ 2) ∂μ) -
          (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi * r ^ 2) -
          Module.finrank ℝ E := rfl
    have hlogV : Real.log ((μ U).toReal / r ^ Module.finrank ℝ E) =
        Real.log (μ U).toReal - (Module.finrank ℝ E : ℝ) * Real.log r := by
      rw [Real.log_div hVpos.ne' (pow_ne_zero _ hr.ne'), Real.log_pow]
    have hconst : cutoffEntropyConstant (Module.finrank ℝ E) D b =
        36 * D + b + D / Real.exp 1 -
          (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi) -
          Module.finrank ℝ E := rfl
    have hDe : 0 ≤ D / Real.exp 1 :=
      div_nonneg (le_trans zero_le_one hD) (Real.exp_pos 1).le
    rw [hE, hlogV, hlog4, hconst]
    linarith only [hbound, hDe]
  exact EReal.coe_le_coe hkey


theorem local_entropy_volume [I.Boundaryless]
    (hdim : 2 ≤ Module.finrank ℝ E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C : ℝ, ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
      (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
        -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) →
      (∀ y ∈ riemannianBallOf (I := I) g x r, metricScalarAt g y ≤ b * r⁻¹ ^ 2) →
      muSobolev g (r ^ 2) ≤
        ((Real.log ((riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal /
          r ^ Module.finrank ℝ E) + C : ℝ) : EReal) := by
  sorry

theorem strong_scalar_no_local_collapsing [I.Boundaryless]
    [T2Space (TangentBundle I M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    {rho : ℝ} (hrho : 0 < rho) : StrongScalarNoLocalCollapsing S rho := by
  sorry

theorem spatial_no_local_collapsing [I.Boundaryless]
    [T2Space (TangentBundle I M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    {rho : ℝ} (hrho : 0 < rho) : SpatialNoLocalCollapsing S rho := by
  let c := scalarFromRmRadius (Module.finrank ℝ E)
  have hc : 0 < c := scalarFromRmRadius_pos _
  have h := spatialNoLocalCollapsing_of_strongScalar
    (strong_scalar_no_local_collapsing hT S hS hdim (div_pos hrho hc))
  have hscale : scalarFromRmRadius (Module.finrank ℝ E) * (rho / c) = rho := by
    change c * (rho / c) = rho
    field_simp [hc.ne']
  rwa [hscale] at h

theorem local_metric_injectivity [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
        [T2Space (TangentBundle I M)] (g : SmoothRiemannianMetric I M),
        RiemannianMetricComplete g → ∀ x : M, ∀ r : ℝ, 0 < r →
          (∀ y ∈ riemannianBallOf (I := I) g x r,
            r ^ 4 * Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y) ≤ 1) →
          ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) ≤
            riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r) →
          Set.InjOn (fun v : TangentSpace I x =>
            DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I) g x v)
            {v | Real.sqrt (g.inner x v v) < iota * r} := by
  sorry

omit [CompleteSpace E] in
theorem parabolic_noncollapse_of_spatial {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {rho : ℝ}
    (h : SpatialNoLocalCollapsing S rho) : ParabolicNoLocalCollapsing S rho :=
  parabolicNoLocalCollapsing_of_spatial h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
