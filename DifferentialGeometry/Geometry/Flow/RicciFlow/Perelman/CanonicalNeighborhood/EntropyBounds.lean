import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Data.EReal.Basic
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed

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

theorem mu_sobolev_relaxation [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    {tau : ℝ} (htau : 0 < tau) :
    (∀ w : EntropyTest g, Integrable (fun x => w.value x ^ 2 * Real.log (w.value x ^ 2))
      (riemannianVolumeMeasure I M g)) ∧ muSobolev g tau = muSmooth g tau := by
  sorry

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
  sorry


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
