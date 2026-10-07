import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AdditiveDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeComparisonReverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedBallVolumeLower
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

/-!
# CH12-O9, Group A (part 1): noncollapsing of an ancient limit from a time-zero volume growth

KL Cor. 45.1/45.13 blow-up (G2a-core, DELIVERIES CH12-O9).  For an ancient Ricci flow `G` on a
connected manifold, complete at all times, with nonnegative curvature operator and bounded scalar
curvature, a Euclidean-type volume growth `v rⁿ ≤ vol_{G 0} B(p, r)` at time `0` (all radii)
propagates to **all** times `t ≤ 0` and **all** centres:

`v rⁿ ≤ vol_{G t} B(x, r)`.

Route: `AVR(G 0) ≥ v/om` (definition), `AVR(G t) ≥ AVR(G 0)` (Hamilton's additive distance bound
`d_t ≤ d_0 + C|t|` and `G 0 ≤ G t` since `Ric ≥ 0`), basepoint independence of the AVR
(Bishop–Gromov), and `AVR ≤ vol B(x,r)/(ω rⁿ)` (definition of the AVR as an infimum).
This replaces earlier-time noncollapsing hypotheses on the blow-up sources (which a local
volume test cannot supply) by the time-zero volume test alone.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

private local instance avrO9Measurable : MeasurableSpace M := borel M
private local instance avrO9Borel : BorelSpace M := ⟨rfl⟩
private local instance avrO9C1 : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
/-- `v/ω ≤ vol B(x,r)/(ω rⁿ)` gives `v rⁿ ≤ vol B(x,r)`. -/
theorem le_ballVolume_of_div_le_ratio_O9 (g : SmoothRiemannianMetric I M) (x : M)
    {v : ℝ≥0∞} {r : ℝ} (hr : 0 < r)
    (h : v / euclideanUnitBallVolume (Module.finrank ℝ E) ≤ normalizedBallVolumeRatio g x r) :
    v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g x r) := by
  set n := Module.finrank ℝ E
  set om := euclideanUnitBallVolume n
  have hom0 : om ≠ 0 := (euclideanUnitBallVolume_pos n).ne'
  have homt : om ≠ ⊤ := euclideanUnitBallVolume_ne_top n
  have hr0 : ENNReal.ofReal (r ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
  have hd0 : om * ENNReal.ofReal (r ^ n) ≠ 0 := mul_ne_zero hom0 hr0
  have hdt : om * ENNReal.ofReal (r ^ n) ≠ ⊤ := ENNReal.mul_ne_top homt ENNReal.ofReal_ne_top
  unfold normalizedBallVolumeRatio at h
  have h2 := (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdt)).mp h
  calc v * ENNReal.ofReal (r ^ n) = v / om * (om * ENNReal.ofReal (r ^ n)) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hom0 homt]
    _ ≤ _ := h2

/-- **Volume growth propagates along an ancient flow with `Rm ≥ 0` and bounded scalar curvature.** -/
theorem ballVolume_lower_all_times_of_ancient_O9 (hdim : 2 ≤ Module.finrank ℝ E)
    [ConnectedSpace M] (G : ℝ → SmoothRiemannianMetric I M)
    (hsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)))
    (hcomplete : ∀ t ≤ (0 : ℝ), RiemannianMetricComplete (G t))
    (hcone : ∀ t ≤ (0 : ℝ), ∀ x : M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    {C : ℝ} (hC : 0 ≤ C) (hscal : ∀ t ≤ (0 : ℝ), ∀ x : M, metricScalarAt (G t) x ≤ C)
    (p : M) (v : ℝ≥0∞)
    (hv : ∀ r : ℝ, 0 < r →
      v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := M) (G 0) (riemannianBallOf (G 0) p r)) :
    ∀ t ≤ (0 : ℝ), ∀ (x : M) (r : ℝ), 0 < r →
      v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := M) (G t) (riemannianBallOf (G t) x r) := by
  intro t ht x r hr
  set S : SolutionOn (I := I) (M := M) (RealTimeInterval.infiniteClosed 0 0 le_rfl) :=
    { base.metric := G } with hSdef
  have hRicNonneg : ∀ s ≤ (0 : ℝ), RicciBoundedBelow (I := I) (G s) 0 := by
    intro s hs y w
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (G s) y (hcone s hs y) w
  -- additive distance bound on `[t, 0]`
  set n := Module.finrank ℝ E
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdim
    linarith
  set K : ℝ := C / ((n : ℝ) - 1) with hKdef
  have hK : 0 ≤ K := div_nonneg hC hn1.le
  have hslab : Icc t 0 ⊆ (RealTimeInterval.infiniteClosed 0 0 le_rfl).carrier :=
    fun s hs => hs.2
  have hreg : Ioo t 0 ⊆ (RealTimeInterval.infiniteClosed 0 0 le_rfl).regular :=
    fun s hs => hs.2
  have hRic2 : ∀ s ∈ Icc t 0, ∀ y : M, ∀ w : TangentSpace I y,
      0 ≤ S.ricciAt s y (vec2 w w) ∧
        S.ricciAt s y (vec2 w w) ≤ ((n : ℝ) - 1) * K * (S.base.metric s).inner y w w := by
    intro s hs y w
    have hcs := hcone s hs.2 y
    refine ⟨metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (G s) y hcs w, ?_⟩
    have h1 := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (G s) y hcs w
    have hR0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative (G s) y hcs
    have hin : 0 ≤ (G s).inner y w w := metric_inner_self_nonneg (G s) y w
    have hRC : metricScalarAt (G s) y / 2 ≤ C := by
      have := hscal s hs.2 y
      linarith
    have hnK : ((n : ℝ) - 1) * K = C := by rw [hKdef]; field_simp
    change metricRicciAt (G s) y (vec2 w w) ≤ ((n : ℝ) - 1) * K * (G s).inner y w w
    rw [hnK]
    exact h1.trans (mul_le_mul_of_nonneg_right hRC hin)
  have hdistAll : ∀ y : M,
      (riemannianEDistOf (I := I) (G t) p y).toReal -
          (10 / 3 : ℝ) * ((n : ℝ) - 1) * Real.sqrt K * (0 - t) ≤
        (riemannianEDistOf (I := I) (G 0) p y).toReal := by
    intro y
    have h := (ricciFlow_additive_distance_bound_of_ricci_upper S hsol hdim
      inferInstance ht hK hslab hreg (fun s hs => hcomplete s hs.2) hRic2 p y).2
    change (riemannianEDistOf (I := I) (G t) p y).toReal -
        (riemannianEDistOf (I := I) (G 0) p y).toReal ≤ _ at h
    linarith
  have hCdist : 0 ≤ (10 / 3 : ℝ) * ((n : ℝ) - 1) * Real.sqrt K * (0 - t) := by
    have : 0 ≤ 0 - t := by linarith
    positivity
  have hmetric : ∀ y : M, ∀ w : TangentSpace I y, (G 0).inner y w w ≤ (G t).inner y w w := by
    intro y w
    have hanti := Perelman.CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior S hsol
      (a := t) (b := 0) hslab hreg
      (fun s hs z u => metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (G s) z
        (hcone s hs.2.le z) u) y w
    exact hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hcomp : asymptoticVolumeRatio (G 0) p ≤ asymptoticVolumeRatio (G t) p :=
    asymptoticVolumeRatio_le_of_additive_distance_and_metric_le (G t) (G 0)
      (hcomplete t ht) (hcomplete 0 le_rfl) (hRicNonneg t ht) (hRicNonneg 0 le_rfl) p hCdist
      hdistAll hmetric
  have hbase : asymptoticVolumeRatio (G t) p = asymptoticVolumeRatio (G t) x :=
    asymptoticVolumeRatio_basepoint_eq (G t) (hcomplete t ht) (hRicNonneg t ht) p x
  have hlow : v / euclideanUnitBallVolume n ≤ asymptoticVolumeRatio (G 0) p :=
    asymptoticVolumeRatio_lower_of_ball_volume_lower (G 0) p v hv
  have hchain : v / euclideanUnitBallVolume n ≤ normalizedBallVolumeRatio (G t) x r :=
    hlow.trans (hcomp.trans (hbase.le.trans (asymptoticVolumeRatio_le_ratio (G t) x hr)))
  exact le_ballVolume_of_div_le_ratio_O9 (G t) x hr hchain

end GC.LongTime.Ch12
