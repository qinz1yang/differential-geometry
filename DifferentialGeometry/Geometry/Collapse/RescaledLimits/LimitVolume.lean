import DifferentialGeometry.Geometry.Collapse.LocalVolumeRescaledCorollaries
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.PointedLimit
import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume

/-!
# LC06: the full-dimensional local volume input for actual rescaled sequences

Blueprint 207A, LC06 (`found:collapse-local-volume-input`, A:20162): for sequences as in LC05
that converge to a limit `(Y, q)`, `dim_H Y > 2` implies
`liminf_i Vol_{ĝ i} B_{ĝ i}(p i, 2) > 0`. The metric argument is LC15
(`PointedGHConverges.eventually_normalizedHausdorffMeasure_ball_lower_bound`); this file binds it
to the actual Riemannian data:

* `normalizedHausdorffMeasure_rescale_eq_riemannianVolumeMeasure`: on a source whose metric
  realizes `g`, the normalized `dim`-dimensional Hausdorff measure of the rescaled metric `ρ⁻¹ d`
  is the Riemannian volume of `ρ⁻² g`; `normalizedHausdorffMeasure_rescale_ball_eq_ballVolume` is
  the ball form in dimension three.
* `eventually_rescaled_ballVolume_lower_of_dimH_gt_two`: LC06 for ANY pointed limit of the
  rescaled sequence; the limit's completeness, comparison and the bound `dim_H ≤ 3` are derived,
  not assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter MeasureTheory Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u v

section Single

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- On a source whose metric realizes `g`, the normalized Hausdorff measure of dimension
`dim M` is the Riemannian volume of `g`. -/
theorem normalizedHausdorffMeasure_eq_riemannianVolumeMeasure_of_riemannian
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    (normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have : IsRiemannianManifold I M := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  exact Geometry.Metric.normalizedHausdorffMeasure_eq_riemannianVolumeMeasure g
    (isMetricNorm_of_riemannianBundle g)

/-- The rescaled metric `ρ⁻¹ d` has normalized Hausdorff measure the Riemannian volume of
`ρ⁻² g`. -/
theorem normalizedHausdorffMeasure_rescale_eq_riemannianVolumeMeasure
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {ρ : ℝ} (hρ : 0 < ρ) :
    letI := m.rescale ρ⁻¹ (inv_pos.mpr hρ)
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    (normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M
        (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g) :=
  normalizedHausdorffMeasure_eq_riemannianVolumeMeasure_of_riemannian (m := m.rescale ρ⁻¹ _) _
    (riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) g hmetric hρ)

/-- Ball form in dimension three: the normalized three-dimensional Hausdorff measure of a ball of
the rescaled metric `ρ⁻¹ d` is the `ballVolume` of `ρ⁻² g`. -/
theorem normalizedHausdorffMeasure_rescale_ball_eq_ballVolume
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hdim : Module.finrank ℝ E = 3) {ρ : ℝ} (hρ : 0 < ρ) (x : M) (r : ℝ) :
    letI := m.rescale ρ⁻¹ (inv_pos.mpr hρ)
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    normalizedHausdorffMeasure 3 (Metric.ball x r) =
      ballVolume (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g) x r := by
  let : MetricSpace M := m.rescale ρ⁻¹ (inv_pos.mpr hρ)
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have h := normalizedHausdorffMeasure_rescale_eq_riemannianVolumeMeasure (m := m) g hmetric hρ
  rw [hdim] at h
  have hball : riemannianBallOf (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g) x r =
      Metric.ball x r := by
    ext y
    change riemannianEDistOf _ x y < ENNReal.ofReal r ↔ _
    rw [riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) g hmetric hρ, Metric.mem_ball,
      dist_comm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg
  rw [ballVolume, hball]
  exact congrArg (fun μ : Measure M => μ (Metric.ball x r)) h

end Single

section Sequence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LC06** for actual sequences. Let the sources satisfy the LC05 hypotheses and let the
rescaled sequence `(X i, ρ i⁻¹ d, p i)` converge to ANY pointed limit `(Y, q)` with
`dim_H Y > 2`. Then the `ρ i⁻² g i`-volume of the radius-`2` ball about `p i` is eventually
bounded below by a positive constant. The completeness, nonnegative comparison and the bound
`dim_H Y ≤ 3` of the limit are derived from the sources. -/
theorem eventually_rescaled_ballVolume_lower_of_dimH_gt_two (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {ρ L : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹))
    {Y : Type v} [MetricSpace Y] {q : Y}
    (hconv : @PointedGHConverges X (fun i => (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) Y _
      p q)
    (hdimY : 2 < dimH (univ : Set Y)) :
    ∃ v : ℝ, 0 < v ∧ ∀ᶠ i in atTop, ENNReal.ofReal v ≤
      ballVolume (scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i)) (p i) 2 := by
  exact eventually_rescaled_ballVolume_lower_of_localVolume_producer
    (mZ := mX) hdim g hmetric p hρ hL hsec hconv hdimY

end Sequence

end DifferentialGeometry.Geometry.Collapse
