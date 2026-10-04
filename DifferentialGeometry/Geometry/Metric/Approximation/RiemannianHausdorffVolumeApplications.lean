import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale

/-!
# Applications of the normalized Hausdorff / Riemannian volume comparison

* `eventually_ballVolume_two_lower_bound_of_pointedGHConverges`: the LC14/LC15 binding. The
  whole-tail normalized Hausdorff lower bound of
  `PointedGHConverges.eventually_normalizedHausdorffMeasure_ball_lower_bound` becomes a whole-tail
  lower bound for the actual Riemannian `ballVolume` of the sequence metrics, with the same
  late tail and the constant divided by `64`.
* `lengthMetric_normalizedHausdorffMeasure_comparison_sixtyFour`: every smooth Riemannian
  three-manifold (regular, σ-compact, possibly disconnected), equipped with the extended length
  distance of its own metric, satisfies the two-sided comparison with constant `64` on all sets.
* `roundThreeSphere_normalizedHausdorffMeasure_comparison_sixtyFour`: the actual round metric on
  the unit three-sphere of Euclidean four-space.
* `lengthMetric_normalizedHausdorffMeasure_firstVolumeScale`: X67's first volume scale, restated
  in the normalized Hausdorff measure of the length distance of `g`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- LC14/LC15: for a pointed sequence of complete Riemannian three-manifolds, each carrying the
length distance of its metric, the hypotheses of the metric volume engine
`PointedGHConverges.eventually_normalizedHausdorffMeasure_ball_lower_bound` give one positive
lower bound for the Riemannian volume of the radius-two balls on the whole late tail. -/
theorem eventually_ballVolume_two_lower_bound_of_pointedGHConverges
    {X : Type v} [MetricSpace X] {Z : ℕ → Type u}
    [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
    [∀ n, ChartedSpace H (Z n)] [∀ n, IsManifold I ∞ (Z n)] [∀ n, SigmaCompactSpace (Z n)]
    [∀ n, RiemannianBundle (fun x : Z n ↦ TangentSpace I x)]
    [∀ n, IsRiemannianManifold I (Z n)]
    [∀ n, IsContinuousRiemannianBundle E (fun x : Z n ↦ TangentSpace I x)]
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hEnorm : ∀ n, IsMetricNorm (I := I) (M := Z n) (g n)) (hdim : Module.finrank ℝ E = 3)
    {p : ∀ n, Z n} {x : X} (hconv : GC.MetricGeometry.PointedGHConverges p x)
    (hcurves : ∀ n, ∀ q y : Z n, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → Z n, Continuous c ∧ c 0 = q ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist q y + η))
    (hcomp : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, fourPointComparison 1 (Metric.ball (p n) R))
    (hcompX : fourPointComparison 0 (univ : Set X))
    (hdimlo : 2 < dimH (univ : Set X)) (hdimhi : dimH (univ : Set X) ≤ 3) :
    ∃ w : ℝ, 0 < w ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal w ≤ DifferentialGeometry.Geometry.Collapse.ballVolume (g n) (p n) 2 := by
  let _ : ∀ n, MeasurableSpace (Z n) := fun n => borel (Z n)
  have _ : ∀ n, BorelSpace (Z n) := fun _ => ⟨rfl⟩
  obtain ⟨w, hw, htail⟩ :=
    hconv.eventually_normalizedHausdorffMeasure_ball_lower_bound hcurves hcomp hcompX
      hdimlo hdimhi
  refine ⟨w / 64, by positivity, ?_⟩
  filter_upwards [htail] with n hn
  exact collapse_ballVolume_lower_of_normalizedHausdorffMeasure_lower (g n) (hEnorm n) hdim
    (p n) hn

/-- Every smooth Riemannian three-manifold, with the extended length distance of its own metric
and the Borel structure, satisfies the two-sided comparison with constant `64` on all sets. -/
theorem lengthMetric_normalizedHausdorffMeasure_comparison_sixtyFour
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (s : Set M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    normalizedHausdorffMeasure 3 s ≤
        64 * DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ∧
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ≤
        64 * normalizedHausdorffMeasure 3 s := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  have _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have hEnorm : IsMetricNorm (I := I) (M := M) g := isMetricNorm_of_riemannianBundle (I := I) g
  exact ⟨normalizedHausdorffMeasure_le_sixtyFour_riemannianVolumeMeasure' g hEnorm hdim s,
    riemannianVolumeMeasure_le_sixtyFour_normalizedHausdorffMeasure' g hEnorm hdim s⟩

private instance roundThreeSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- The round unit three-sphere with its length distance: the comparison with constant `64`. -/
theorem roundThreeSphere_normalizedHausdorffMeasure_comparison_sixtyFour
    (s : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    letI : RiemannianBundle
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦ TangentSpace (𝓡 3) x) :=
      ⟨(roundMetric (n := 3)).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦ TangentSpace (𝓡 3) x) :=
      ⟨(roundMetric (n := 3)).inner, (roundMetric (n := 3)).contMDiff.continuous,
        fun _ _ _ => rfl⟩
    letI : EMetricSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    letI : MeasurableSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
      borel (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    haveI : BorelSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := ⟨rfl⟩
    normalizedHausdorffMeasure 3 s ≤
        64 * DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (roundMetric (n := 3)) s ∧
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (roundMetric (n := 3)) s ≤
        64 * normalizedHausdorffMeasure 3 s :=
  lengthMetric_normalizedHausdorffMeasure_comparison_sixtyFour (roundMetric (n := 3))
    (by simp) s

/-- X67's first volume scale in normalized Hausdorff measure: on a closed boundaryless Riemannian
three-manifold with the length distance of `g`, the `g`-ball of radius `firstVolumeScale g p w`
has normalized `ℋ³` equal to `w` times the cube of the radius. -/
theorem lengthMetric_normalizedHausdorffMeasure_firstVolumeScale
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric J M) (hdim : Module.finrank ℝ F = 3) (p : M) {w : ℝ}
    (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace J x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace J x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric J M
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    normalizedHausdorffMeasure 3
        (riemannianBallOf g p (DifferentialGeometry.Geometry.Collapse.firstVolumeScale g p w)) =
      ENNReal.ofReal (w * DifferentialGeometry.Geometry.Collapse.firstVolumeScale g p w ^ 3) := by
  rw [lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure g hdim]
  exact DifferentialGeometry.Geometry.Collapse.ballVolume_firstVolumeScale g hdim p hw hwc

end DifferentialGeometry.Geometry.Metric
