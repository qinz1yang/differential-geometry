import DifferentialGeometry.Geometry.Exponential.HyperbolicSpaceForm
import DifferentialGeometry.Geometry.Measure.LocalIsometry

open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [SimplyConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (Hyperboloid E) := borel (Hyperboloid E)
private local instance : BorelSpace (Hyperboloid E) := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianVolumeMeasure_ball_hyperbolicComparison
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hR : ∀ (q : M) (X Y Z : TangentSpace I q),
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p) (x : Hyperboloid E) (r : ℝ),
      riemannianVolumeMeasure I M g (riemannianBallOf g (hyperbolicComparison g hg p i x) r) =
        riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) Hyperboloid.riemannianMetric
          (Metric.ball x r) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  intro i x r
  let F := hyperbolicComparison g hg p i
  let e := hyperbolicComparisonIsometryEquiv g hg p hR i
  have he (z : Hyperboloid E) : e z = F z :=
    hyperbolicComparisonIsometryEquiv_apply g hg p hR i z
  have hF : Function.Injective F := by
    intro z w hzw
    apply e.injective
    simpa only [he] using hzw
  have hvolume := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (S := Metric.ball x r) Hyperboloid.riemannianMetric g F
    (isLocalDiffeomorph_hyperbolicComparison g hg p hR i) hF
    (fun z u v => (hyperbolicComparison_inner g hg p hR i z u v).symm)
    Metric.isOpen_ball.measurableSet
  have hdist (z w : Hyperboloid E) : riemannianEDistOf g (F z) (F w) = edist z w := by
    change edist (F z) (F w) = edist z w
    rw [← he, ← he, e.edist_eq]
  have himage : F '' Metric.ball x r = riemannianBallOf g (F x) r := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      change riemannianEDistOf g (F x) (F z) < ENNReal.ofReal r
      rw [hdist, edist_lt_ofReal]
      exact Metric.mem_ball'.mp hz
    · intro y hy
      obtain ⟨z, hz⟩ := e.surjective y
      have hz' : F z = y := (he z).symm.trans hz
      refine ⟨z, ?_, hz'⟩
      change riemannianEDistOf g (F x) y < ENNReal.ofReal r at hy
      rw [← hz', hdist, edist_lt_ofReal] at hy
      exact Metric.mem_ball'.mpr hy
  rw [himage] at hvolume
  exact hvolume.symm

end DifferentialGeometry.Geometry.Riemannian.Exponential
