import DifferentialGeometry.Geometry.Hyperbolic.UniversalCover
import DifferentialGeometry.Geometry.Measure.HyperbolicComparison
import DifferentialGeometry.Geometry.Measure.UniversalCover

open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open Riemannian.Exponential (hyperbolicComparison hyperbolicComparisonIsometryEquiv
  hyperbolicComparisonIsometryEquiv_apply hyperbolicComparisonIsometryEquiv_origin
  riemannianVolumeMeasure_ball_hyperbolicComparison)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianVolumeMeasure_normalized_ball_eq_of_le_deck_displacement
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (p : M) (X Y : TangentSpace I p),
      Curvature.metricRm04StandardAt g p X Y Y X =
        κ * (g.inner p X X * g.inner p Y Y - g.inner p X Y * g.inner p X Y)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    ∀ (x : UniversalCover M) (r : ℝ),
      (∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
        ENNReal.ofReal (2 * r) ≤ riemannianEDistOf ĝ x (γ • x)) →
      riemannianVolumeMeasure I M gN (riemannianBallOf gN (UniversalCover.proj x) r) =
        riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
          (Metric.ball Hyperboloid.origin r) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  have hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  dsimp only
  intro x r hx
  have hdeck := UniversalCover.riemannianVolumeMeasure_ball_eq_of_le_deck_displacement gN x r hx
  have hR := normalized_lifted_riemannOp g κ hκ hsec
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let i : E₃ ≃ₗᵢ[ℝ] TangentSpace I x := (stdOrthonormalBasis ℝ E₃).equiv
    (stdOrthonormalBasis ℝ (TangentSpace I x)) (finCongr rfl)
  have horigin : hyperbolicComparison ĝ hĝ x i Hyperboloid.origin = x := by
    rw [← hyperbolicComparisonIsometryEquiv_apply ĝ hĝ x hR i,
      hyperbolicComparisonIsometryEquiv_origin]
  have hvolume := riemannianVolumeMeasure_ball_hyperbolicComparison
    ĝ hĝ x hR i Hyperboloid.origin r
  rw [horigin] at hvolume
  exact hdeck.symm.trans hvolume

end DifferentialGeometry.Geometry.Hyperbolic
