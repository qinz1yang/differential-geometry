import DifferentialGeometry.Geometry.Measure.CoveringBall
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckIsometryGlobal
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph

open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem riemannianEDistOf_deck (g : SmoothRiemannianMetric I M)
    (γ : FundamentalGroup M (default : M)) (x y : UniversalCover M) :
    riemannianEDistOf (liftedMetric (I := I) g) (γ • x) (γ • y) =
      riemannianEDistOf (liftedMetric (I := I) g) x y := by
  have h := universalCover_deck_isometry_of_liftedMetric (I := I) g γ
  exact h x y

theorem riemannianVolumeMeasure_ball_eq_of_le_deck_displacement
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M) (r : ℝ)
    (hx : ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
      ENNReal.ofReal (2 * r) ≤ riemannianEDistOf (liftedMetric (I := I) g) x (γ • x)) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    riemannianVolumeMeasure I (UniversalCover M) (liftedMetric (I := I) g)
        (riemannianBallOf (liftedMetric (I := I) g) x r) =
      riemannianVolumeMeasure I M g (riemannianBallOf g (proj x) r) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let ĝ := liftedMetric (I := I) g
  have hinj : Set.InjOn (proj : UniversalCover M → M) (riemannianBallOf ĝ x r) := by
    intro y hy z hz heq
    obtain ⟨γ, hγ⟩ := (proj_eq_iff_smul z y).mp heq.symm
    by_cases h1 : γ = 1
    · simpa only [h1, one_smul] using hγ.symm
    · have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hy)
      have hdist : riemannianEDistOf ĝ x (γ • x) < ENNReal.ofReal (2 * r) := calc
        _ ≤ riemannianEDistOf ĝ x y + riemannianEDistOf ĝ y (γ • x) :=
          riemannianEDistOf_triangle ĝ x y (γ • x)
        _ = riemannianEDistOf ĝ x y + riemannianEDistOf ĝ x z := by
          rw [← hγ, riemannianEDistOf_deck, riemannianEDistOf_comm ĝ z x]
        _ < ENNReal.ofReal r + ENNReal.ofReal r := ENNReal.add_lt_add hy hz
        _ = ENNReal.ofReal (2 * r) := by rw [two_mul, ENNReal.ofReal_add hr.le hr.le]
      exact (not_lt_of_ge (hx γ h1) hdist).elim
  have hp : IsLocalDiffeomorph I I ∞ (proj : UniversalCover M → M) := proj_localDiffeo
  have hpull : localPullMetric g proj hp = ĝ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, (hasMFDerivAt_proj (I := I) y).mfderiv]
    rfl
  exact DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_injOn_coveringMap
    ĝ g hp proj_isCoveringMap hpull x r hinj

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
