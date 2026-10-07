import DifferentialGeometry.Geometry.Measure.CoveringCollapse
import DifferentialGeometry.Geometry.Measure.UniversalCover
import DifferentialGeometry.Geometry.Measure.Isometry

noncomputable section

open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (UniversalCover M) := borel (UniversalCover M)
private local instance : BorelSpace (UniversalCover M) := ⟨rfl⟩

theorem nat_mul_volume_ball_le_of_short_deck_displacement
    (g : SmoothRiemannianMetric I M) (γ : FundamentalGroup M (default : M))
    (hγ : ¬ IsOfFinOrder γ) (x : UniversalCover M)
    (R δ : ℝ) (hR : 0 < R) (hδ : 0 ≤ δ)
    (hshort : riemannianEDistOf (liftedMetric (I := I) g) x (γ • x) ≤ ENNReal.ofReal δ)
    (N : ℕ) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    (N : ℝ≥0∞) * riemannianVolumeMeasure I M g (riemannianBallOf g (proj x) R) ≤
      riemannianVolumeMeasure I (UniversalCover M) (liftedMetric (I := I) g)
        (riemannianBallOf (liftedMetric (I := I) g) x (R + ((N - 1 : ℕ) : ℝ) * δ)) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let ĝ := liftedMetric (I := I) g
  let _ : ContinuousConstSMul (FundamentalGroup M (default : M)) (UniversalCover M) :=
    ⟨fun a => (deckDiffeo (I := I) a).continuous⟩
  have hiso (a : FundamentalGroup M (default : M)) (y z : UniversalCover M) :
      riemannianEDistOf ĝ (a • y) (a • z) = riemannianEDistOf ĝ y z :=
    universalCover_deck_isometry_of_liftedMetric (I := I) g a y z
  have hvol (a : FundamentalGroup M (default : M)) :
      MeasureTheory.MeasurePreserving (fun y : UniversalCover M => a • y)
        (riemannianVolumeMeasure I (UniversalCover M) ĝ)
        (riemannianVolumeMeasure I (UniversalCover M) ĝ) :=
    Geometry.Measure.measurePreserving_diffeomorph_of_riemannian_distance_eq
      ĝ ĝ (deckDiffeo (I := I) a) (hiso a)
  have hp : IsLocalDiffeomorph I I ∞ (proj : UniversalCover M → M) := proj_localDiffeo
  have hpull : localPullMetric g proj hp = ĝ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, (hasMFDerivAt_proj (I := I) y).mfderiv]
    rfl
  exact Geometry.Measure.nat_mul_volume_ball_le_of_short_deck_displacement
    ĝ g hp proj_isCoveringMap hpull
    (fun a y => ((proj_eq_iff_smul y (a • y)).mpr ⟨a, rfl⟩).symm)
    (fun a ha y he => ha ((deckAct_eq_self_iff y).mp he))
    hiso hvol γ hγ x R δ hR hδ hshort N

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
