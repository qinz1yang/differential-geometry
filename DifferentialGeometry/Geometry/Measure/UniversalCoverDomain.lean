import DifferentialGeometry.Geometry.Measure.LocalIsometrySection
import DifferentialGeometry.Geometry.Measure.UniversalCover

noncomputable section

open scoped Manifold ContDiff
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

theorem exists_fundamental_domain_volume_eq (g : SmoothRiemannianMetric I M) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    ∃ D : Set (UniversalCover M), MeasurableSet D ∧
      (∀ x : UniversalCover M, ∃! a : FundamentalGroup M (default : M), a • x ∈ D) ∧
      MeasureTheory.IsFundamentalDomain (FundamentalGroup M (default : M)) D
        (riemannianVolumeMeasure I (UniversalCover M) (liftedMetric (I := I) g)) ∧
      riemannianVolumeMeasure I (UniversalCover M) (liftedMetric (I := I) g) D =
        riemannianVolumeMeasure I M g Set.univ := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have honto : Function.Surjective (proj : UniversalCover M → M) := by
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro y
    exact ⟨⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath default y)⟩, rfl⟩
  have hmetric (x : UniversalCover M) (v w : TangentSpace I x) :
      (liftedMetric (I := I) g).inner x v w =
        g.inner (proj x) (mfderiv I I proj x v) (mfderiv I I proj x w) := by
    rw [(hasMFDerivAt_proj (I := I) x).mfderiv]
    rfl
  exact Geometry.Measure.exists_fundamental_domain_volume_eq_of_surjective_local_isometry
    (liftedMetric (I := I) g) g proj proj_localDiffeo honto hmetric proj_eq_iff_smul
    (fun a ha x hx => ha ((deckAct_eq_self_iff x).mp hx))

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
