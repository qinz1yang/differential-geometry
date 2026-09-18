import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckHighCurvature

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_spatialNeck_scalar_upper_bound :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧
      ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g →
        DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g →
        ∃ C : ℝ, ∀ (p : M) (eta : ℝ), eta ≤ eta₀ →
          SpatialNeck g eta p → metricScalarAt g p ≤ C := by
  obtain ⟨eta₀, heta₀, hconvert⟩ := exists_spatialNeckWitness_of_spatialNeck
    spatialNeckControlEpsilon_pos
  refine ⟨eta₀, heta₀, ?_⟩
  intro M _ _ _ _ _ _ g hg hsec
  classical
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : MetricSpace M := riemMetricSpace (I := I3) (M := M)
  have hEnorm : IsMetricNorm (I := I3) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I3) g x v
  by_contra hbound
  have hlarge (n : ℕ) : ∃ (p : M) (eta : ℝ) (heta : eta ≤ eta₀)
      (nk : SpatialNeck g eta p), (n : ℝ) < metricScalarAt g p := by
    push Not at hbound
    obtain ⟨p, eta, heta, nk, hn⟩ := hbound n
    exact ⟨p, eta, heta, nk, hn⟩
  choose p eta heta nk hn using hlarge
  choose W _hW using fun n : ℕ => hconvert M g hg (p n) (eta n) (heta n) (nk n)
  have hdiverges : Tendsto (fun n => metricScalarAt g (p n)) atTop atTop :=
    tendsto_atTop_mono (fun n => (hn n).le) (tendsto_natCast_atTop_atTop (R := ℝ))
  exact not_tendsto_scalar_spatialNeck_centers_of_nonnegative W hEnorm le_rfl hsec hdiverges

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
