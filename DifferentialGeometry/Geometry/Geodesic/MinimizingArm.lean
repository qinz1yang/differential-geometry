import DifferentialGeometry.Geometry.Geodesic.Ray
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseGeometry

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_minimizingArm_of_complete
    (g : SmoothRiemannianMetric I3 M) (hcomplete : RiemannianMetricComplete g)
    (x y : M) (hxy : x ≠ y) :
    ∃ a : MinimizingArm g x, a.length = metricDistance g x y ∧ a.point a.length = y := by
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := riemMetricSpace (I := I3) (M := M)
  have hEnorm : IsMetricNorm (I := I3) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hd (p q : M) : metricDistance g p q = dist p q := by
    rw [metricDistance, riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← riemMetric_dist_eq (I := I3)]
  obtain ⟨γ, hγ, hstart, hend, _, _⟩ :=
    exists_unitSpeed_minimizing_riemannian_geodesic g hEnorm x y hxy
  refine ⟨{ length := dist x y
            length_pos := dist_pos.mpr hxy
            point := γ
            start := hstart
            minimizing := ?_ }, (hd x y).symm, hend⟩
  intro s hs t ht
  rw [hd]
  exact (hγ.dist_eq ⟨s, hs⟩ ⟨t, ht⟩).trans (by rfl)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
