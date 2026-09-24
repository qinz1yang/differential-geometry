import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteTriangleEquality
import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Curvature.Nonnegative

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem comparisonAngle_le_of_equal_radius_minimizing_lenses
    (g : SmoothRiemannianMetric I3 M) (hcomplete : RiemannianMetricComplete g)
    (hsec : HasNonnegativeSectionalCurvature g) (y p z q w : M) {r : ℝ}
    (hr : 0 < r) (hrp : r < metricDistance g y p) (hrz : r < metricDistance g y z)
    (hq : metricDistance g y q = r) (hw : metricDistance g y w = r)
    (hqp : metricDistance g q p = metricDistance g y p - r)
    (hwz : metricDistance g w z = metricDistance g y z - r) :
    comparisonAngle (metricDistance g y p) (metricDistance g y z) (metricDistance g p z) ≤
      comparisonAngle r r (metricDistance g q w) := by
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I3) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hd (a b : M) : (riemannianEDist I3 a b).toReal = metricDistance g a b := by
    rw [metricDistance, riemannianEDistOf_eq_riemannianEDist g hEnorm]
  obtain ⟨u, hu, huq⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm y q
    (by rw [hd, hq]; exact hr)
  rw [hd, hq] at huq
  obtain ⟨v, hv, hvw⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm y w
    (by rw [hd, hw]; exact hr)
  rw [hd, hw] at hvw
  have hup : intrinsicGeodesic g hEnorm y u (metricDistance g y p) = p := by
    have hh := intrinsicGeodesic_continues_of_distance_add g hEnorm y p u hu hr
      (sub_pos.mpr hrp) (by
        rw [add_sub_cancel, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) y p)])
      (by
        rw [huq, ← hqp, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) q p)])
    simpa only [add_sub_cancel] using hh
  have hvz : intrinsicGeodesic g hEnorm y v (metricDistance g y z) = z := by
    have hh := intrinsicGeodesic_continues_of_distance_add g hEnorm y z v hv hr
      (sub_pos.mpr hrz) (by
        rw [add_sub_cancel, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) y z)])
      (by
        rw [hvw, ← hwz, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) w z)])
    simpa only [add_sub_cancel] using hh
  have hh := complete_comparisonAngle_shortening g hEnorm hsec y u v
    r (metricDistance g y p) r (metricDistance g y z) hr hrp.le hr hrz.le hu hv
    (by rw [hup, hd]) (by rw [hvz, hd])
  simpa only [hup, hvz, huq, hvw, hd] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
