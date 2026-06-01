import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of the Riemannian extended distance from a fixed base point

For a smooth Riemannian metric `g` on a smooth manifold `M` and a fixed
base point `p : M`, the map `q ↦ riemannianEDist I p q` is continuous for
the manifold topology on `M`.

The proof installs, from the metric data `g`, the auxiliary fibre instances
`Bundle.RiemannianBundle (TangentSpace I)` (from `g.toRiemannianMetric`)
and `IsContinuousRiemannianBundle E (TangentSpace I)` (from the
smooth-implies-continuous inner product of `g`), then builds Mathlib's
`PseudoEMetricSpace.ofRiemannianMetric I M`. By construction (via
`PseudoEMetricSpace.ofEDistOfTopology`) this pseudo-emetric structure has

* `edist = riemannianEDist I` (definitionally), and
* a topology *definitionally equal* to the ambient manifold topology
  (`UniformSpace.ofFunOfHasBasis` sets `toTopologicalSpace := t`).

Continuity of the extended distance (`Continuous.edist`) for this
pseudo-emetric structure therefore yields continuity of
`q ↦ riemannianEDist I p q` for the manifold topology directly.

The regularity hypothesis `[RegularSpace M]` required by
`PseudoEMetricSpace.ofRiemannianMetric` is discharged from the manifold
structure: a finite-dimensional manifold is locally compact
(`Manifold.locallyCompact_of_finiteDimensional`), and a weakly locally
compact `R1` (here Hausdorff) space is regular.

This is the prerequisite continuity input for the open/closed clopen
decomposition in radial-geodesic surjectivity arguments.
-/

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- **Continuity of the Riemannian extended distance from a fixed base point.**

For a smooth Riemannian metric `g` and a fixed `p : M`, the map
`q ↦ riemannianEDist I p q` is continuous for the manifold topology on `M`.

The auxiliary fibre instances `RiemannianBundle (TangentSpace I)` and
`IsContinuousRiemannianBundle E (TangentSpace I)` are installed from `g`
inside the proof, exactly as Mathlib's `riemannianEDist` API expects; the
statement itself uses only the manifold topology and the metric data `g`.

Mathlib's `PseudoEMetricSpace.ofRiemannianMetric I M` provides a pseudo
extended metric whose `edist` is `riemannianEDist I` and whose topology is
definitionally the ambient one; continuity of `edist` (`Continuous.edist`)
then transfers to `riemannianEDist`.

The regularity hypothesis of `ofRiemannianMetric` is discharged locally
from finite-dimensionality (local compactness) together with the
Hausdorff hypothesis. -/
theorem continuous_riemannianEDist
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    Continuous (fun q : M ↦ riemannianEDist I p q) := by
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_const.edist continuous_id)

/-- **Continuity on the finite locus of the real Riemannian distance from a fixed
base point.**

There is no separate `riemannianDist` definition in Mathlib; the real-valued
Riemannian distance is `(riemannianEDist I p ·).toReal`. Since `ENNReal.toReal`
is discontinuous at `∞` (and `riemannianEDist I p q = ∞` is possible when no
`C¹` path joins `p` to `q`), the real distance is *not* globally continuous on a
non-complete manifold. It is, however, continuous on the locus where the
extended distance is finite, which is what the corollary records: on
`{q | riemannianEDist I p q ≠ ∞}` the map `q ↦ (riemannianEDist I p q).toReal`
is continuous. -/
theorem continuousOn_riemannianEDist_toReal_on_finite
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    ContinuousOn (fun q : M ↦ (riemannianEDist I p q).toReal)
      {q : M | riemannianEDist I p q ≠ (∞ : ℝ≥0∞)} := by
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  refine ENNReal.continuousOn_toReal.comp'
    (continuous_riemannianEDist g p).continuousOn (fun q hq ↦ ?_)
  exact hq

end Riemannian
end Geometry
end DifferentialGeometry

end
