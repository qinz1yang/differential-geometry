import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

/-!
# CH12-S64, group 2a: sharp radial placement for the K-cap ball-in-window step

`norm_le_add_of_quad_edist_S64`: if `StandardCap.metric ≤ c · g` (quadratic forms on all of `ℝ³`) and
`d_g(z, y) ≤ a`, then `‖y‖ ≤ ‖z‖ + √c · a`.  This is the SHARP version (no `Λ (L+1)` slack) of the
private `norm_le_of_edist_le` of `StandardWindowBallPlacement.lean`: the radial coordinate is
1-Lipschitz for the standard cap metric (`StandardCap.radial_difference_le_edist`), so with
`c = 4`, `a < 2A` one gets `‖y‖ < ‖z‖ + 4A` — exactly the `4 A` of the K-cap radius budget
`32 (Dcap + 1 + 4 A) + 2` of `[FROZEN v2] CH12-S48`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

theorem norm_le_add_of_quad_edist_S64
    (g : SmoothRiemannianMetric I3 (EuclideanSpace ℝ (Fin 3))) {c : ℝ} (hc : 0 < c)
    (hu : ∀ (x : EuclideanSpace ℝ (Fin 3)) (v : TangentSpace I3 x),
      StandardCap.metric.inner x v v ≤ c * g.inner x v v)
    {z y : EuclideanSpace ℝ (Fin 3)} {a : ℝ} (ha : 0 ≤ a)
    (hzy : riemannianEDistOf (I := I3) g z y ≤ ENNReal.ofReal a) :
    ‖y‖ ≤ ‖z‖ + Real.sqrt c * a := by
  have hcap := edistOf_le_of_quad (I := I3) g StandardCap.metric hc hu z y
  have hrad := StandardCap.radial_difference_le_edist z y
  have hmul : riemannianEDistOf (I := I3) StandardCap.metric z y ≤
      ENNReal.ofReal (Real.sqrt c * a) := by
    refine hcap.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl hzy
  have h := hrad.trans hmul
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have := (le_abs_self (‖y‖ - ‖z‖)).trans h
  linarith only [this]

end GC.LongTime.Ch12
