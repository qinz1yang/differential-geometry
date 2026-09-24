import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Metric.Distance.Ball

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianClosedBallOf_subset_of_add_radius_le
    (g : SmoothRiemannianMetric I M) {p x : M} {r ρ R : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hR : r + ρ ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p r) :
    riemannianClosedBallOf g x ρ ⊆ riemannianClosedBallOf g p R := by
  intro y hy
  change riemannianEDistOf g p y ≤ ENNReal.ofReal R
  calc
    _ ≤ riemannianEDistOf g p x + riemannianEDistOf g x y :=
      riemannianEDistOf_triangle g p x y
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal ρ := add_le_add hx hy
    _ = ENNReal.ofReal (r + ρ) := (ENNReal.ofReal_add hr hρ).symm
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hR

theorem riemannianBallOf_eq_of_eqOn_outer_closedBall
    (g g' : SmoothRiemannianMetric I M) {p x : M} {r ρ R : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hR : r + ρ ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p r)
    (heq : ∀ z ∈ riemannianClosedBallOf g p R, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) :
    riemannianBallOf g' x ρ = riemannianBallOf g x ρ := by
  have hbuffer := riemannianClosedBallOf_subset_of_add_radius_le g hr hρ hR hx
  ext y
  constructor
  · intro hy
    exact (edistOf_mono g g' hle x y).trans_lt hy
  · intro hy
    have hd := riemannianEDistOf_eq_of_eqOn_ball g g' hbuffer heq hle hy
    change riemannianEDistOf g' x y < ENNReal.ofReal ρ
    rwa [hd]

end DifferentialGeometry
