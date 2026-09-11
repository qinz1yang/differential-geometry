import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornInteriorMinimizers

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_exists_local_complete_metric
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ p : W,
      dist (p : UniformSpace.Completion W) H.endpoint < d →
      ∃ (g' : SmoothRiemannianMetric I3 W) (r : ℝ) (U : Set W),
        0 < r ∧ RiemannianMetricComplete g' ∧ IsOpen U ∧
        Metric.closedBall p (4 * r) ⊆ U ∧
        (∀ z ∈ U, g'.inner z = g.inner z) ∧
        (∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v) ∧
        ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
          riemannianEDistOf g' x y = ENNReal.ofReal (dist x y) := by
  obtain ⟨d, hd, hcompact⟩ := finiteHorn_isCompact_subradial_closedBall g H
  refine ⟨d, hd, ?_⟩
  intro p hp
  let R : ℝ := dist (p : UniformSpace.Completion W) H.endpoint / 2
  have hrad : 0 < dist (p : UniformSpace.Completion W) H.endpoint :=
    dist_pos.mpr (H.endpoint_missing p)
  have hR : 0 < R := half_pos hrad
  have hRlt : R < dist (p : UniformSpace.Completion W) H.endpoint := half_lt_self hrad
  obtain ⟨g', U, hcomplete, hU, hKU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g (hcompact p hp R hRlt)
  refine ⟨g', R / 4, U, by positivity, hcomplete, hU, ?_, heq, hle, ?_⟩
  · simpa only [show 4 * (R / 4) = R by ring] using hKU
  · intro x hx y hy
    have hxp : dist x p < R / 4 := hx
    have hyp : dist y p < R / 4 := hy
    have hxy : dist x y < R / 2 := by
      have htri := dist_triangle x p y
      rw [dist_comm p y] at htri
      linarith
    have hball : {z : W | riemannianEDistOf g x z ≤ ENNReal.ofReal (R / 2)} ⊆ U := by
      intro z hz
      apply hKU
      change dist z p ≤ R
      change riemannianEDistOf g x z ≤ ENNReal.ofReal (R / 2) at hz
      rw [H.edist_eq_ofReal_dist] at hz
      have hxz : dist x z ≤ R / 2 :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hz
      have htri := dist_triangle z x p
      rw [dist_comm z x] at htri
      linarith
    have hyshort : riemannianEDistOf g x y < ENNReal.ofReal (R / 2) := by
      rw [H.edist_eq_ofReal_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hxy
    exact (riemannianEDistOf_eq_of_eqOn_ball g g' hball heq hle hyshort).trans
      (edist_eq_ofReal_dist g H x y)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
