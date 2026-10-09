import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence

set_option autoImplicit false

namespace GC.MetricGeometry.PointedBallApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R ε : ℝ}

noncomputable def extendToWholeSpace (f : PointedBallApprox p q R ε) (x : X) : Y :=
  if hx : dist x p ≤ R then f.toFun ⟨x, hx⟩ else q

theorem extendToWholeSpace_apply (f : PointedBallApprox p q R ε)
    (x : X) (hx : dist x p ≤ R) :
    f.extendToWholeSpace x = f.toFun ⟨x, hx⟩ := by
  classical
  simp only [extendToWholeSpace, dite_eq_left hx]

end GC.MetricGeometry.PointedBallApprox

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology

universe u v
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
variable {Y : Type v} [MetricSpace Y] {p c : ∀ i, X i} {q y : Y}
variable {R ε : ℕ → ℝ} {C d : ℝ}

theorem eventually_marked_point_radial_error
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hc : ∀ i, dist (c i) (p i) ≤ C) :
    ∀ᶠ i in atTop,
      |dist ((f i).extendToWholeSpace (c i)) q - dist (c i) (p i)| < ε i := by
  filter_upwards [hR.eventually (eventually_ge_atTop C)] with i hi
  rw [(f i).extendToWholeSpace_apply (c i) ((hc i).trans hi)]
  exact (f i).radial_error _

theorem marked_point_limit_dist
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hc : ∀ i, dist (c i) (p i) ≤ C)
    (hy : Tendsto (fun i => (f i).extendToWholeSpace (c i)) atTop (𝓝 y))
    (hd : Tendsto (fun i => dist (c i) (p i)) atTop (𝓝 d)) : dist y q = d := by
  have he := eventually_marked_point_radial_error f hR hc
  have hz : Tendsto (fun i => dist (dist ((f i).extendToWholeSpace (c i)) q)
      (dist (c i) (p i))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hε
    exact he.mono (fun i hi => by simpa only [Real.dist_eq] using hi.le)
  have hh := (hy.dist tendsto_const_nhds).congr_dist hz
  exact tendsto_nhds_unique hh hd

end GC.MetricGeometry
