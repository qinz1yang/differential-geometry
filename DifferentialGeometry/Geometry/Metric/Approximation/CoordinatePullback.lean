import DifferentialGeometry.Topology.UniformConvergence.ApproximateInverse
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

namespace GC.MetricGeometry

open Filter Set
open scoped Topology

theorem tendstoUniformlyOn_coordinate_pullback
    {ι : Type*} {X : ι → Type*} {Y E : Type*}
    [∀ i, MetricSpace (X i)] [MetricSpace Y] [PseudoMetricSpace E]
    {l : Filter ι} {p : ∀ i, X i} {q : Y} {R ε : ι → ℝ}
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hε : Tendsto ε l (𝓝 0))
    {K : Set Y} (hK : Bornology.IsBounded K)
    {j : ∀ i, Y → X i} {u : ∀ i, X i → E} {t : Y → E}
    (hdom : ∀ᶠ i in l, ∀ x ∈ K, dist (j i x) (p i) ≤ R i)
    (hround : TendstoUniformlyOn
      (fun i x => (f i).extendToWholeSpace (j i x)) id l K)
    (ht : UniformContinuous t)
    (hclose : ∀ S η : ℝ, 0 < η → ∀ᶠ i in l,
      ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        dist (u i x.val) (t ((f i).toFun x)) ≤ η) :
    TendstoUniformlyOn (fun i x => u i (j i x)) t l K := by
  obtain ⟨C, hC⟩ := hK.subset_closedBall q
  have hbound : ∀ᶠ i in l, ∀ x ∈ K, dist (j i x) (p i) ≤ C + 2 := by
    filter_upwards [hdom, hε.eventually (eventually_lt_nhds zero_lt_one),
      Metric.tendstoUniformlyOn_iff.mp hround 1 zero_lt_one] with i hdi hei hri x hx
    have hxdom := hdi x hx
    have hr := (f i).radial_lower ⟨j i x, hxdom⟩
    have happrox := hri x hx
    change dist x ((f i).extendToWholeSpace (j i x)) < 1 at happrox
    rw [(f i).extendToWholeSpace_apply (j i x) hxdom] at happrox
    have hrad : dist x q ≤ C := hC hx
    have htriangle := dist_triangle ((f i).toFun ⟨j i x, hxdom⟩) x q
    rw [dist_comm ((f i).toFun ⟨j i x, hxdom⟩) x] at htriangle
    change dist (j i x) (p i) < dist ((f i).toFun ⟨j i x, hxdom⟩) q + ε i at hr
    linarith
  apply hround.comp_of_approximate_inverse ht
    (S := fun i => {x : X i | dist x (p i) ≤ R i ∧ dist x (p i) ≤ C + 2})
  · filter_upwards [hdom, hbound] with i hdi hbi x hx
    exact ⟨hdi x hx, hbi x hx⟩
  · intro η hη
    filter_upwards [hclose (C + 2) η hη] with i hi x hx
    rw [(f i).extendToWholeSpace_apply x hx.1]
    exact hi ⟨x, hx.1⟩ hx.2

end GC.MetricGeometry
