import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Topology.MetricSpace.Lipschitz

noncomputable section

open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

private theorem locallyLipschitz_of_riemannian_ball_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    {a b : ℝ} (ell : M × Icc a b → ℝ)
    (hell : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf g p R,
      ∀ y ∈ riemannianClosedBallOf g p R,
      ∀ s t : Icc a b, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|)) :
    let : PseudoMetricSpace M := g.toPseudoMetricSpace
    LocallyLipschitz ell := by
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  change LocallyLipschitz ell
  by_cases hab : a ≤ b
  · apply locallyLipschitz_of_lipschitzOn_closedBall (p, ⟨a, le_rfl, hab⟩)
    intro R hR
    obtain ⟨K, hK⟩ := hell R hR
    refine ⟨2 * K, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hxB : x.1 ∈ riemannianClosedBallOf g p R := by
      change edist p x.1 ≤ ENNReal.ofReal R
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
      exact (le_max_left _ _).trans (Metric.mem_closedBall.mp hx)
    have hyB : y.1 ∈ riemannianClosedBallOf g p R := by
      change edist p y.1 ≤ ENNReal.ofReal R
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
      exact (le_max_left _ _).trans (Metric.mem_closedBall.mp hy)
    have h := hK x.1 hxB y.1 hyB x.2 y.2
    change |ell x - ell y| ≤ (K : ℝ) * (dist x.1 y.1 + dist x.2 y.2) at h
    change |ell x - ell y| ≤ ((2 * K : ℝ≥0) : ℝ) * dist x y
    rw [NNReal.coe_mul, NNReal.coe_ofNat, Prod.dist_eq]
    have hd : dist x.1 y.1 + dist x.2 y.2 ≤ 2 * max (dist x.1 y.1) (dist x.2 y.2) := by
      linarith only [le_max_left (dist x.1 y.1) (dist x.2 y.2),
        le_max_right (dist x.1 y.1) (dist x.2 y.2)]
    nlinarith only [h, mul_le_mul_of_nonneg_left hd K.coe_nonneg]
  · rintro ⟨x, t⟩
    exact (hab (t.2.1.trans t.2.2)).elim

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    {a b : ℝ} (hab : a ≤ b) (ell : M × Icc a b → ℝ)
    (hell : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf g p R,
      ∀ y ∈ riemannianClosedBallOf g p R,
      ∀ s t : Icc a b, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|)) (α : M) :
    LocallyLipschitzOn (univ ×ˢ (extChartAt I α).target)
      (fun p : ℝ × E => ell ((extChartAt I α).symm p.2, projIcc a b hab p.1)) := by
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have he := locallyLipschitz_of_riemannian_ball_bounds g p ell hell
  have hs : LocallyLipschitzOn (univ ×ˢ (extChartAt I α).target)
      (fun p : ℝ × E => (extChartAt I α).symm p.2) :=
    (locallyLipschitzOn_extChartAt_symm α).comp
      LipschitzWith.prod_snd.locallyLipschitz.locallyLipschitzOn (fun _ hp => hp.2)
  have ht : LocallyLipschitzOn (univ ×ˢ (extChartAt I α).target)
      (fun p : ℝ × E => projIcc a b hab p.1) :=
    ((LipschitzWith.projIcc hab).comp LipschitzWith.prod_fst).locallyLipschitz.locallyLipschitzOn
  exact he.locallyLipschitzOn.comp (hs.prodMk ht) (mapsTo_univ _ _)

end DifferentialGeometry.Geometry.Riemannian
