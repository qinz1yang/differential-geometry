import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryLaunchContinuation

/-!
The actual positive launch and native maximal-flow domain has a constructed exit supremum.
It is open and downward closed, and its membership is exactly below that exit time.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N]

def boundaryFlowExitDomain (g : SmoothRiemannianMetric I N) (seed : TangentBundle I N)
    (a : ℝ) : Set ℝ :=
  {t | 0 < t ∧ (t < a ∨ (seed, t - a) ∈ g.geodesicFlowDomain)}

noncomputable def boundaryFlowExitTime (g : SmoothRiemannianMetric I N)
    (seed : TangentBundle I N) (a : ℝ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' boundaryFlowExitDomain g seed a)

theorem boundaryFlowExitDomain_down (g : SmoothRiemannianMetric I N)
    (seed : TangentBundle I N) (a : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t ∈ boundaryFlowExitDomain g seed a) : s ∈ boundaryFlowExitDomain g seed a := by
  rcases ht with ⟨htpos, hbefore | hflow⟩
  · exact ⟨hs, Or.inl (hst.trans_lt hbefore)⟩
  · refine ⟨hs, ?_⟩
    by_cases hsa : s < a
    · exact Or.inl hsa
    · apply Or.inr
      change s - a ∈ maximalIntegralCurveInterval g.geodesicSpray seed
      have hzero : (0 : ℝ) ∈ maximalIntegralCurveInterval g.geodesicSpray seed :=
        g.mem_geodesicFlowDomain_zero (r := ⊤) le_top seed
      have htflow : t - a ∈ maximalIntegralCurveInterval g.geodesicSpray seed := hflow
      exact ordConnected_maximalIntegralCurveInterval.out hzero htflow
        ⟨by linarith [le_of_not_gt hsa], by linarith⟩

variable [interiorT2 : T2Space N]

theorem boundaryFlowExitDomain_isOpen (g : SmoothRiemannianMetric I N)
    (seed : TangentBundle I N) (a : ℝ) : IsOpen (boundaryFlowExitDomain g seed a) := by
  change IsOpen (Ioi (0 : ℝ) ∩ (Iio a ∪
    (fun t : ℝ => (seed, t - a)) ⁻¹' g.geodesicFlowDomain))
  exact isOpen_Ioi.inter (isOpen_Iio.union
    ((g.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage
      (continuous_const.prodMk (continuous_id.sub continuous_const))))

theorem boundaryFlowExitTime_mem_iff {g : SmoothRiemannianMetric I N}
    {seed : TangentBundle I N} {a : ℝ} {t : ℝ} (ht : 0 < t) :
    t ∈ boundaryFlowExitDomain g seed a ↔ ENNReal.ofReal t < boundaryFlowExitTime g seed a := by
  constructor
  · intro htD
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
      ((boundaryFlowExitDomain_isOpen g seed a).mem_nhds htD)
    have hr : t + δ / 2 ∈ boundaryFlowExitDomain g seed a := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, show t + δ / 2 - t = δ / 2 by ring,
        abs_of_pos (by positivity : 0 < δ / 2)]
      linarith
    have hlt : ENNReal.ofReal t < ENNReal.ofReal (t + δ / 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < t + δ / 2)).mpr (by linarith)
    exact hlt.trans_le (le_sSup ⟨t + δ / 2, hr, rfl⟩)
  · intro hlt
    obtain ⟨r, hr, htr⟩ := lt_sSup_iff.mp hlt
    obtain ⟨s, hs, hsr⟩ := hr
    rw [← hsr] at htr
    exact boundaryFlowExitDomain_down g seed a ht
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp htr).le hs

theorem boundaryFlowExitTime_pos (g : SmoothRiemannianMetric I N)
    (seed : TangentBundle I N) {a : ℝ} (ha : 0 < a) : 0 < boundaryFlowExitTime g seed a := by
  have hhalf : 0 < a / 2 := by positivity
  have hmem : a / 2 ∈ boundaryFlowExitDomain g seed a := ⟨hhalf, Or.inl (by linarith)⟩
  exact ((ENNReal.ofReal_pos.mpr hhalf).trans
    ((boundaryFlowExitTime_mem_iff (g := g) (seed := seed) (a := a) hhalf).mp hmem))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
