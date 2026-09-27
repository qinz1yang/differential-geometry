import DifferentialGeometry.Topology.MetricSpace.LocalLipschitzComposition
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.BallImage

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type u} [PseudoMetricSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PseudoMetricSpace N] [T2Space N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [RiemannianBundle (fun y : N => TangentSpace I y)] [IsRiemannianManifold I N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PartialDiffeomorphMetricApproximation.lipschitzOnWith_symm_comp
    (Φ : PartialDiffeomorph I I M N ∞) {K : Set M} {ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : Geometry.Riemannian.IsMetricNorm g)
    (hhnorm : Geometry.Riemannian.IsMetricNorm h)
    (D : PartialDiffeomorphMetricApproximation K ε p Φ g h)
    {V : Set N} (hV : IsOpen V) (hcapture : V ⊆ (Φ : M → N) '' K)
    {gamma : ℝ → N} {a b : ℝ} {C : ℝ≥0}
    (hgamma : LipschitzOnWith C gamma (Icc a b)) (hmem : MapsTo gamma (Icc a b) V) :
    LipschitzOnWith (⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩ * C)
        ((Φ.symm : N → M) ∘ gamma) (Icc a b) ∧
      MapsTo ((Φ.symm : N → M) ∘ gamma) (Icc a b) K ∧
      ∀ s ∈ Icc a b, Φ (Φ.symm (gamma s)) = gamma s := by
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    hgnorm.isContinuousRiemannianBundle
  let : IsContinuousRiemannianBundle E (fun y : N => TangentSpace I y) :=
    hhnorm.isContinuousRiemannianBundle
  have hgedist (x y : M) : riemannianEDistOf g x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hgnorm, ← IsRiemannianManifold.out]
  have hhedist (x y : N) : riemannianEDistOf h x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist h hhnorm, ← IsRiemannianManifold.out]
  have htarget (y : N) (hy : y ∈ V) : y ∈ Φ.target ∧ Φ.symm y ∈ K := by
    obtain ⟨x, hx, rfl⟩ := hcapture hy
    exact ⟨Φ.map_source (D.source_sub hx), by
      change Φ.invFun (Φ x) ∈ K
      rw [Φ.left_inv' (D.source_sub hx)]
      exact hx⟩
  let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
  have hLpos : 0 < Real.sqrt (1 + ε) := Real.sqrt_pos.mpr (by linarith [D.forward.eps_pos])
  have hlocal (y : N) (hy : y ∈ V) :
      ∃ s ∈ 𝓝 y, LipschitzOnWith L (Φ.symm : N → M) s := by
    obtain ⟨R, hR, hRV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hy)
    refine ⟨Metric.ball y (R / 4), Metric.ball_mem_nhds y (by positivity), ?_⟩
    intro z hz w hw
    have hsource : riemannianClosedBallOf h y R ⊆ Φ.symm.source := by
      intro x hx
      have hxball : x ∈ Metric.closedBall y R := by
        change riemannianEDistOf h y x ≤ ENNReal.ofReal R at hx
        rw [hhedist, edist_dist, ENNReal.ofReal_le_ofReal_iff hR.le] at hx
        exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hx)
      exact (htarget x (hRV hxball)).1
    have hupper : ∀ x ∈ riemannianClosedBallOf h y R, ∀ v : TangentSpace I x,
        g.inner (Φ.symm x) (mfderiv I I (Φ.symm : N → M) x v)
            (mfderiv I I (Φ.symm : N → M) x v) ≤
          (Real.sqrt (1 + ε)) ^ 2 * h.inner x v v := by
      intro x hx v
      have hxball : x ∈ Metric.closedBall y R := by
        change riemannianEDistOf h y x ≤ ENNReal.ofReal R at hx
        rw [hhedist, edist_dist, ENNReal.ofReal_le_ofReal_iff hR.le] at hx
        exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hx)
      rw [Real.sq_sqrt (by linarith [D.forward.eps_pos] : 0 ≤ 1 + ε),
        ← D.reverse.pullback_apply x (hcapture (hRV hxball)) (fun _ => v)]
      exact (tensor_apply_bounds_of_metricTensorErrorNorm_le D.reverse.pullback h
        (D.reverse.c0_small x (hcapture (hRV hxball))) v).2
    have hzball : z ∈ riemannianClosedBallOf h y (R / 4) := by
      change riemannianEDistOf h y z ≤ ENNReal.ofReal (R / 4)
      rw [hhedist, edist_dist]
      exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using (Metric.mem_ball.mp hz).le)
    have hwball : w ∈ riemannianClosedBallOf h y (R / 4) := by
      change riemannianEDistOf h y w ≤ ENNReal.ofReal (R / 4)
      rw [hhedist, edist_dist]
      exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using (Metric.mem_ball.mp hw).le)
    have hbound := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      h g Φ.symm y z w (by positivity : 0 ≤ R / 4) (by linarith : 3 * (R / 4) < R)
      hLpos hsource hupper hzball hwball
    have hbound' : edist (Φ.symm z) (Φ.symm w) ≤
        ENNReal.ofReal (Real.sqrt (1 + ε)) * edist z w := by
      simpa only [hgedist, hhedist] using hbound
    have hcoe : (L : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (1 + ε)) := by
      exact ENNReal.coe_nnreal_eq _
    rw [hcoe]
    exact hbound'
  have hLip : LipschitzOnWith (L * C) ((Φ.symm : N → M) ∘ gamma) (Icc a b) := by
    apply DifferentialGeometry.Topology.lipschitzOnWith_comp_of_locally_lipschitzOn
      (f := (Φ.symm : N → M)) (gamma := gamma) (a := a) (b := b) (C := C) (L := L) hgamma
    rintro x ⟨s, hs, rfl⟩
    exact hlocal (gamma s) (hmem hs)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [L] using hLip
  · intro s hs
    exact (htarget (gamma s) (hmem hs)).2
  · intro s hs
    exact Φ.right_inv' (htarget (gamma s) (hmem hs)).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PartialDiffeomorphMetricApproximation.lipschitzOnWith_symm_comp_of_mapsTo_ball
    (Φ : PartialDiffeomorph I I M N ∞) {O x : M} {r R A ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : Geometry.Riemannian.IsMetricNorm g)
    (hhnorm : Geometry.Riemannian.IsMetricNorm h)
    (hcompact : IsCompact (Metric.closedBall O R))
    (hx : x ∈ Metric.ball O r) (hmargin : Real.sqrt (1 + ε) * A + r < R)
    (D : PartialDiffeomorphMetricApproximation (Metric.closedBall O R) ε p Φ g h)
    {gamma : ℝ → N} {a b : ℝ} {C : ℝ≥0}
    (hgamma : LipschitzOnWith C gamma (Icc a b))
    (hmem : MapsTo gamma (Icc a b) (Metric.ball (Φ x) A)) :
    LipschitzOnWith (⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩ * C)
        ((Φ.symm : N → M) ∘ gamma) (Icc a b) ∧
      MapsTo ((Φ.symm : N → M) ∘ gamma) (Icc a b) (Metric.closedBall O R) ∧
      ∀ s ∈ Icc a b, Φ (Φ.symm (gamma s)) = gamma s := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact D.lipschitzOnWith_symm_comp Φ hgnorm hhnorm Metric.isOpen_ball
    (D.ball_subset_image_closedBall Φ hgnorm hhnorm hcompact hx hmargin) hgamma hmem

end DifferentialGeometry.CheegerGromovCompactness
