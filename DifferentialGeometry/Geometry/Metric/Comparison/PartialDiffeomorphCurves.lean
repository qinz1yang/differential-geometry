import DifferentialGeometry.Geometry.Metric.Comparison.CompactMapDistance
import DifferentialGeometry.Topology.MetricSpace.LocalLipschitzComposition
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

namespace DifferentialGeometry.PartialDiffeomorph

open Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section MetricUpper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PseudoMetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [RiemannianBundle (fun y : N => TangentSpace I y)] [IsRiemannianManifold I N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lipschitzOnWith_comp_of_metric_upper
    (Φ : PartialDiffeomorph I I N M ∞)
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : Geometry.Riemannian.IsMetricNorm g)
    (hhnorm : Geometry.Riemannian.IsMetricNorm h)
    {V : Set N} (hV : IsOpen V) (hsource : V ⊆ Φ.source)
    {L : ℝ} (hL : 0 < L)
    (hupper : ∀ x ∈ V, ∀ v : TangentSpace I x,
      g.inner (Φ x) (mfderiv I I (Φ : N → M) x v)
        (mfderiv I I (Φ : N → M) x v) ≤ L ^ 2 * h.inner x v v)
    {gamma : ℝ → N} {a b : ℝ} {C : ℝ≥0}
    (hgamma : LipschitzOnWith C gamma (Icc a b)) (hmem : MapsTo gamma (Icc a b) V) :
    LipschitzOnWith (⟨L, hL.le⟩ * C) ((Φ : N → M) ∘ gamma) (Icc a b) := by
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    hgnorm.isContinuousRiemannianBundle
  let : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    hhnorm.isContinuousRiemannianBundle
  have hgedist (x y : M) : riemannianEDistOf g x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hgnorm, ← IsRiemannianManifold.out]
  have hhedist (x y : N) : riemannianEDistOf h x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist h hhnorm, ← IsRiemannianManifold.out]
  let D : ℝ≥0 := ⟨L, hL.le⟩
  have hlocal (y : N) (hy : y ∈ V) :
      ∃ s ∈ 𝓝 y, LipschitzOnWith D (Φ : N → M) s := by
    obtain ⟨R, hR, hRV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hy)
    refine ⟨Metric.ball y (R / 4), Metric.ball_mem_nhds y (by positivity), ?_⟩
    intro z hz w hw
    have hball (x : N) (hx : x ∈ riemannianClosedBallOf h y R) : x ∈ Metric.closedBall y R := by
      change riemannianEDistOf h y x ≤ ENNReal.ofReal R at hx
      rw [hhedist, edist_dist, ENNReal.ofReal_le_ofReal_iff hR.le] at hx
      exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hx)
    have hzball : z ∈ riemannianClosedBallOf h y (R / 4) := by
      change riemannianEDistOf h y z ≤ ENNReal.ofReal (R / 4)
      rw [hhedist, edist_dist]
      exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using (Metric.mem_ball.mp hz).le)
    have hwball : w ∈ riemannianClosedBallOf h y (R / 4) := by
      change riemannianEDistOf h y w ≤ ENNReal.ofReal (R / 4)
      rw [hhedist, edist_dist]
      exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using (Metric.mem_ball.mp hw).le)
    have hbound := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      h g Φ y z w (by positivity : 0 ≤ R / 4) (by linarith : 3 * (R / 4) < R)
      hL (fun x hx => hsource (hRV (hball x hx)))
      (fun x hx => hupper x (hRV (hball x hx))) hzball hwball
    have hbound' : edist (Φ z) (Φ w) ≤ ENNReal.ofReal L * edist z w := by
      simpa only [hgedist, hhedist] using hbound
    have hcoe : (D : ℝ≥0∞) = ENNReal.ofReal L := ENNReal.coe_nnreal_eq _
    rw [hcoe]
    exact hbound'
  apply DifferentialGeometry.Topology.lipschitzOnWith_comp_of_locally_lipschitzOn hgamma
  rintro x ⟨s, hs, rfl⟩
  exact hlocal (gamma s) (hmem hs)

end MetricUpper

noncomputable section InverseMetricUpper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metric_upper_symm_of_metric_lower
    (Φ : PartialDiffeomorph I I M N ∞)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    {V : Set M} (hsource : V ⊆ Φ.source) {L : ℝ}
    (hlower : ∀ x ∈ V, ∀ v : TangentSpace I x,
      g.inner x v v ≤ L ^ 2 * h.inner (Φ x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x v)) :
    ∀ y ∈ (Φ : M → N) '' V, ∀ v : TangentSpace I y,
      g.inner (Φ.symm y) (mfderiv I I (Φ.symm : N → M) y v)
        (mfderiv I I (Φ.symm : N → M) y v) ≤ L ^ 2 * h.inner y v v := by
  intro y hy v
  obtain ⟨x, hx, rfl⟩ := hy
  have hxsource := hsource hx
  have hytarget := Φ.map_source hxsource
  have hback : (Φ.symm : N → M) (Φ x) = x := Φ.left_inv hxsource
  have hF := (Φ.contMDiffOn_toFun.contMDiffAt
    (Φ.open_source.mem_nhds hxsource)).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hG := (Φ.symm.contMDiffOn_toFun.contMDiffAt
    (Φ.open_target.mem_nhds hytarget)).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have heq : ((Φ : M → N) ∘ (Φ.symm : N → M)) =ᶠ[𝓝 (Φ x)] id := by
    filter_upwards [Φ.open_target.mem_nhds hytarget] with z hz
    exact Φ.right_inv hz
  have hder : mfderiv I I (Φ : M → N) x
      (mfderiv I I (Φ.symm : N → M) (Φ x) v) = v := by
    have hf : MDifferentiableAt I I (Φ : M → N) (Φ.symm (Φ x)) := hback.symm ▸ hF
    have hd := congrArg (fun A => A v) (mfderiv_comp (Φ x) hf hG)
    rw [heq.mfderiv_eq, mfderiv_id] at hd
    have hdback := congrArg (fun z : M =>
      (mfderiv I I (Φ : M → N) z (mfderiv I I (Φ.symm : N → M) (Φ x) v) : E)) hback
    change v = mfderiv I I (Φ : M → N) ((Φ.symm : N → M) (Φ x))
      (mfderiv I I (Φ.symm : N → M) (Φ x) v) at hd
    rw [hdback] at hd
    exact hd.symm
  have hb := hlower x hx (mfderiv I I (Φ.symm : N → M) (Φ x) v)
  have hgback := congrArg (fun z : M =>
    g.inner z (mfderiv I I (Φ.symm : N → M) (Φ x) v)
      (mfderiv I I (Φ.symm : N → M) (Φ x) v)) hback
  rw [hgback]
  simpa only [hder] using hb

end InverseMetricUpper

noncomputable section InverseMetricLower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PseudoMetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [RiemannianBundle (fun y : N => TangentSpace I y)] [IsRiemannianManifold I N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lipschitzOnWith_symm_comp_of_metric_lower
    (Φ : PartialDiffeomorph I I M N ∞)
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : Geometry.Riemannian.IsMetricNorm g)
    (hhnorm : Geometry.Riemannian.IsMetricNorm h)
    {U : Set M} (hU : IsOpen U) (hsource : U ⊆ Φ.source)
    {L : ℝ} (hL : 0 < L)
    (hlower : ∀ x ∈ U, ∀ v : TangentSpace I x,
      g.inner x v v ≤ L ^ 2 * h.inner (Φ x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x v))
    {gamma : ℝ → N} {a b : ℝ} {C : ℝ≥0}
    (hgamma : LipschitzOnWith C gamma (Icc a b))
    (hmem : MapsTo gamma (Icc a b) ((Φ : M → N) '' U)) :
    LipschitzOnWith (⟨L, hL.le⟩ * C) ((Φ.symm : N → M) ∘ gamma) (Icc a b) := by
  apply lipschitzOnWith_comp_of_metric_upper Φ.symm hgnorm hhnorm
    (Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU hsource)
    (by rintro y ⟨x, hx, rfl⟩; exact Φ.map_source (hsource hx)) hL
    (metric_upper_symm_of_metric_lower Φ g h hsource hlower) hgamma hmem

end InverseMetricLower

noncomputable section CompactMetricLower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [WeaklyLocallyCompactSpace M]
  {N : ℕ → Type*} [∀ n, PseudoMetricSpace (N n)]
  [∀ n, ChartedSpace H (N n)] [∀ n, IsManifold I ∞ (N n)]
  [∀ n, RiemannianBundle (fun y : N n => TangentSpace I y)]
  [∀ n, IsRiemannianManifold I (N n)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_lipschitzOnWith_symm_comp_of_compact_metric_lower
    (Φ : ∀ n, PartialDiffeomorph I I M (N n) ∞)
    (g : SmoothRiemannianMetric I M) (h : ∀ n, SmoothRiemannianMetric I (N n))
    (hgnorm : Geometry.Riemannian.IsMetricNorm g)
    (hhnorm : ∀ n, Geometry.Riemannian.IsMetricNorm (h n))
    (hlower : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      K ⊆ (Φ n).source ∧ ∀ x ∈ K, ∀ v : TangentSpace I x,
        (1 - ε) * g.inner x v v ≤ (h n).inner (Φ n x)
          (mfderiv I I (Φ n : M → N n) x v) (mfderiv I I (Φ n : M → N n) x v))
    (gamma : ∀ n, ℝ → N n) {a b : ℝ}
    (hgamma : ∀ C : ℝ≥0, 1 < C → ∀ᶠ n in atTop, LipschitzOnWith C (gamma n) (Icc a b))
    (htarget : ∀ᶠ n in atTop, MapsTo (gamma n) (Icc a b) (Φ n).target)
    (hcompact : ∃ K : Set M, IsCompact K ∧ ∀ᶠ n in atTop,
      MapsTo ((Φ n).symm ∘ gamma n) (Icc a b) K)
    {C : ℝ≥0} (hC : 1 < C) :
    ∀ᶠ n in atTop, LipschitzOnWith C ((Φ n).symm ∘ gamma n) (Icc a b) := by
  obtain ⟨K, hK, htrap⟩ := hcompact
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  let L : ℝ := Real.sqrt C
  have hCsq : L ^ 2 = (C : ℝ) := Real.sq_sqrt C.property
  have hLnonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hCreal : (1 : ℝ) < C := hC
  have hL : 1 < L := by nlinarith
  let D : ℝ≥0 := ⟨L, hLnonneg⟩
  have hD : 1 < D := hL
  have hDC : D * D = C := by
    ext
    change L * L = (C : ℝ)
    nlinarith [hCsq]
  let ε : ℝ := 1 - 1 / L ^ 2
  have hε : 0 < ε := by
    dsimp only [ε]
    apply sub_pos.mpr
    apply (div_lt_one (sq_pos_of_pos (lt_trans zero_lt_one hL))).2
    nlinarith
  have hweight : L ^ 2 * (1 - ε) = 1 := by
    dsimp only [ε]
    field_simp
    ring
  filter_upwards [hlower K' hK' ε hε, hgamma D hD, htarget, htrap] with n hn hgam htar htr
  have hmem : MapsTo (gamma n) (Icc a b) ((Φ n : M → N n) '' interior K') := by
    intro s hs
    exact ⟨(Φ n).symm (gamma n s), hKK' (htr hs), (Φ n).right_inv (htar hs)⟩
  have hLip := lipschitzOnWith_symm_comp_of_metric_lower (Φ n) hgnorm (hhnorm n)
    isOpen_interior (interior_subset.trans hn.1) (lt_trans zero_lt_one hL)
    (fun x hx v => by
      have hb := mul_le_mul_of_nonneg_left (hn.2 x (interior_subset hx) v) (sq_nonneg L)
      rwa [← mul_assoc, hweight, one_mul] at hb) hgam hmem
  change LipschitzOnWith (D * D) ((Φ n).symm ∘ gamma n) (Icc a b) at hLip
  rwa [hDC] at hLip

end CompactMetricLower

noncomputable section DistanceConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [WeaklyLocallyCompactSpace M]
  {N : ℕ → Type*} [∀ n, PseudoMetricSpace (N n)]
  [∀ n, ChartedSpace H (N n)] [∀ n, IsManifold I ∞ (N n)]
  [∀ n, RiemannianBundle (fun y : N n => TangentSpace I y)]
  [∀ n, IsRiemannianManifold I (N n)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tendsto_dist_symm_curve_of_compact_metric_bounds
    (Φ : ∀ n, PartialDiffeomorph I I M (N n) ∞)
    (g : SmoothRiemannianMetric I M) (h : ∀ n, SmoothRiemannianMetric I (N n))
    (hgnorm : Geometry.Riemannian.IsMetricNorm g)
    (hhnorm : ∀ n, Geometry.Riemannian.IsMetricNorm (h n))
    (hlower : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      K ⊆ (Φ n).source ∧ ∀ x ∈ K, ∀ v : TangentSpace I x,
        (1 - ε) * g.inner x v v ≤ (h n).inner (Φ n x)
          (mfderiv I I (Φ n : M → N n) x v) (mfderiv I I (Φ n : M → N n) x v))
    (hupper : ∀ K : Set M, IsCompact K → ∀ L : ℝ, 1 < L → ∀ᶠ n in atTop,
      (∀ x ∈ K, ContMDiffAt I I 1 (Φ n : M → N n) x) ∧
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        ‖mfderiv I I (Φ n : M → N n) x v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ)
    (gamma : ∀ n, ℝ → N n) {a b : ℝ}
    (hgamma : ∀ C : ℝ≥0, 1 < C → ∀ᶠ n in atTop, LipschitzOnWith C (gamma n) (Icc a b))
    (htarget : ∀ᶠ n in atTop, MapsTo (gamma n) (Icc a b) (Φ n).target)
    (hcompact : ∃ K : Set M, IsCompact K ∧ ∀ᶠ n in atTop,
      MapsTo ((Φ n).symm ∘ gamma n) (Icc a b) K)
    (hdist : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      Tendsto (fun n => dist (gamma n s) (gamma n t)) atTop (𝓝 (dist s t))) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      Tendsto (fun n => dist ((Φ n).symm (gamma n s)) ((Φ n).symm (gamma n t)))
        atTop (𝓝 (dist s t)) := by
  intro s hs t ht
  apply Geometry.Riemannian.tendsto_dist_of_compact_map_distance_convergence
    (fun n => (Φ n : M → N n)) hupper
    (fun n => (Φ n).symm (gamma n s)) (fun n => (Φ n).symm (gamma n t))
  · obtain ⟨K, hK, htrap⟩ := hcompact
    exact ⟨K, hK, htrap.mono fun n hn => ⟨hn hs, hn ht⟩⟩
  · apply Tendsto.congr' _ (hdist s hs t ht)
    filter_upwards [htarget] with n hn
    exact congrArg₂ dist ((Φ n).right_inv (hn hs)).symm ((Φ n).right_inv (hn ht)).symm
  · intro C hC
    let D : ℝ≥0 := ⟨C, (lt_trans zero_lt_one hC).le⟩
    have hD : 1 < D := hC
    filter_upwards [eventually_lipschitzOnWith_symm_comp_of_compact_metric_lower
      Φ g h hgnorm hhnorm hlower gamma hgamma htarget hcompact hD] with n hn
    exact hn.dist_le_mul s hs t ht


end DistanceConvergence

end DifferentialGeometry.PartialDiffeomorph
