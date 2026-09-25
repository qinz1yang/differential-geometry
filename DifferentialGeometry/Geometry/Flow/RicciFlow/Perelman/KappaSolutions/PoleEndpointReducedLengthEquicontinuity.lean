import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.LocalDistanceBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthSpatialDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeModulus
import Mathlib.Topology.MetricSpace.Equicontinuity


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_on_compact
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ J, ∀ y ∈ J, ∀ t ∈ Icc a c,
      riemannianEDistOf R x y < ENNReal.ofReal 1 →
      |redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) x) t -
        redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) t| ≤
          C * (riemannianEDistOf R x y).toReal := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨s, _hs, z, hz⟩ := (hancient 0).notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric s) z (by norm_num : 0 < 4) _ hz⟩
  have hapos : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨n, hn⟩ := exists_nat_gt c
  have hsub : Icc (1 - c) (1 - a) ⊆ Icc (-(n : ℝ)) 0 := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  let coW : FlowMetricConvergenceData Phi R bf hsrc htgt (1 - c) (1 - a) :=
    FlowMetricConvergenceData.restrict Phi
      (HalfLineMetricConvergenceData.atWindow Phi co n) hsub
  have hcarrier : Icc (1 - c) (1 - a) ⊆ (Y).D.carrier := by
    intro s hs
    change s ≤ 0
    linarith [hs.2]
  have hG := FlowMetricConvergenceData.metric_cont (Φ := Phi) hcarrier coW
  obtain ⟨B, hB, hdist⟩ :=
    FlowMetricConvergenceData.exists_eventually_local_edist_map_map_le_on_compact
      Phi R hR bf hsrc htgt coW hG hJ
  obtain ⟨V, _hV, hcost⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) hapos hbase
  refine ⟨(Real.sqrt 3 / Real.sqrt a * Real.sqrt V) * B, by positivity, ?_⟩
  filter_upwards [hdist, hcost] with k hdistk hcostk
  intro x hx y hy t ht hxy
  have htime : 1 - t ∈ Icc (1 - c) (1 - a) := by
    constructor <;> linarith [ht.1, ht.2]
  have hmapY : riemannianEDistOf
      (((Y).term (phi (co.φ k))).S.base.metric (1 - t))
      (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) ≤
        ENNReal.ofReal B * riemannianEDistOf R x y :=
    hdistk (1 - t) htime x hx y hxy
  have hshift : ((Y).term (phi (co.φ k))).S.base.metric (1 - t) =
      ((U).term (phi (co.φ k))).S.base.metric (-t) := by
    have heq := poleEndpointRescaledFlowSeq_metric_eq_shift
      F hcar hreg b hbmem tau q hsigma (phi (co.φ k)) (1 - t)
    have htimeEq : 1 - t - 1 = -t := by ring
    simpa only [htimeEq] using heq
  have hmap : riemannianEDistOf (((U).term (phi (co.φ k))).S.base.metric (-t))
      (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) ≤
        ENNReal.ofReal B * riemannianEDistOf R x y := by
    rw [hshift] at hmapY
    exact hmapY
  have hfinite : riemannianEDistOf R x y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy.le
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hmap
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hreal
  have hbound := abs_redLength_sub_le_of_time_lower_bound
    ((U).term (phi (co.φ k))) (hancient (phi (co.φ k))) p
    (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
    hapos ht.1 (hcostk x hx t ht) (hcostk y hy t ht) hreal
  simpa only [mul_assoc] using hbound

theorem exists_eventually_abs_poleEndpoint_redLength_sub_le_on_compact_time_interval
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ y ∈ J, ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      |redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) s -
        redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) t| ≤
          C * |s - t| := by
  obtain ⟨V, hV, hcost⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  refine ⟨(2 * max c 0 / a ^ 2) * V, by positivity, ?_⟩
  filter_upwards [hcost] with k hk
  intro y hy s hs t ht
  exact ancient_abs_redLength_sub_le_mul_abs_sub_of_le
    ((U).term (phi (co.φ k))) (hancient (phi (co.φ k))) p (Phi.map (co.φ k) y)
    ha hs ht hV (hk y hy s hs) (hk y hy t ht)

theorem exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᶠ k in atTop,
      ∀ x ∈ J, ∀ y ∈ J, ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      riemannianEDistOf R x y < ENNReal.ofReal 1 →
      |redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) x) s -
        redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) t| ≤
          C * (riemannianEDistOf R x y).toReal + D * |s - t| := by
  obtain ⟨C, hC, hspace⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨Dt, hDt, htime⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) (zero_lt_one.trans_le ha) hbase
  refine ⟨C, Dt, hC, hDt, ?_⟩
  filter_upwards [hspace, htime] with k hspacek htimek
  intro x hx y hy s hs t ht hxy
  exact (abs_sub_le _ _ _).trans
    (add_le_add (hspacek x hx y hy s hs hxy) (htimek y hy s hs t ht))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_equicontinuous_poleEndpoint_redLength_tail_on_compact_time_interval
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ N : ℕ, Equicontinuous (fun k (z : J ×ˢ Icc a c) ↦
      redLength ((U).term (phi (co.φ (N + k)))).S 0 p
        (Phi.map (co.φ (N + k)) z.val.1) z.val.2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨s, _hs, z, hz⟩ := (hancient 0).notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric s) z (by norm_num : 0 < 4) _ hz⟩
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let : T3Space P.M := inferInstance
  let : RiemannianBundle (fun x : P.M ↦ TangentSpace I x) := ⟨R.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : P.M ↦ TangentSpace I x) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : MetricSpace P.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := P.M)
  have hedist (x y : P.M) : edist x y = riemannianEDistOf R x y :=
    IsRiemannianManifold.out (I := I) x y
  obtain ⟨C, Dt, _hC, _hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmodulus
  refine ⟨N, fun z₀ ↦ ?_⟩
  let modulus : (J ×ˢ Icc a c) → ℝ := fun z ↦
    C * dist z₀.val.1 z.val.1 + Dt * |z₀.val.2 - z.val.2|
  have hmodcont : ContinuousAt modulus z₀ := by
    dsimp [modulus]
    fun_prop
  have hmodzero : modulus z₀ = 0 := by simp [modulus]
  have hmodlim : Tendsto modulus (𝓝 z₀) (𝓝 0) := by
    simpa only [hmodzero] using hmodcont.tendsto
  apply Metric.equicontinuousAt_of_continuity_modulus modulus hmodlim
  have hdistcont : ContinuousAt (fun z : J ×ˢ Icc a c ↦ dist z₀.val.1 z.val.1) z₀ := by
    fun_prop
  have hnear : ∀ᶠ z : J ×ˢ Icc a c in 𝓝 z₀, dist z₀.val.1 z.val.1 < 1 :=
    hdistcont.tendsto (Iio_mem_nhds (by simpa only [dist_self] using zero_lt_one))
  filter_upwards [hnear] with z hz
  intro k
  have hxy : riemannianEDistOf R z₀.val.1 z.val.1 < ENNReal.ofReal 1 := by
    rw [← hedist, edist_dist, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    exact hz
  have hbound := hN (N + k) (Nat.le_add_right N k)
    z₀.val.1 z₀.property.1 z.val.1 z.property.1
    z₀.val.2 z₀.property.2 z.val.2 z.property.2 hxy
  rw [← hedist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hbound
  simpa only [Real.dist_eq] using hbound

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
