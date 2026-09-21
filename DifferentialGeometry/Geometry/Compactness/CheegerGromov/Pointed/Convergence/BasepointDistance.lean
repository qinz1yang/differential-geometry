import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphCurves
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}


attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianConvergenceMaps.basepoint_distance_eq_of_tendsto_inverse_segment
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {Q : PointedRiemannianManifold.{u, uE, uH} I} [ConnectedSpace Q.M]
    {chi : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X Q chi)
    (C : MetricConvergenceData F)
    (hreference : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hconnected : ∀ i, ConnectedSpace (X.obj (chi i)).M)
    {A d : ℝ} (hd : 0 < d) (hdA : d < A)
    (hcapture : ∃ K : Set Q.M, IsCompact K ∧ ∀ᶠ i in atTop,
      riemannianBallOf (X.obj (chi i)).metric (X.obj (chi i)).basepoint A ⊆ F.map i '' K)
    (gamma : ∀ i, ℝ → (X.obj (chi i)).M) (length b : ℕ → ℝ)
    (hzero : ∀ i, gamma i 0 = (X.obj (chi i)).basepoint)
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (length i), ∀ t ∈ Icc 0 (length i),
      (riemannianEDistOf (X.obj (chi i)).metric (gamma i s) (gamma i t)).toReal = |s - t|)
    (hb : ∀ᶠ i in atTop, b i ∈ Icc 0 (length i))
    (hblim : Tendsto b atTop (𝓝 d)) (q : Q.M)
    (hq : Tendsto (fun i => (F.partialDiffeomorph i).symm (gamma i (b i))) atTop (𝓝 q)) :
    (riemannianEDistOf Q.metric Q.basepoint q).toReal = d := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace Q.M := ChartedSpace.locallyCompactSpace H Q.M
  let M := fun i => (X.obj (chi i)).M
  let g := fun i => (X.obj (chi i)).metric
  let : RiemannianBundle (fun x : Q.M => TangentSpace I x) := Q.riemBundle
  let : IsContinuousRiemannianBundle E (fun x : Q.M => TangentSpace I x) := Q.riemBundle_cont
  let : TopologicalSpace.MetrizableSpace Q.M := Manifold.metrizableSpace I Q.M
  let : T3Space Q.M := inferInstance
  let : MetricSpace Q.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I)
  have hnorm : Geometry.Riemannian.IsMetricNorm Q.metric :=
    Geometry.Riemannian.isMetricNorm_of_riemannianBundle Q.metric
  let : IsRiemannianManifold I Q.M := ⟨fun x y => by
    rw [edist_dist, Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := I)]
    exact ENNReal.ofReal_toReal (Geometry.Riemannian.Exponential.riemannianEDist_ne_top x y)⟩
  let : ∀ i, ConnectedSpace (M i) := fun i => hconnected i
  let : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x) := fun i => ⟨(g i).toRiemannianMetric⟩
  let : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x) :=
    fun i => ⟨⟨(g i).inner, (g i).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : ∀ i, TopologicalSpace.MetrizableSpace (M i) := fun i => Manifold.metrizableSpace I (M i)
  let : ∀ i, T3Space (M i) := fun i => inferInstance
  let : ∀ i, MetricSpace (M i) := fun i => Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I)
  let : ∀ i, IsRiemannianManifold I (M i) := fun i => ⟨fun x y => by
    rw [edist_dist, Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := I)]
    exact ENNReal.ofReal_toReal (Geometry.Riemannian.Exponential.riemannianEDist_ne_top x y)⟩
  have hnorms (i : ℕ) : Geometry.Riemannian.IsMetricNorm (g i) :=
    Geometry.Riemannian.isMetricNorm_of_riemannianBundle (g i)
  have hdist (i : ℕ) (x y : M i) : dist x y = (riemannianEDistOf (g i) x y).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist (g i) (hnorms i)]
    exact Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := I) x y
  let G : ∀ i, PartialDiffeomorph I I Q.M (M i) ∞ := fun i => F.partialDiffeomorph i
  have hupper : ∀ K : Set Q.M, IsCompact K → ∀ L : ℝ, 1 < L → ∀ᶠ i in atTop,
      (∀ x ∈ K, ContMDiffAt I I 1 (G i) x) ∧
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        ‖mfderiv I I (G i) x v‖ₑ ≤ ENNReal.ofReal L * ‖v‖ₑ := by
    intro K hK L hL
    obtain ⟨N, hN⟩ := PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control C hreference K hK
      (L ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with i hi
    refine ⟨fun x hx => ((G i).contMDiffOn_toFun.contMDiffAt
      ((G i).open_source.mem_nhds ((hN i hi).1 hx))).of_le (by simp), ?_⟩
    intro x hx v
    have hh := (abs_le.mp ((hN i hi).2 x hx v)).2
    change (g i).inner (G i x) (mfderiv I I (G i) x v) (mfderiv I I (G i) x v) -
      Q.metric.inner x v v ≤ (L ^ 2 - 1) * Q.metric.inner x v v at hh
    have hv := hnorms i (G i x) (mfderiv I I (G i) x v)
    have hw := hnorm x v
    have hL0 : 0 ≤ L := by linarith
    erw [hv, hw, ← ENNReal.ofReal_mul hL0]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.sqrt (L ^ 2 * Q.metric.inner x v v) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0]
  have hlower : ∀ K : Set Q.M, IsCompact K → ∀ e : ℝ, 0 < e → ∀ᶠ i in atTop,
      K ⊆ (G i).source ∧ ∀ x ∈ K, ∀ v : TangentSpace I x,
        (1 - e) * Q.metric.inner x v v ≤ (g i).inner (G i x)
          (mfderiv I I (G i) x v) (mfderiv I I (G i) x v) := by
    intro K hK e he
    obtain ⟨N, hN⟩ := PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control C hreference K hK e he
    filter_upwards [eventually_ge_atTop N] with i hi
    refine ⟨(hN i hi).1, fun x hx v => ?_⟩
    have hh := (abs_le.mp ((hN i hi).2 x hx v)).1
    change - (e * Q.metric.inner x v v) ≤
      (g i).inner (G i x) (mfderiv I I (G i) x v) (mfderiv I I (G i) x v) -
        Q.metric.inner x v v at hh
    linarith
  let delta : ∀ i, ℝ → M i := fun i t => gamma i (b i * t / d)
  have hparam (i : ℕ) (hi : b i ∈ Icc 0 (length i)) {t : ℝ} (ht : t ∈ Icc 0 d) :
      b i * t / d ∈ Icc 0 (length i) := by
    constructor
    · exact div_nonneg (mul_nonneg hi.1 ht.1) hd.le
    · have hh : b i * t / d ≤ b i := (div_le_iff₀ hd).mpr
        (mul_le_mul_of_nonneg_left ht.2 hi.1)
      exact hh.trans hi.2
  have hdeltaDist (i : ℕ) (hi : b i ∈ Icc 0 (length i))
      (s : ℝ) (hs : s ∈ Icc 0 d) (t : ℝ) (ht : t ∈ Icc 0 d) :
      dist (delta i s) (delta i t) = (b i / d) * dist s t := by
    rw [hdist, hsegment i _ (hparam i hi hs) _ (hparam i hi ht), Real.dist_eq]
    rw [show b i * s / d - b i * t / d = (b i / d) * (s - t) by ring,
      abs_mul, abs_of_nonneg (div_nonneg hi.1 hd.le)]
  have hratio : Tendsto (fun i => b i / d) atTop (𝓝 (1 : ℝ)) := by
    simpa only [div_self hd.ne'] using hblim.div_const d
  have hdeltaLip : ∀ B : ℝ≥0, 1 < B → ∀ᶠ i in atTop, LipschitzOnWith B (delta i) (Icc 0 d) := by
    intro B hB
    have hBR : (1 : ℝ) < (B : ℝ) := hB
    filter_upwards [hb, hratio.eventually (eventually_lt_nhds hBR)] with i hi hBi
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [hdeltaDist i hi s hs t ht]
    exact mul_le_mul_of_nonneg_right hBi.le dist_nonneg
  obtain ⟨K, hK, hcap⟩ := hcapture
  have hKsource : ∀ᶠ i in atTop, K ⊆ (G i).source := by
    obtain ⟨N, hN⟩ := F.source_subset hK
    exact eventually_atTop.mpr ⟨N, hN⟩
  have hfull : ∀ᶠ i in atTop, ∀ t ∈ Icc 0 d,
      delta i t ∈ (G i).target ∧ (G i).symm (delta i t) ∈ K := by
    filter_upwards [hcap, hKsource, hb, hblim.eventually (eventually_lt_nhds hdA)] with i hcap hKsrc hi hbi
    intro t ht
    have hball : delta i t ∈ riemannianBallOf (g i) (X.obj (chi i)).basepoint A := by
      have hdval : (riemannianEDistOf (g i) (X.obj (chi i)).basepoint (delta i t)).toReal = b i * t / d := by
        rw [← hzero i, hsegment i 0 ⟨le_rfl, hi.1.trans hi.2⟩ _ (hparam i hi ht)]
        rw [zero_sub, abs_neg, abs_of_nonneg (hparam i hi ht).1]
      have hlt : (riemannianEDistOf (g i) (X.obj (chi i)).basepoint (delta i t)).toReal < A := by
        rw [hdval]
        exact ((div_le_iff₀ hd).mpr (mul_le_mul_of_nonneg_left ht.2 hi.1)).trans_lt hbi
      exact (ENNReal.lt_ofReal_iff_toReal_lt (riemannianEDistOf_ne_top (g i) _ _)).mpr hlt
    obtain ⟨w, hw, heq⟩ := hcap hball
    have hsrc : w ∈ (G i).source := hKsrc hw
    have htar : delta i t ∈ (G i).target := heq ▸ (G i).map_source hsrc
    have hinv : (G i).symm (delta i t) = w := by
      rw [← heq]
      exact (G i).left_inv hsrc
    exact ⟨htar, hinv ▸ hw⟩
  have hdistlim : ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d,
      Tendsto (fun i => dist (delta i s) (delta i t)) atTop (𝓝 (dist s t)) := by
    intro s hs t ht
    have hh := hratio.mul_const (dist s t)
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hb] with i hi
    exact (hdeltaDist i hi s hs t ht).symm
  have hresult := PartialDiffeomorph.tendsto_dist_symm_curve_of_compact_metric_bounds
    G Q.metric g hnorm hnorms hlower hupper delta hdeltaLip
    (hfull.mono fun _ h _ ht => (h _ ht).1)
    ⟨K, hK, hfull.mono fun _ h _ ht => (h _ ht).2⟩ hdistlim
    0 ⟨le_rfl, hd.le⟩ d ⟨hd.le, le_rfl⟩
  have hzeroInv (i : ℕ) : (G i).symm (delta i 0) = Q.basepoint := by
    have hbase : (G i) Q.basepoint = (X.obj (chi i)).basepoint := F.basepoint_map i
    dsimp only [delta]
    rw [mul_zero, zero_div, hzero i, ← hbase]
    exact (G i).left_inv (F.base_mem i)
  have hdInv (i : ℕ) : (G i).symm (delta i d) = (F.partialDiffeomorph i).symm (gamma i (b i)) := by
    exact congrArg (fun t => (F.partialDiffeomorph i).symm (gamma i t))
      (mul_div_cancel_right₀ (b i) hd.ne')
  simp only [hzeroInv, hdInv, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hd] at hresult
  have hqlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Q.basepoint) atTop (𝓝 Q.basepoint)).dist hq
  have heq : dist Q.basepoint q = d := tendsto_nhds_unique hqlim hresult
  rw [← heq, riemannianEDistOf_eq_riemannianEDist Q.metric hnorm]
  exact (Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := I) Q.basepoint q).symm

end DifferentialGeometry.CheegerGromovCompactness

end
