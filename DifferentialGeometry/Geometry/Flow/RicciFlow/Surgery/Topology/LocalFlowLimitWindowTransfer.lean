import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitShiftedTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitCurvature

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open private metricDerivNorm_localPullMetric_of_injective from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitShiftedTransfer
open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance opensSigmaCompactWindowTransfer {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem abs_derivWithin_scalar_le_of_local_flow_limit_of_shrinking_sliver_on_window
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    {V : ℕ → Opens P.M} (hVmono : Monotone V) (hVcover : ∀ x : P.M, ∃ k, x ∈ V k)
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    {T : ℝ} (hT : 0 < T) {c τ : ℕ → ℝ} (hτ : ∀ k, 0 < τ k) (hcτ : ∀ k, c k < τ k)
    (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))))
    {E : ℕ → Set ℝ} {ζ : ℕ → ℝ} (hζ : Tendsto ζ atTop (𝓝 0))
    (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite) {q Ctime : ℝ}
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, q < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2) :
    ∀ t ∈ Ioo (-T) 0, ∀ x : P.M, 4 * max q 1 < metricScalarAt (G t) x →
      |derivWithin (fun v => metricScalarAt (G v) x) (Iic t) t| ≤
        16 * max Ctime 0 * metricScalarAt (G t) x ^ 2 := by
  intro t ht x hxq
  set a := metricScalarAt (G t) x with ha_def
  set K := max Ctime 0 with hK_def
  have hK : 0 ≤ K := le_max_right _ _
  have hq1 : 1 ≤ max q 1 := le_max_right _ _
  have hqq : q ≤ max q 1 := le_max_left _ _
  have ha : 0 < a := by linarith
  obtain ⟨k₁, hk₁⟩ := hVcover x
  obtain ⟨l, hl⟩ := hcT t ⟨ht.1, ht.2.le⟩
  set k := max k₁ l with hk_def
  have hxk : x ∈ V k := hVmono (le_max_left _ _) hk₁
  have htk : -c k < t := lt_of_le_of_lt (neg_le_neg (hcmono (le_max_right k₁ l))) hl
  have hckτ := hcτ k
  set δ := min (min (1 / (8 * (K + 1) * a)) ((t + c k) / 2)) (-t / 2)
    with hδ_def
  have hδ1 : δ ≤ 1 / (8 * (K + 1) * a) := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ (t + c k) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ -t / 2 := min_le_right _ _
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by linarith)) (by linarith [ht.2])
  let J := Icc (t - δ) (t + δ)
  have hJwin : J ⊆ Icc (-c k) 0 :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
  have hJreg : J ⊆ Ioo (-τ k) 0 := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
  let _ : SigmaCompactSpace (V k) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (V k).isOpen)
  let xk : V k := ⟨x, hxk⟩
  let seq : ℕ → ℝ → SmoothRiemannianMetric I3 (V k) := fun i s =>
    if hi : N k ≤ ψ i then localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G s).restrictOpen (V k)
  let F : ℕ → ℝ → ℝ := fun i s => metricScalarAt (seq i s) xk
  have hlim : ∀ s ∈ Icc (-c k) 0,
      Tendsto (fun i => F i s) atTop (𝓝 (metricScalarAt (G s) x)) := by
    intro s hs
    have hcp : MetricCPConvergenceOn {xk} 2 (fun i => seq i s) ((G s).restrictOpen (V k))
        (P.metric.restrictOpen (V k)) := by
      intro η hη
      obtain ⟨j₀, hj₀⟩ := hconv k {xk} isCompact_singleton 2 η hη
      refine ⟨j₀, fun i hi => ?_⟩
      obtain ⟨hi', hb⟩ := hj₀ i hi
      change metricDerivNormSupOn {xk} 2 (if hi : N k ≤ ψ i then _ else _) _ _ < η
      rw [dite_eq_left hi']
      exact hb s hs
    have hu := (hcp.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at
      (mem_singleton xk)
    rwa [metricScalarAt_restrictOpen] at hu
  have hFeq : ∀ i (hi : N k ≤ ψ i) (s : ℝ),
      F i s = metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi xk) := by
    intro i hi s
    change metricScalarAt (if hi : N k ≤ ψ i then _ else _) xk = _
    rw [dite_eq_left hi, metricScalarAt_localPull]
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  have hta : Tendsto (fun i => F i t) atTop (𝓝 a) := hlim t ⟨htk.le, ht.2.le⟩
  have hev : ∀ᶠ i in atTop, ∃ hi : N k ≤ ψ i,
      IsSolutionOn ({ base.metric := h k (f (ψ i)) } : SolutionOn (I := I3)
        (M := W k (f (ψ i))) (RealTimeInterval.closed (-τ k) 0
          (neg_nonpos.mpr (hτ k).le))) ∧
      (∀ s ∈ Ioo (-τ k) 0, s ∉ E (f (ψ i)) → ∀ z : W k (f (ψ i)),
        q < metricScalarAt (h k (f (ψ i)) s) z →
          |derivWithin (fun v => metricScalarAt (h k (f (ψ i)) v) z) (Iic s) s| ≤
            Ctime * metricScalarAt (h k (f (ψ i)) s) z ^ 2) ∧
      a / 2 ≤ F i t ∧ F i t ≤ 2 * a ∧ ζ (f (ψ i)) < -(t + δ) := by
    filter_upwards [hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k)),
      hfψ.eventually (hsol k), hfψ.eventually (hderiv k),
      hta.eventually (Icc_mem_nhds (by linarith : a / 2 < a) (by linarith : a < 2 * a)),
      hfψ.eventually (hζ.eventually (gt_mem_nhds (show (0 : ℝ) < -(t + δ) by linarith [ht.2])))]
      with i hi hs hd hF hζi
    exact ⟨hi, hs, hd, hF.1, hF.2, hζi⟩
  have hlip_i : ∀ᶠ i in atTop, ∀ s ∈ J, ∀ s' ∈ J,
      |F i s - F i s'| ≤ K * (2 * (2 * a)) ^ 2 * |s - s'| := by
    filter_upwards [hev] with i ⟨hi, hs, hd, hlow, hup, hζi⟩
    have hFe := hFeq i hi
    set z := φ k (ψ i) hi xk
    have hfun : (fun v => F i v) = fun v => metricScalarAt (h k (f (ψ i)) v) z :=
      funext fun v => hFe v
    have hdiff : ∀ s ∈ J, DifferentiableAt ℝ (fun v => F i v) s := by
      intro s hsJ
      have h1 := hs.scalarTime (K := Ioo (-τ k) 0) (t := s) (hJreg hsJ)
        Ioo_subset_Icc_self z
      rw [hfun]
      exact h1.differentiableAt (Ioo_mem_nhds (hJreg hsJ).1 (hJreg hsJ).2)
    have hder : ∀ s ∈ J, s ∉ E (f (ψ i)) \ Icc (-(ζ (f (ψ i)))) 0 → a / 2 / 2 < F i s →
        |deriv (fun v => F i v) s| ≤ K * F i s ^ 2 := by
      intro s hsJ hsE' hs2
      have hsE : s ∉ E (f (ψ i)) := fun hsE =>
        hsE' ⟨hsE, fun hsI => by linarith [hsI.1, (show s ∈ J from hsJ).2]⟩
      have hderiv' : deriv (fun v => F i v) s =
          derivWithin (fun v => metricScalarAt (h k (f (ψ i)) v) z) (Iic s) s := by
        have hd' := hdiff s hsJ
        rw [hfun] at hd' ⊢
        exact (hd'.derivWithin (uniqueDiffWithinAt_Iic s)).symm
      rw [hderiv', hFe s]
      rw [hFe s] at hs2
      exact (hd s (hJreg hsJ) hsE z (by linarith)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have hlen : K * (t + δ - (t - δ)) ≤ 1 / (2 * (2 * a)) := by
      have h1 : K * (t + δ - (t - δ)) = 2 * K * δ := by ring
      rw [h1]
      have h2 : 2 * K * δ ≤ 2 * (K + 1) * (1 / (8 * (K + 1) * a)) :=
        mul_le_mul (by linarith) hδ1 hδ.le (by positivity)
      have h3 : 2 * (K + 1) * (1 / (8 * (K + 1) * a)) = 1 / (4 * a) := by
        field_simp
        ring
      have h4 : 1 / (2 * (2 * a)) = 1 / (4 * a) := by ring
      linarith
    exact abs_sub_le_of_abs_deriv_le_mul_sq_of_finite (u := fun v => F i v) (A := a / 2)
      (B := 2 * a) (hE (f (ψ i))) (by positivity) (by linarith) hK hdiff hder
      ⟨by linarith, by linarith⟩ hlow hup hlen
  have hlip : ∀ s ∈ J, ∀ s' ∈ J, |metricScalarAt (G s) x - metricScalarAt (G s') x| ≤
      K * (2 * (2 * a)) ^ 2 * |s - s'| := by
    intro s hs s' hs'
    have ht1 := ((hlim s (hJwin hs)).sub (hlim s' (hJwin hs'))).abs
    exact le_of_tendsto ht1 (hlip_i.mono fun i hi => hi s hs s' hs')
  have hLip : LipschitzOnWith (Real.toNNReal (K * (2 * (2 * a)) ^ 2))
      (fun v => metricScalarAt (G v) x) J := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact hlip s hs s' hs'
  have hnorm := norm_deriv_le_of_lipschitzOn
    (Icc_mem_nhds (show t - δ < t by linarith) (show t < t + δ by linarith)) hLip
  have hdiffG : DifferentiableAt ℝ (fun v => metricScalarAt (G v) x) t := by
    have h := hG.scalarTime (K := Ioo (-T) 0) (t := t) ht (fun s hs => ⟨hs.1, hs.2.le⟩) x
    exact h.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
  rw [hdiffG.derivWithin (uniqueDiffWithinAt_Iic t)]
  rw [Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)] at hnorm
  exact hnorm.trans (le_of_eq (by ring))

theorem tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz_on_window
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {c : ℕ → ℝ} {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-c k) 0,
      ∀ σ' ∈ Icc (-c k) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {s : ℝ} (hs : s ≤ 0) {σ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 s)) (hσs : ∀ n, σ n ≤ s)
    (k : ℕ) (hk : -c k < s) (K : Set (V k)) (hK : IsCompact K) (p : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
      σ (f (ψ i)) ∈ Icc (-c k) 0 ∧
      metricDerivNormSupOn K p
        (localPullMetric (h k (f (ψ i)) (σ (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
        ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
  obtain ⟨L, hL⟩ := hLip k p
  set L' := max L 0 with hL'_def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  set D := metricCovariantDerivativeComparisonConstant (E := ThreeSpace) 2 p with hD_def
  have hD0 : 0 ≤ D := metric_covariant_derivative_comparison_constant_nonneg (E := ThreeSpace) 2 p
  set Λ := Real.sqrt ((1 + 1) ^ (2 + p)) * (1 + 1 * D * ((p : ℝ) + 1)) with hΛ_def
  have hΛ0 : 0 ≤ Λ := by positivity
  have hsk : s ∈ Icc (-c k) 0 := ⟨hk.le, hs⟩
  have h0k : (0 : ℝ) ∈ Icc (-c k) 0 := ⟨by linarith, le_rfl⟩
  let _ : LocallyCompactSpace (V k) := ChartedSpace.locallyCompactSpace ThreeSpace (V k)
  obtain ⟨u, hu, hKu, hcl⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hconvAt : ∀ {t : ℝ}, t ∈ Icc (-c k) 0 → MetricCInfConvergenceOnCompacts
      (fun i => if hi : N k ≤ ψ i then
        localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi)
      else (G t).restrictOpen (V k)) ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
    intro t ht K' hK' p' η' hη'
    obtain ⟨j₀, hj₀⟩ := hconv k K' hK' p' η' hη'
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    simp only [dite_eq_left hi']
    exact hb t ht
  have hconv0 := hconvAt h0k
  rw [hG0] at hconv0
  have hswap := eventually_metricDerivNorm_swap_le hconv0 hcl p
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨j₁, hj₁⟩ := hconvAt hsk K hK p (η / 2) (by positivity)
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  have hkr : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  have himage := F.eventually_image_closed_ball_subset Cd href hPc P.basepoint hkr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  set δ' := min (s + c k) (η / (2 * (Λ * L' + 1))) with hδ'_def
  have hδ' : 0 < δ' := lt_min (by linarith) (by positivity)
  have hσlim := Metric.tendsto_nhds.mp (hσ.comp hfψ) δ' hδ'
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hψ.tendsto_atTop.eventually himage).and ((hfψ.eventually hL).and
        (hswap.and ((eventually_ge_atTop j₁).and hσlim)))))
  refine ⟨j₀, fun i hij => ?_⟩
  obtain ⟨hi, ⟨hsrc, himg⟩, hLi, hsw, hij₁, hσi⟩ := hj₀ i hij
  have hσd : |σ (f (ψ i)) - s| < δ' := by
    have h1 := hσi
    rwa [Function.comp_apply, Real.dist_eq] at h1
  have hσI : σ (f (ψ i)) ∈ Icc (-c k) 0 := by
    have h1 := (abs_lt.mp (hσd.trans_le (min_le_left _ _))).1
    exact ⟨by linarith, (hσs _).trans hs⟩
  refine ⟨hi, hσI, ?_⟩
  have hmemV : ∀ y : V k,
      (y : P.M) ∈ riemannianClosedBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2) := by
    intro y
    have hy : (y : P.M) ∈ (V k : Set P.M) := y.2
    rw [hV] at hy
    exact (show riemannianEDistOf P.metric P.basepoint y < _ from hy).le
  have hinj : Function.Injective (φ k (ψ i) hi) := by
    intro z z' hzz
    have h1 : F.map (ψ i) z = F.map (ψ i) z' := by
      rw [← hφF k (ψ i) hi z, ← hφF k (ψ i) hi z', hzz]
    exact Subtype.ext ((F.partialDiffeomorph (ψ i)).injOn (hsrc (hmemV z)) (hsrc (hmemV z')) h1)
  have hball : ∀ y : V k, ((φ k (ψ i) hi y : W k (f (ψ i))) : (X.obj (f (ψ i))).M) ∈
      riemannianClosedBallOf (X.obj (f (ψ i))).metric (X.obj (f (ψ i))).basepoint
        ((k + 2 : ℕ) : ℝ) := by
    intro y
    rw [hφF]
    have h1 := himg ⟨y, hmemV y, rfl⟩
    have hb : F.map (ψ i) P.basepoint = (X.obj (f (ψ i))).basepoint := F.basepoint_map (ψ i)
    rw [hb] at h1
    exact riemannianClosedBallOf_mono _ _ (by push_cast; linarith) h1
  have hZ : ∀ x ∈ u, ∀ q : ℕ, q ≤ p → metricDerivNorm q (P.metric.restrictOpen (V k))
      (localPullMetric (h k (f (ψ i)) 0) (φ k (ψ i) hi) (hφ k (ψ i) hi))
      (localPullMetric (h k (f (ψ i)) 0) (φ k (ψ i) hi) (hφ k (ψ i) hi)) x ≤ 1 / 2 := by
    intro x hx q hq
    have h1 := hsw x (subset_closure hx) q hq
    simpa only [dite_eq_left hi] using h1
  have hS2 : metricDerivNormSupOn K p
      (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
      ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η / 2 := by
    have h1 := hj₁ i hij₁
    simpa only [dite_eq_left hi] using h1
  set σi := σ (f (ψ i)) with hσi_def
  set A := localPullMetric (h k (f (ψ i)) σi) (φ k (ψ i) hi) (hφ k (ψ i) hi) with hA_def
  set B := localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi) with hB_def
  set Z := localPullMetric (h k (f (ψ i)) 0) (φ k (ψ i) hi) (hφ k (ψ i) hi) with hZ_def
  set g₁ := P.metric.restrictOpen (V k) with hg₁_def
  have hequiv : ∀ x ∈ u, ∀ v : TangentSpace I3 x,
      (1 + 1 : ℝ)⁻¹ * Z.inner x v v ≤ g₁.inner x v v ∧
        g₁.inner x v v ≤ (1 + 1) * Z.inner x v v := by
    intro x hx v
    have hb := Geometry.Metric.inner_bounds_of_metricDerivNorm_le Z g₁ x
      (hZ x hx 0 (Nat.zero_le _)) v
    have hnn : 0 ≤ Z.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (Z.pos x v hv).le
    norm_num
    constructor <;> linarith [hb.1, hb.2]
  have hcov : ∀ x ∈ u, ∀ q : ℕ, 1 ≤ q → q ≤ p → metricCovDerivNorm q g₁ Z x ≤ 1 := by
    intro x hx q hq1 hqp
    obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le' hq1
    rw [← metricDerivNorm_succ_self_reference]
    linarith [hZ x hx _ hqp]
  have hlipK : ∀ r : ℕ, r ≤ p → metricDerivNormSupOn K r A B Z ≤ L' * |σi - s| := by
    intro r hr
    refine metricDerivNormSupOn_le_of_forall K r _ _ _ _ (by positivity) fun a ha x _ => ?_
    rw [metricDerivNorm_localPullMetric_of_injective _ _ _ _ hinj]
    exact (hLi σi hσI s hsk _ (hball x) a (ha.trans hr)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hswapK := metricDerivNormSupOn_le_of_reference_swap_of_covDerivNorm hK hu hKu A B g₁ Z p
    zero_le_one le_rfl (by positivity : 0 ≤ L' * |σi - s|) hequiv hcov hlipK
  have hS2nn : 0 ≤ metricDerivNormSupOn K p B ((G s).restrictOpen (V k)) g₁ :=
    Real.sSup_nonneg fun r ⟨a, _, x, _, hr⟩ => hr ▸ Real.sqrt_nonneg _
  have hsmall : Λ * (L' * |σi - s|) < η / 2 := by
    have hlt : |σi - s| < η / (2 * (Λ * L' + 1)) := hσd.trans_le (min_le_right _ _)
    have hpos : 0 < 2 * (Λ * L' + 1) := by positivity
    rw [lt_div_iff₀ hpos] at hlt
    have h1 := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one : Λ * L' ≤ Λ * L' + 1) (abs_nonneg (σi - s))
    nlinarith
  refine lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ _
    (Λ * (L' * |σi - s|) + metricDerivNormSupOn K p B ((G s).restrictOpen (V k)) g₁)
    (by positivity) fun a ha x hx => ?_) (by linarith)
  exact (metricDerivNorm_triangle a A B _ g₁ x).trans (add_le_add
    ((derivNorm_le_sup hK ha A B g₁ hx).trans hswapK) (derivNorm_le_sup hK ha B _ g₁ hx))

theorem curvatureOperator_nonnegative_of_local_pinching_limit_on_window
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M} {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)}
    {f : ℕ → ℕ} (hf : StrictMono f) {V : ℕ → Opens P.M} (hV : Monotone V)
    (hcover : ∀ x : P.M, ∃ k, x ∈ V k) {N : ℕ → ℕ}
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    {T : ℝ} {c : ℕ → ℝ} (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x))) :
    ∀ t ∈ Ioc (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone := by
  intro t ht x
  obtain ⟨k, hxk⟩ := hcover x
  obtain ⟨l, hl⟩ := hcT t ht
  set n := max k l
  have hxn : x ∈ V n := hV (le_max_left k l) hxk
  have htn : t ∈ Icc (-c n) 0 :=
    ⟨(neg_le_neg (hcmono (le_max_right k l))).trans hl.le, ht.2⟩
  let _ : SigmaCompactSpace (V n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (V n).isOpen)
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N n))).and
      ((hQ.comp hfψ).eventually (eventually_gt_atTop (0 : ℝ))))
  let seq : ℕ → SmoothRiemannianMetric I3 (V n) := fun i =>
    localPullMetric (h n (f (ψ (i + i0))) t) (φ n (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      (hφ n (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
  have hconvU : MetricCInfConvergenceOnCompacts seq ((G t).restrictOpen (V n))
      (P.metric.restrictOpen (V n)) := by
    intro K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconv n K hK p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ (i + i0) (by omega)
    exact hb t htn
  have hpinchU : ∀ᶠ i in atTop, ∀ y : V n,
      curvatureOperatorLowerBoundAt (seq i) y (metricAlgebraicCurvatureTensorAt (seq i) y)
        (rescalePinchingFunction (Q (f (ψ (i + i0)))) Phi (metricScalarAt (seq i) y)) := by
    filter_upwards [(hfψ.comp (tendsto_add_atTop_nat i0)).eventually (hpinch n)] with i hi y
    have h1 := hi t htn (φ n (ψ (i + i0)) (hi0 (i + i0) (by omega)).1 y)
    rw [curvatureOperatorLowerBoundAt_localPullMetric_iff, metricScalarAt_localPull]
    exact h1
  have hnonneg := curvatureOperator_nonnegative_of_metricCInf_admissible_pinching seq
    ((G t).restrictOpen (V n)) (P.metric.restrictOpen (V n)) hconvU hPhi
    (fun i => Q (f (ψ (i + i0)))) (fun i => (hi0 (i + i0) (by omega)).2)
    ((hQ.comp hfψ).comp (tendsto_add_atTop_nat i0)) hpinchU ⟨x, hxn⟩
  exact (metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
    (G t) (V n) ⟨x, hxn⟩).mp hnonneg

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
