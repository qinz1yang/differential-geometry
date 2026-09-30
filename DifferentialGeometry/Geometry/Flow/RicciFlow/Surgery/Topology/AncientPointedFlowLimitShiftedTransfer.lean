import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Topology.Sequences.ExceptionalSetApproximation

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section ShiftedConvergence

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance opensSigmaCompactShifted {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

private theorem metricDerivNorm_localPullMetric_of_injective {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]
    (g g' g'' : SmoothRiemannianMetric I3 N) {e : M → N} (he : IsLocalDiffeomorph I3 I3 ∞ e)
    (hinj : Function.Injective e) (a : ℕ) (x : M) :
    metricDerivNorm a (localPullMetric g e he) (localPullMetric g' e he)
      (localPullMetric g'' e he) x = metricDerivNorm a g g' g'' (e x) := by
  have key : ∀ m : SmoothRiemannianMetric I3 N, localPullMetric m e he =
      Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph m e he hinj := fun m =>
    SmoothRiemannianMetric.ext_inner fun y v w => by
      rw [localPullMetric_inner, Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner]
  rw [key, key, key]
  exact Geometry.Metric.metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph g g' g'' e he
    hinj a x

theorem abs_derivWithin_scalar_le_of_local_flow_limit_of_shrinking_sliver
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    {V : ℕ → Opens P.M} (hVmono : Monotone V) (hVcover : ∀ x : P.M, ∃ k, x ∈ V k)
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      ancientTimeInterval))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    {E : ℕ → Set ℝ} {ζ : ℕ → ℝ} (hζ : Tendsto ζ atTop (𝓝 0))
    (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite) {q Ctime : ℝ}
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E n →
      ∀ z : W k n, q < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2) :
    ∀ t < 0, ∀ x : P.M, 4 * max q 1 < metricScalarAt (G t) x →
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
  obtain ⟨l, hl⟩ := exists_nat_gt (-t)
  set k := max k₁ l with hk_def
  have hxk : x ∈ V k := hVmono (le_max_left _ _) hk₁
  have hlk : (l : ℝ) ≤ k := by exact_mod_cast le_max_right k₁ l
  have htk : -((k + 1 : ℕ) : ℝ) < t := by push_cast; linarith
  set δ := min (min (1 / (8 * (K + 1) * a)) ((t + ((k + 1 : ℕ) : ℝ)) / 2)) (-t / 2)
    with hδ_def
  have hδ1 : δ ≤ 1 / (8 * (K + 1) * a) := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ (t + ((k + 1 : ℕ) : ℝ)) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ -t / 2 := min_le_right _ _
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by linarith)) (by linarith)
  let J := Icc (t - δ) (t + δ)
  have hJwin : J ⊆ Icc (-((k + 1 : ℕ) : ℝ)) 0 :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJreg : J ⊆ Ioo (-((k + 2 : ℕ) : ℝ)) 0 := fun s hs =>
    ⟨by push_cast at hδ2 ⊢; linarith [hs.1], by linarith [hs.2]⟩
  let _ : SigmaCompactSpace (V k) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (V k).isOpen)
  let xk : V k := ⟨x, hxk⟩
  let seq : ℕ → ℝ → SmoothRiemannianMetric I3 (V k) := fun i s =>
    if hi : N k ≤ ψ i then localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G s).restrictOpen (V k)
  let F : ℕ → ℝ → ℝ := fun i s => metricScalarAt (seq i s) xk
  have hlim : ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
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
  have hta : Tendsto (fun i => F i t) atTop (𝓝 a) := hlim t ⟨htk.le, ht.le⟩
  have hev : ∀ᶠ i in atTop, ∃ hi : N k ≤ ψ i,
      IsSolutionOn ({ base.metric := h k (f (ψ i)) } : SolutionOn (I := I3)
        (M := W k (f (ψ i))) (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
      (∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E (f (ψ i)) → ∀ z : W k (f (ψ i)),
        q < metricScalarAt (h k (f (ψ i)) s) z →
          |derivWithin (fun v => metricScalarAt (h k (f (ψ i)) v) z) (Iic s) s| ≤
            Ctime * metricScalarAt (h k (f (ψ i)) s) z ^ 2) ∧
      a / 2 ≤ F i t ∧ F i t ≤ 2 * a ∧ ζ (f (ψ i)) < -(t + δ) := by
    filter_upwards [hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k)),
      hfψ.eventually (hsol k), hfψ.eventually (hderiv k),
      hta.eventually (Icc_mem_nhds (by linarith : a / 2 < a) (by linarith : a < 2 * a)),
      hfψ.eventually (hζ.eventually (gt_mem_nhds (show (0 : ℝ) < -(t + δ) by linarith)))]
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
      have h1 := hs.scalarTime (K := Ioo (-((k + 2 : ℕ) : ℝ)) 0) (t := s) (hJreg hsJ)
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
    have h := hG.scalarTime (K := Iio 0) (t := t) ht (fun s hs => by
      rw [ancientTimeInterval_carrier]
      exact mem_Iic.mpr hs.le) x
    exact h.differentiableAt (Iio_mem_nhds ht)
  rw [hdiffG.derivWithin (uniqueDiffWithinAt_Iic t)]
  rw [Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)] at hnorm
  exact hnorm.trans (le_of_eq (by ring))

theorem tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz
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
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {s : ℝ} (hs : s ≤ 0) {σ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 s)) (hσs : ∀ n, σ n ≤ s)
    (k : ℕ) (hk : -((k : ℕ) : ℝ) ≤ s) (K : Set (V k)) (hK : IsCompact K) (p : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
      σ (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 ∧
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
  have hsk : s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := ⟨by push_cast at hk ⊢; linarith, hs⟩
  have h0k : (0 : ℝ) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩
  let _ : LocallyCompactSpace (V k) := ChartedSpace.locallyCompactSpace ThreeSpace (V k)
  obtain ⟨u, hu, hKu, hcl⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hconv0 := metricCInfConvergenceOnCompacts_localPull_of_local_flow_limit hconv k h0k
  rw [hG0] at hconv0
  have hswap := eventually_metricDerivNorm_swap_le hconv0 hcl p
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨j₁, hj₁⟩ := metricCInfConvergenceOnCompacts_localPull_of_local_flow_limit hconv k hsk
    K hK p (η / 2) (by positivity)
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  have hkr : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  have himage := F.eventually_image_closed_ball_subset Cd href hPc P.basepoint hkr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  set δ' := min 1 (η / (2 * (Λ * L' + 1))) with hδ'_def
  have hδ' : 0 < δ' := lt_min one_pos (by positivity)
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
  have hσI : σ (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := by
    have h1 := (abs_lt.mp (hσd.trans_le (min_le_left _ _))).1
    exact ⟨by push_cast at hk ⊢; linarith, (hσs _).trans hs⟩
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

theorem neck_alternatives_of_local_flow_limit_at_shifted_times {alpha : ℝ} (halpha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11)
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {σ : ℝ → ℕ → ℝ}
    (hconvσ : ∀ s ≤ 0, ∀ k : ℕ, -((k : ℕ) : ℝ) ≤ s → ∀ (K : Set (V k)), IsCompact K →
      ∀ p : ℕ, ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        σ s (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 ∧
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hcomplete : ∀ t ≤ 0, RiemannianMetricComplete (G t)) {E : ℕ → Set ℝ}
    (hσE : ∀ s ≤ 0, ∀ᶠ n in atTop, σ s n ∉ E n) {q C2 : ℝ} (hC2 : 1 ≤ C2)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      q < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        ∀ y ∈ connectedComponent z, metricScalarAt (h k n s) y ≤ C2 * metricScalarAt (h k n s) z) :
    ∀ s ≤ 0, ∀ x : P.M, 4 * max q 1 < metricScalarAt (G s) x →
      Nonempty (SpatialNeck (G s) (2 * alpha) x) ∨
      (∃ w : P.M, Nonempty (SpatialNeck (G s) (2 * alpha) w) ∧
        metricScalarAt (G s) x ≤ 4 * max C2 1 * metricScalarAt (G s) w) ∨
      ∀ y : P.M, metricScalarAt (G s) y ≤ 4 * max C2 1 * metricScalarAt (G s) x := by
  intro s hs x hxq
  set a := metricScalarAt (G s) x with ha_def
  set C2' := max C2 1 with hC2'_def
  have hC2' : 1 ≤ C2' := le_max_right _ _
  have hC2le : C2 ≤ C2' := le_max_left _ _
  have ha : 0 < a := by linarith [le_max_right q 1]
  have hqa : q < a / 4 := by linarith [le_max_left q 1]
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hgs := hcomplete s hs
  obtain ⟨R, δ, ε, hR, hδ, hε, hεa, hcore⟩ :=
    exists_neck_alternatives_transfer_constants.{w} halpha hsmall hC2 ha
  have hcpt2R : IsCompact (riemannianClosedBallOf (G s) x (2 * R)) :=
    RiemannianMetricComplete.closedEBall_isCompact hgs x (2 * R)
  obtain ⟨k₁, hk₁⟩ := hcpt2R.elim_directed_cover (fun k => (V k : Set P.M))
    (fun k => (V k).isOpen) (fun z _ => mem_iUnion.mpr (hVcover z)) hVmono.directed_le
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge (-s)
  set k₀ := max k₁ k₂ with hk₀_def
  have hball_k : ∀ k, k₀ ≤ k → riemannianClosedBallOf (G s) x (2 * R) ⊆ V k :=
    fun k hk => hk₁.trans (hVmono ((le_max_left _ _).trans hk))
  have hxself : x ∈ riemannianClosedBallOf (G s) x (2 * R) := by
    change riemannianEDistOf (G s) x x ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hxmem : ∀ k, k₀ ≤ k → x ∈ V k := fun k hk => hball_k k hk hxself
  have hs_k : ∀ k, k₀ ≤ k → -((k : ℕ) : ℝ) ≤ s := by
    intro k hk
    have : (k₂ : ℝ) ≤ k := by exact_mod_cast (le_max_right k₁ k₂).trans hk
    linarith
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  let seq : ∀ k, ℕ → SmoothRiemannianMetric I3 (V k) := fun k i =>
    if hi : N k ≤ ψ i then
      localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G s).restrictOpen (V k)
  have hseq_eq : ∀ k i (hi : N k ≤ ψ i),
      seq k i = localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi) :=
    fun k i hi => dite_eq_left hi
  have hconvk : ∀ k, k₀ ≤ k → MetricCInfConvergenceOnCompacts (seq k)
      ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
    intro k hk K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconvσ s hs k (hs_k k hk) K hK p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', -, hb⟩ := hj₀ i hi
    rw [hseq_eq k i hi']
    exact hb
  have hσI : ∀ k, k₀ ≤ k → ∀ᶠ i in atTop, σ s (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := by
    intro k hk
    obtain ⟨j₀, hj₀⟩ := hconvσ s hs k (hs_k k hk) ∅ isCompact_empty 0 1 one_pos
    exact eventually_atTop.mpr ⟨j₀, fun i hi => (hj₀ i hi).choose_spec.1⟩
  have hlimpt : ∀ k (hk : k₀ ≤ k) (y : V k), Tendsto (fun i => metricScalarAt (seq k i) y)
      atTop (𝓝 (metricScalarAt (G s) y)) := by
    intro k hk y
    have hu := ((hconvk k hk {y} isCompact_singleton 2).tendstoUniformlyOn_metricScalarAt
      isCompact_singleton).tendsto_at (mem_singleton y)
    rwa [metricScalarAt_restrictOpen] at hu
  have hinj : ∀ k j (hj : N k ≤ j), Function.Injective (φ k j hj) := by
    intro k j hj z z' hzz
    have h1 : F.map j z = F.map j z' := by
      rw [← hφF k j hj z, ← hφF k j hj z', hzz]
    exact Subtype.ext ((F.partialDiffeomorph j).injOn (hVF k j hj z.2) (hVF k j hj z'.2) h1)
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  let WholeType : ∀ k, V k → ℕ → Prop := fun k xk i => ∃ hi : N k ≤ ψ i,
    ∀ y ∈ connectedComponent xk, metricScalarAt (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi y) ≤
      C2' * metricScalarAt (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi xk)
  by_cases hwhole : ∀ k (hk : k₀ ≤ k), ∀ᶠ i in atTop, WholeType k ⟨x, hxmem k hk⟩ i
  · refine Or.inr (Or.inr fun y => ?_)
    let _ : PathConnectedSpace P.M := by
      let _ : LocallyPathConnectedSpace P.M :=
        ChartedSpace.locallyPathConnectedSpace ThreeSpace P.M
      exact pathConnectedSpace_iff_connectedSpace.mpr hconn
    obtain ⟨k, hk, hxk, hyk, hcomp⟩ :=
      exists_mem_connectedComponent_of_monotone_cover hVmono hVcover x y k₀
    have hle : metricScalarAt (G s) y ≤ C2' * a := by
      refine le_of_tendsto_of_tendsto (hlimpt k hk ⟨y, hyk⟩)
        ((hlimpt k hk ⟨x, hxk⟩).const_mul C2') ?_
      filter_upwards [hwhole k hk] with i ⟨hi, hbound⟩
      rw [hseq_eq k i hi, metricScalarAt_localPull, metricScalarAt_localPull]
      exact hbound ⟨y, hyk⟩ hcomp
    have h4 : C2' * a ≤ 4 * C2' * a := by nlinarith
    exact hle.trans h4
  push Not at hwhole
  obtain ⟨k, hk, hfreq⟩ := hwhole
  set xk : V k := ⟨x, hxmem k hk⟩ with hxk_def
  let Kbig : Set (V k) := Subtype.val ⁻¹' riemannianClosedBallOf (G s) x (2 * R)
  have hKbig : IsCompact Kbig := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' Kbig = riemannianClosedBallOf (G s) x (2 * R) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hball_k k hk hz⟩, hz, rfl⟩
    rw [himg]
    exact hcpt2R
  have hunif := (hconvk k hk Kbig hKbig 2).tendstoUniformlyOn_metricScalarAt hKbig
  have hquad := (hconvk k hk Kbig hKbig 0).eventually_quadratic_bounds hKbig
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hjet := eventually_metricDerivNorm_swap_le (hconvk k hk) hKbig ⌈(2 * alpha)⁻¹⌉₊ hδ
  have hkr : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  have himage := F.eventually_image_closed_ball_subset Cd href hPc P.basepoint hkr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hxball : x ∈ riemannianClosedBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2) := by
    have hx' : x ∈ (V k : Set P.M) := xk.2
    rw [hV] at hx'
    exact (show riemannianEDistOf P.metric P.basepoint x < _ from hx').le
  obtain ⟨i, hnot, hi, ⟨hWi, hsE⟩, hσIi, himg, hsc, hq2, hj⟩ := (hfreq.and_eventually
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hfψ.eventually ((hW k).and (hσE s hs))).and ((hσI k hk).and
        ((hψ.tendsto_atTop.eventually himage).and
          ((Metric.tendstoUniformlyOn_iff.mp hunif ε hε).and (hquad.and hjet))))))).exists
  have hseq := hseq_eq k i hi
  have hzball : ((φ k (ψ i) hi xk : W k (f (ψ i))) : (X.obj (f (ψ i))).M) ∈
      riemannianClosedBallOf (X.obj (f (ψ i))).metric (X.obj (f (ψ i))).basepoint
        ((k + 1 : ℕ) : ℝ) := by
    rw [hφF]
    have h1 := himg.2 ⟨x, hxball, rfl⟩
    have hb : F.map (ψ i) P.basepoint = (X.obj (f (ψ i))).basepoint := F.basepoint_map (ψ i)
    rw [hb] at h1
    exact riemannianClosedBallOf_mono _ _ (by linarith) h1
  have hzpos : a / 2 < metricScalarAt (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi xk) := by
    have h1 := hsc xk hxself
    rw [Real.dist_eq, hseq, metricScalarAt_localPull, metricScalarAt_restrictOpen] at h1
    have h2 := (abs_lt.mp h1).2
    have h3 : metricScalarAt (G s) x = a := rfl
    linarith
  have hzq : q < metricScalarAt (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi xk) := by linarith
  have halt := hWi (σ s (f (ψ i))) hσIi hsE _ hzball hzq
  have hcases := hcore (G s) hgs (V k) (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi)
    (hφ k (ψ i) hi)
    (hinj k (ψ i) hi) xk rfl (hball_k k hk)
    (fun y hy v => by
      have h1 := ((hq2 y hy v).1)
      rw [hseq] at h1
      linarith)
    (fun y hy r hr => by
      have h1 := hj y hy r hr
      rw [hseq] at h1
      exact h1)
    (fun y hy => by
      have h1 := hsc y hy
      rw [Real.dist_eq, hseq] at h1
      exact h1)
    halt
  rcases hcases with h1 | h2 | hdomb
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine absurd ⟨hi, fun y hy => ?_⟩ hnot
    have hy' : φ k (ψ i) hi y ∈ connectedComponent (φ k (ψ i) hi xk) :=
      ((isPreconnected_connectedComponent.image _
        (hφ k (ψ i) hi).contMDiff.continuous.continuousOn).subset_connectedComponent
          ⟨xk, mem_connectedComponent, rfl⟩) ⟨y, hy, rfl⟩
    have hz0 : 0 ≤ metricScalarAt (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi xk) := by linarith
    exact (hdomb _ hy').trans (mul_le_mul_of_nonneg_right hC2le hz0)

theorem exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ {X : PointedRiemannianSeq.{w, 0, 0} I3}
      {P : PointedRiemannianManifold.{w, 0, 0} I3} {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ}, StrictMono f →
      ∀ (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F),
      (∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n) →
      MetricComplete P → ConnectedSpace P.M → ∀ {V : ℕ → Opens P.M},
      (∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) →
      ∀ {N : ℕ → ℕ}, (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) →
      ∀ {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
        {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)},
      (∀ k j (hj : N k ≤ j) (z : V k),
        ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z) →
      ∀ {G : ℝ → SmoothRiemannianMetric I3 P.M}, G 0 = P.metric →
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) →
      ∀ {ψ : ℕ → ℕ}, StrictMono ψ →
      (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) →
      (∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
        SolutionOn (I := I3) (M := W k n)
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
            (neg_nonpos.mpr (Nat.cast_nonneg _))))) →
      ∀ {Q : ℕ → ℝ}, Tendsto Q atTop atTop → ∀ {Phi : ℝ → ℝ}, AdmissiblePinchingFunction Phi →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
          (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x))) →
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
          ∀ z : W k n, (z : (X.obj n).M) ∈
              riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
            ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) →
      ∀ {E : ℕ → Set ℝ} {ζ : ℕ → ℝ}, Tendsto ζ atTop (𝓝 0) →
      (∀ n, (E n \ Icc (-(ζ n)) 0).Finite) →
      ∀ {eps qW C2 qD Ctime : ℝ}, 0 < eps → eps ≤ epsW → 1 ≤ C2 →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n → ∀ z : W k n,
        (z : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        qW < metricScalarAt (h k n s) z →
        Nonempty (SpatialNeck (h k n s) eps z) ∨
          (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
            metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
            metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
            riemannianEDistOf (h k n s) z w <
              ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
          ∀ y ∈ connectedComponent z,
            metricScalarAt (h k n s) y ≤ C2 * metricScalarAt (h k n s) z) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E n → ∀ z : W k n,
        qD < metricScalarAt (h k n s) z →
          |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
            Ctime * metricScalarAt (h k n s) z ^ 2) →
      ∃ C : ℝ, ∀ t ≤ 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C := by
  obtain ⟨η₀, hη₀, hslice⟩ :=
    exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives.{w}
  set alpha := min (η₀ / 2) (1 / 44) with halpha_def
  have halpha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have h2α : 2 * alpha ≤ η₀ := by
    have := min_le_left (η₀ / 2) (1 / 44 : ℝ)
    linarith
  have hsmall : 2 * alpha < 1 / 11 := by
    have := min_le_right (η₀ / 2) (1 / 44 : ℝ)
    linarith
  have hnmt : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  refine ⟨neckModelTolerance alpha, neckModelTolerance_pos halpha, ?_⟩
  intro X P W h f hf F Cd hcan hPc hconn V hV N hVF φ hφ hφF G hG0 hGsol ψ hψ hconv hsol Q hQ
    Phi hPhi hpinch hLip E ζ hζ hE eps qW C2 qD Ctime heps hle hC2 hW hderiv
  obtain ⟨hcone, hcomplete⟩ :=
    ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete hf hPc hconn hV hG0
      hGsol hψ hconv hQ hPhi hpinch
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hW' : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n →
      ∀ z : W k n, (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        ∀ y ∈ connectedComponent z,
          metricScalarAt (h k n s) y ≤ C2 * metricScalarAt (h k n s) z := by
    intro k
    filter_upwards [hW k] with n hn s hs hsE z hz hq
    rcases hn s hs hsE z hz hq with hnk | ⟨w, hnk, h1⟩ | h3
    · obtain ⟨nk⟩ := hnk
      exact Or.inl ⟨nk.mono hle hnmt⟩
    · obtain ⟨nk⟩ := hnk
      exact Or.inr (Or.inl ⟨w, ⟨nk.mono hle hnmt⟩, h1⟩)
    · exact Or.inr (Or.inr h3)
  have hsel : ∀ s : ℝ, ∃ σ : ℕ → ℝ, s ≤ 0 →
      Tendsto σ atTop (𝓝 s) ∧ ∀ n, σ n ≤ s ∧ σ n ∉ E n := fun s =>
    if hs : s ≤ 0 then (exists_tendsto_forall_notMem_of_finite_diff_Icc hζ hE hs).imp
      fun _ hσ _ => hσ
    else ⟨0, fun h => absurd h hs⟩
  choose σ hσ using hsel
  have hσE : ∀ s ≤ 0, ∀ᶠ n in atTop, σ s n ∉ E n := fun s hs =>
    Eventually.of_forall fun n => ((hσ s hs).2 n).2
  have hconvσ : ∀ s ≤ 0, ∀ k : ℕ, -((k : ℕ) : ℝ) ≤ s → ∀ (K : Set (V k)), IsCompact K →
      ∀ p : ℕ, ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        σ s (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 ∧
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η :=
    fun s hs k hk K hK p η hη =>
      tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz hf F Cd hcan hPc hV hφF
        hG0 hψ hconv hLip hs (hσ s hs).1 (fun n => ((hσ s hs).2 n).1) k hk K hK p hη
  have halt := neck_alternatives_of_local_flow_limit_at_shifted_times halpha hsmall hf F Cd hcan
    hPc hconn hV hVF hφF hψ hconvσ hcomplete hσE hC2 hW'
  let _ : ConnectedSpace P.M := hconn
  have hslices : ∀ t ≤ 0, ∃ C : ℝ, ∀ x : P.M, metricScalarAt (G t) x ≤ C := fun t ht =>
    hslice (G t) (hcomplete t ht) (hcone t ht) h2α (halt t ht)
  have hder := abs_derivWithin_scalar_le_of_local_flow_limit_of_shrinking_sliver hf hVmono hVcover
    hGsol hψ hconv hsol hζ hE hderiv
  exact exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_slice_bounds hGsol
    hcomplete hcone hslices hder

end ShiftedConvergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
