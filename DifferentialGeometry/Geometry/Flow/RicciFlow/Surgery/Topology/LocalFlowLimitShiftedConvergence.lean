import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitShiftedTransfer

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private metricDerivNorm_localPullMetric_of_injective from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitShiftedTransfer

section ShiftedConvergenceAtZero

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance opensSigmaCompactShiftedAtZero {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem tendsto_metricDerivNormSupOn_localPull_shifted_to_zero_of_time_lipschitz
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
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv0 : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) 0) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          (P.metric.restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {c : ℕ → ℝ} (hc : ∀ k, 0 < c k)
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-c k) 0, ∀ σ' ∈ Icc (-c k) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {σ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) (hσs : ∀ n, σ n ≤ 0)
    (k : ℕ) (K : Set (V k)) (hK : IsCompact K) (p : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
      σ (f (ψ i)) ∈ Icc (-c k) 0 ∧
      metricDerivNormSupOn K p
        (localPullMetric (h k (f (ψ i)) (σ (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
        (P.metric.restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
  obtain ⟨L, hL⟩ := hLip k p
  set L' := max L 0 with hL'_def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  set D := metricCovariantDerivativeComparisonConstant (E := ThreeSpace) 2 p with hD_def
  have hD0 : 0 ≤ D := metric_covariant_derivative_comparison_constant_nonneg (E := ThreeSpace) 2 p
  set Λ := Real.sqrt ((1 + 1) ^ (2 + p)) * (1 + 1 * D * ((p : ℝ) + 1)) with hΛ_def
  have hΛ0 : 0 ≤ Λ := by positivity
  have h0k : (0 : ℝ) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩
  have h0c : (0 : ℝ) ∈ Icc (-c k) 0 := ⟨neg_nonpos.mpr (hc k).le, le_rfl⟩
  let _ : LocallyCompactSpace (V k) := ChartedSpace.locallyCompactSpace ThreeSpace (V k)
  obtain ⟨u, hu, hKu, hcl⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hconvC := metricCInfConvergenceOnCompacts_localPull_of_local_flow_limit
    (h := fun k n _ => h k n 0) (G := fun _ => P.metric)
    (fun k K hK p η hη => (hconv0 k K hK p η hη).imp fun _ hj i hi =>
      (hj i hi).imp fun _ hb _ _ => hb) k h0k
  have hswap := eventually_metricDerivNorm_swap_le hconvC hcl p
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨j₁, hj₁⟩ := hconvC K hK p (η / 2) (by positivity)
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  have hkr : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  have himage := F.eventually_image_closed_ball_subset Cd href hPc P.basepoint hkr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  set δ' := min (c k) (η / (2 * (Λ * L' + 1))) with hδ'_def
  have hδ' : 0 < δ' := lt_min (hc k) (by positivity)
  have hσlim := Metric.tendsto_nhds.mp (hσ.comp hfψ) δ' hδ'
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hψ.tendsto_atTop.eventually himage).and ((hfψ.eventually hL).and
        (hswap.and ((eventually_ge_atTop j₁).and hσlim)))))
  refine ⟨j₀, fun i hij => ?_⟩
  obtain ⟨hi, ⟨hsrc, himg⟩, hLi, hsw, hij₁, hσi⟩ := hj₀ i hij
  have hσd : |σ (f (ψ i))| < δ' := by
    have h1 := hσi
    rwa [Function.comp_apply, Real.dist_eq, sub_zero] at h1
  have hσI : σ (f (ψ i)) ∈ Icc (-c k) 0 := by
    have h1 := (abs_lt.mp (hσd.trans_le (min_le_left _ _))).1
    exact ⟨h1.le, hσs _⟩
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
    simpa only [dif_pos hi] using h1
  have hS2 : metricDerivNormSupOn K p
      (localPullMetric (h k (f (ψ i)) 0) (φ k (ψ i) hi) (hφ k (ψ i) hi))
      (P.metric.restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η / 2 := by
    have h1 := hj₁ i hij₁
    simpa only [dif_pos hi] using h1
  set σi := σ (f (ψ i)) with hσi_def
  set A := localPullMetric (h k (f (ψ i)) σi) (φ k (ψ i) hi) (hφ k (ψ i) hi) with hA_def
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
  have hlipK : ∀ r : ℕ, r ≤ p → metricDerivNormSupOn K r A Z Z ≤ L' * |σi - 0| := by
    intro r hr
    refine metricDerivNormSupOn_le_of_forall K r _ _ _ _ (by positivity) fun a ha x _ => ?_
    rw [metricDerivNorm_localPullMetric_of_injective _ _ _ _ hinj]
    exact (hLi σi hσI 0 h0c _ (hball x) a (ha.trans hr)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hswapK := metricDerivNormSupOn_le_of_reference_swap_of_covDerivNorm hK hu hKu A Z g₁ Z p
    zero_le_one le_rfl (by positivity : 0 ≤ L' * |σi - 0|) hequiv hcov hlipK
  have hS2nn : 0 ≤ metricDerivNormSupOn K p Z g₁ g₁ :=
    Real.sSup_nonneg fun r ⟨a, _, x, _, hr⟩ => hr ▸ Real.sqrt_nonneg _
  have hsmall : Λ * (L' * |σi - 0|) < η / 2 := by
    have hlt : |σi - 0| < η / (2 * (Λ * L' + 1)) := by
      rw [sub_zero]
      exact hσd.trans_le (min_le_right _ _)
    have hpos : 0 < 2 * (Λ * L' + 1) := by positivity
    rw [lt_div_iff₀ hpos] at hlt
    have h1 := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one : Λ * L' ≤ Λ * L' + 1) (abs_nonneg (σi - 0))
    nlinarith
  refine lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ _
    (Λ * (L' * |σi - 0|) + metricDerivNormSupOn K p Z g₁ g₁)
    (by positivity) fun a ha x hx => ?_) (by linarith)
  exact (metricDerivNorm_triangle a A Z _ g₁ x).trans (add_le_add
    ((derivNorm_le_sup hK ha A Z g₁ hx).trans hswapK) (derivNorm_le_sup hK ha Z _ g₁ hx))

end ShiftedConvergenceAtZero

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
