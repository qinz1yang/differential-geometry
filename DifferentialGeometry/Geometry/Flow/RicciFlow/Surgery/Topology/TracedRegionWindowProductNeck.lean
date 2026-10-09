import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalFlowLimitWindowTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPullProductNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedProductLimitNeck
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Comparison.Finiteness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.riemannianBallOf_scaleMetric_eq
  ObservedHistory.mem_Icc_of_mem_window from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

open private metricDerivNorm_localPullMetric_of_injective from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitShiftedTransfer

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness SpatialCanonicalAlternative
  eventually_metricDerivNorm_swap_le)

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem exists_subset_riemannianClosedBallOf_of_isCompact {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g g' : SmoothRiemannianMetric ThreeModel M) (x : M) {K : Set M} (hK : IsCompact K)
    {D : ℝ} (hKD : K ⊆ riemannianClosedBallOf g' x D) :
    ∃ D' : ℝ, 0 ≤ D' ∧ K ⊆ riemannianClosedBallOf g x D' := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, le_rfl, by rw [hKe]; exact empty_subset _⟩
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hKne
    (Geometry.Riemannian.continuous_riemannianEDist g x).continuousOn
  have hfin : riemannianEDistOf g x w₀ ≠ ⊤ := by
    rw [riemannianEDistOf_ne_top_iff g g' x w₀]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKD hw₀)
  refine ⟨(riemannianEDistOf g x w₀).toReal, ENNReal.toReal_nonneg, fun w hw => ?_⟩
  change riemannianEDistOf g x w ≤ ENNReal.ofReal (riemannianEDistOf g x w₀).toReal
  rw [ENNReal.ofReal_toReal hfin]
  exact hmax hw

private theorem tendsto_localPull_shifted_of_subseq
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {c : ℕ → ℝ} {G : ℝ → SmoothRiemannianMetric ThreeModel P.M} (hG0 : G 0 = P.metric)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
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
    {s : ℝ} (hs : s ≤ 0) {τ : ℕ → ℕ} (hτ : StrictMono τ) {σ : ℕ → ℝ}
    (hσ : Tendsto σ atTop (𝓝 s)) (hσ0 : ∀ m, σ m ≤ 0)
    (k : ℕ) (hk : -c k < s) (K : Set (V k)) (hK : IsCompact K) (p : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ hi : N k ≤ ψ (τ m),
      σ m ∈ Icc (-c k) 0 ∧
      metricDerivNormSupOn K p
        (localPullMetric (h k (f (ψ (τ m))) (σ m)) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi))
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
  have hψτ : Tendsto (fun m => ψ (τ m)) atTop atTop := (hψ.comp hτ).tendsto_atTop
  have hfψτ : Tendsto (fun m => f (ψ (τ m))) atTop atTop := (hf.comp (hψ.comp hτ)).tendsto_atTop
  set δ' := min (s + c k) (η / (2 * (Λ * L' + 1))) with hδ'_def
  have hδ' : 0 < δ' := lt_min (by linarith) (by positivity)
  have hσlim := Metric.tendsto_nhds.mp hσ δ' hδ'
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp
    ((hψτ.eventually (eventually_ge_atTop (N k))).and
      ((hψτ.eventually himage).and ((hfψτ.eventually hL).and
        ((hτ.tendsto_atTop.eventually hswap).and
          ((hτ.tendsto_atTop.eventually (eventually_ge_atTop j₁)).and hσlim)))))
  refine ⟨m₀, fun m hmm => ?_⟩
  obtain ⟨hi, ⟨hsrc, himg⟩, hLi, hsw, hij₁, hσi⟩ := hm₀ m hmm
  have hσd : |σ m - s| < δ' := by
    have h1 := hσi
    rwa [Real.dist_eq] at h1
  have hσI : σ m ∈ Icc (-c k) 0 := by
    have h1 := (abs_lt.mp (hσd.trans_le (min_le_left _ _))).1
    exact ⟨by linarith, hσ0 m⟩
  refine ⟨hi, hσI, ?_⟩
  have hmemV : ∀ y : V k,
      (y : P.M) ∈ riemannianClosedBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2) := by
    intro y
    have hy : (y : P.M) ∈ (V k : Set P.M) := y.2
    rw [hV] at hy
    exact (show riemannianEDistOf P.metric P.basepoint y < _ from hy).le
  have hinj : Function.Injective (φ k (ψ (τ m)) hi) := by
    intro z z' hzz
    have h1 : F.map (ψ (τ m)) z = F.map (ψ (τ m)) z' := by
      rw [← hφF k (ψ (τ m)) hi z, ← hφF k (ψ (τ m)) hi z', hzz]
    exact Subtype.ext ((F.partialDiffeomorph (ψ (τ m))).injOn (hsrc (hmemV z))
      (hsrc (hmemV z')) h1)
  have hball : ∀ y : V k, ((φ k (ψ (τ m)) hi y : W k (f (ψ (τ m)))) : (X.obj (f (ψ (τ m)))).M) ∈
      riemannianClosedBallOf (X.obj (f (ψ (τ m)))).metric (X.obj (f (ψ (τ m)))).basepoint
        ((k + 2 : ℕ) : ℝ) := by
    intro y
    rw [hφF]
    have h1 := himg ⟨y, hmemV y, rfl⟩
    have hb : F.map (ψ (τ m)) P.basepoint = (X.obj (f (ψ (τ m)))).basepoint :=
      F.basepoint_map (ψ (τ m))
    rw [hb] at h1
    exact riemannianClosedBallOf_mono _ _ (by push_cast; linarith) h1
  have hZ : ∀ x ∈ u, ∀ q : ℕ, q ≤ p → metricDerivNorm q (P.metric.restrictOpen (V k))
      (localPullMetric (h k (f (ψ (τ m))) 0) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi))
      (localPullMetric (h k (f (ψ (τ m))) 0) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi)) x ≤ 1 / 2 := by
    intro x hx q hq
    have h1 := hsw x (subset_closure hx) q hq
    simpa only [dite_eq_left hi] using h1
  have hS2 : metricDerivNormSupOn K p
      (localPullMetric (h k (f (ψ (τ m))) s) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi))
      ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η / 2 := by
    have h1 := hj₁ (τ m) hij₁
    simpa only [dite_eq_left hi] using h1
  set σi := σ m with hσi_def
  set A := localPullMetric (h k (f (ψ (τ m))) σi) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi) with hA_def
  set B := localPullMetric (h k (f (ψ (τ m))) s) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi) with hB_def
  set Z := localPullMetric (h k (f (ψ (τ m))) 0) (φ k (ψ (τ m)) hi) (hφ k (ψ (τ m)) hi) with hZ_def
  set g₁ := P.metric.restrictOpen (V k) with hg₁_def
  have hequiv : ∀ x ∈ u, ∀ v : TangentSpace ThreeModel x,
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

private theorem depth_schedule_exists_gt {T : ℝ} (hT : 0 < T) :
    (Monotone (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) ∧
    (∀ s < T, ∃ k : ℕ, s < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) := by
  refine ⟨?_, fun s hs => ?_⟩
  · intro k l hkl
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    refine mul_le_mul_of_nonneg_right ?_ hT.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  · obtain ⟨k, hk⟩ := exists_nat_gt ((T - s)⁻¹ * T)
    refine ⟨k, ?_⟩
    have hTs : 0 < T - s := by linarith
    have hk' : (T - s)⁻¹ * T < k + 1 := by linarith
    have hk'' : T < (k + 1) * (T - s) := by
      rw [inv_mul_lt_iff₀ hTs] at hk'
      linarith
    have hpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
    push_cast
    nlinarith

theorem eventually_forall_neckAlternative_of_window_product_structure
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    {T : ℝ} (hT : 0 < T) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∀ {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)},
    (∀ k : ℕ, ∀ᶠ n in atTop,
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
      ∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
        (a : ℝ) = t n - T / R n ∧
        ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) →
            W k n → ((H n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : W k n,
              ((H n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : W k n,
              f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∀ s ∈ Icc (-T) 0,
              ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                (t n : ℝ) + s / R n ∈ (H n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / R n)) (f j)
                      (hf j))) →
    ∀ {f : ℕ → ℕ}, StrictMono f → ∀ {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
      (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F),
      (∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n) →
      MetricComplete P →
    ∀ {V : ℕ → Opens P.M},
      (∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) →
    ∀ {N : ℕ → ℕ}, (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) →
    ∀ {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
      {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)},
      (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
        F.map j z) →
    ∀ {G : ℝ → SmoothRiemannianMetric ThreeModel P.M}, G 0 = P.metric →
      (∀ s ∈ Ioc (-T) 0, RiemannianMetricComplete (G s)) →
    ∀ {ψ : ℕ → ℕ}, StrictMono ψ →
      (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
          ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
            metricDerivNormSupOn K p
              (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
              ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) →
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop,
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
        ∀ σ' ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0, ∀ z : W k n,
          (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) →
    ∀ {T' : ℝ}, 0 ≤ T' → T' < T →
    ∀ (Nf : Type u) [TopologicalSpace Nf] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Nf]
      [IsManifold (𝓡 2) ∞ Nf] [T2Space Nf] [SigmaCompactSpace Nf] [ConnectedSpace Nf]
      (hN : ℝ → SmoothRiemannianMetric (𝓡 2) Nf)
      (Phi : (Nf × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), ThreeModel⟯ P.M),
      (∀ s ∈ Icc (-T') 0, Diffeomorph.pullbackMetricCross (G s) Phi =
        (hN s).prod (euclideanMetric (E := ℝ))) →
    ∀ {ε C1 C2 : ℝ}, ε ≤ 1 / 1000 →
    ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf
          ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage (t (f (ψ i)))) (t (f (ψ i))))
          (y (f (ψ i))) (A / Real.sqrt (R (f (ψ i)))),
      ∀ v : Icc (0 : ℝ) (H (f (ψ i))).horizon, (t (f (ψ i)) : ℝ) - T' / R (f (ψ i)) ≤ v →
      ∀ hvt : v ≤ t (f (ψ i)),
      ∀ B : BackwardPointTrace (H (f (ψ i))) ((H (f (ψ i))).activeStage v)
          ((H (f (ψ i))).activeStage (t (f (ψ i)))) ((H (f (ψ i))).activeStage_mono hvt) x,
        c * R (f (ψ i)) ≤
          metricScalarAt ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage v) v)
            (B.point ((H (f (ψ i))).activeStage v) le_rfl
              ((H (f (ψ i))).activeStage_mono hvt)) →
        ∀ W : SpatialCanonicalWitness
            ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage v) v) ε C1 C2
            (B.point ((H (f (ψ i))).activeStage v) le_rfl
              ((H (f (ψ i))).activeStage_mono hvt)),
          W.capTubeHasNeckChart ε →
            ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
  intro X W h hsurv f hf P F Cd hcan hPc V hV N hVF φ hφ hφF G hG0 hcomplete ψ hψ hconv hLip T'
    hT'0 hT' Nf _ _ _ _ _ _ hN Phi hprod ε C1 C2 hε A c hA hc
  obtain ⟨hcmono, hcex⟩ := depth_schedule_exists_gt hT
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨σ, hσ, hbad⟩ := Filter.extraction_of_frequently_atTop hcon
  have hbad' : ∀ m, ∃ x ∈ riemannianBallOf
      ((H (f (ψ (σ m)))).stageMetric ((H (f (ψ (σ m)))).activeStage (t (f (ψ (σ m)))))
        (t (f (ψ (σ m))))) (y (f (ψ (σ m)))) (A / Real.sqrt (R (f (ψ (σ m))))),
      ∃ v : Icc (0 : ℝ) (H (f (ψ (σ m)))).horizon,
        (t (f (ψ (σ m))) : ℝ) - T' / R (f (ψ (σ m))) ≤ v ∧
      ∃ hvt : v ≤ t (f (ψ (σ m))),
      ∃ B : BackwardPointTrace (H (f (ψ (σ m)))) ((H (f (ψ (σ m)))).activeStage v)
          ((H (f (ψ (σ m)))).activeStage (t (f (ψ (σ m)))))
          ((H (f (ψ (σ m)))).activeStage_mono hvt) x,
        c * R (f (ψ (σ m))) ≤ metricScalarAt
          ((H (f (ψ (σ m)))).stageMetric ((H (f (ψ (σ m)))).activeStage v) v)
          (B.point ((H (f (ψ (σ m)))).activeStage v) le_rfl
            ((H (f (ψ (σ m)))).activeStage_mono hvt)) ∧
        ∃ W : SpatialCanonicalWitness
            ((H (f (ψ (σ m)))).stageMetric ((H (f (ψ (σ m)))).activeStage v) v) ε C1 C2
            (B.point ((H (f (ψ (σ m)))).activeStage v) le_rfl
              ((H (f (ψ (σ m)))).activeStage_mono hvt)),
          W.capTubeHasNeckChart ε ∧
          ∀ nk, W.alternative ≠ SpatialCanonicalAlternative.neck nk := by
    intro m
    have hm := hbad m
    push Not at hm
    exact hm
  choose x hx v hv1 hvt B hcB Wt hWt hWnot using hbad'
  let s : ℕ → ℝ := fun m => R (f (ψ (σ m))) * ((v m : ℝ) - t (f (ψ (σ m))))
  have hs : ∀ m, s m ∈ Icc (-T') 0 := by
    intro m
    have hRm := hR (f (ψ (σ m)))
    constructor
    · have h1 := hv1 m
      have h3 : -(T' / R (f (ψ (σ m)))) ≤ (v m : ℝ) - t (f (ψ (σ m))) := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hRm.le
      have h2 : R (f (ψ (σ m))) * (-(T' / R (f (ψ (σ m))))) = -T' := by field_simp
      change -T' ≤ R (f (ψ (σ m))) * ((v m : ℝ) - t (f (ψ (σ m))))
      rw [← h2]
      exact h4
    · have h5 : (v m : ℝ) ≤ t (f (ψ (σ m))) := hvt m
      exact mul_nonpos_of_nonneg_of_nonpos hRm.le (by linarith)
  obtain ⟨sl, hsl, ρ₀, hρ₀, hslim₀⟩ := isCompact_Icc.tendsto_subseq hs
  have hslT : -T < sl := by linarith [hsl.1]
  have hsl0 : sl ≤ 0 := hsl.2
  set C2' : ℝ := max C2 1 with hC2'
  have hC2'pos : 0 < C2' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set C1' : ℝ := max C1 0 with hC1'
  have hsqc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  set r : ℝ := 2 * Real.sqrt 2 * (C1' / Real.sqrt c) + 1 with hr_def
  have hr : 0 < r := by positivity
  set η : ℝ := min (1 / 8) (c / (23040 * C2')) with hη_def
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hPc' : RiemannianMetricComplete P.metric := ⟨hPc⟩
  have hGsl : RiemannianMetricComplete (G sl) := hcomplete sl ⟨hslT, hsl0⟩
  have hK₀c : IsCompact (riemannianClosedBallOf P.metric P.basepoint (2 * A + 1)) :=
    hPc'.closedEBall_isCompact _ _
  obtain ⟨D₀, hD₀, hK₀D₀⟩ := exists_subset_riemannianClosedBallOf_of_isCompact (G sl) P.metric
    P.basepoint hK₀c (subset_refl _)
  have hKbigc : IsCompact (riemannianClosedBallOf (G sl) P.basepoint (D₀ + r)) :=
    hGsl.closedEBall_isCompact _ _
  obtain ⟨D₁, hD₁, hKbigD₁⟩ := exists_subset_riemannianClosedBallOf_of_isCompact P.metric (G sl)
    P.basepoint hKbigc (subset_refl _)
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (2 * D₁ + 2 * A + 1)
  obtain ⟨k₂, hk₂⟩ := hcex (-sl) (by linarith)
  set k := max k₁ k₂ with hk_def
  have hk₁k : (k₁ : ℝ) ≤ k := by exact_mod_cast le_max_left k₁ k₂
  have hkD₁ : D₁ < ((k + 1 : ℕ) : ℝ) / 2 := by
    push_cast
    linarith
  have hkA : A ≤ ((k + 3 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hkc : -(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) < sl := by
    have h1 := hcmono (le_max_right k₁ k₂)
    simp only at h1
    linarith
  have hKbigV : riemannianClosedBallOf (G sl) P.basepoint (D₀ + r) ⊆ V k := by
    intro w hw
    rw [hV]
    exact lt_of_le_of_lt (hKbigD₁ hw) ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hkD₁)
  have hK₀Kbig : riemannianClosedBallOf P.metric P.basepoint (2 * A + 1) ⊆
      riemannianClosedBallOf (G sl) P.basepoint (D₀ + r) := fun w hw =>
    (hK₀D₀ hw).trans (ENNReal.ofReal_le_ofReal (by linarith))
  set Kbig' : Set (V k) :=
    Subtype.val ⁻¹' riemannianClosedBallOf (G sl) P.basepoint (D₀ + r) with hKbig'
  have hKbig'c : IsCompact Kbig' := by
    apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
    have heq : (Subtype.val : V k → P.M) '' Kbig' =
        riemannianClosedBallOf (G sl) P.basepoint (D₀ + r) := by
      rw [image_preimage_eq_of_subset]
      intro w hw
      exact ⟨⟨w, hKbigV hw⟩, rfl⟩
    rwa [heq]
  have hconvLarge : metricSourceConvergesOn F
      (CanonicalMetricCompactness.canonicalSourceData F)
      (riemannianClosedBallOf P.metric P.basepoint (2 * A + 1)) 0 := by
    intro ε' hε'
    obtain ⟨k', hk'⟩ := Cd.converges _ hK₀c 0 ε' hε'
    refine ⟨k', fun j hj => ?_⟩
    have hh := hk' j hj
    rw [hcan j] at hh
    exact hh
  have hcapture := pointed_metric_eventually_inverse_ball_capture (Φ := F) P.basepoint
    (R := 2 * A + 1) (r := A) (factor := 2) hA.le (by norm_num) (by linarith) hK₀c hconvLarge
  obtain ⟨m₂, hm₂⟩ := eventually_atTop.mp
    ((hψ.comp (hσ.comp hρ₀)).tendsto_atTop.eventually (eventually_ge_atTop (N k)))
  let ρ : ℕ → ℕ := fun m => ρ₀ (m + m₂)
  have hρ : StrictMono ρ := hρ₀.comp (strictMono_id.add_const m₂)
  have hslim : Tendsto (s ∘ ρ) atTop (𝓝 sl) := hslim₀.comp (tendsto_add_atTop_nat m₂)
  have hmN : ∀ m, N k ≤ ψ (σ (ρ m)) := fun m => hm₂ (m + m₂) (Nat.le_add_left _ _)
  have hτ : StrictMono (σ ∘ ρ) := hσ.comp hρ
  have hs0 : ∀ m, (s ∘ ρ) m ≤ 0 := fun m => (hs (ρ m)).2
  let seq : ℕ → SmoothRiemannianMetric ThreeModel (V k) := fun m =>
    localPullMetric (h k (f (ψ (σ (ρ m)))) (s (ρ m))) (φ k (ψ (σ (ρ m))) (hmN m))
      (hφ k (ψ (σ (ρ m))) (hmN m))
  have hseqconv : MetricCInfConvergenceOnCompacts seq ((G sl).restrictOpen (V k))
      (P.metric.restrictOpen (V k)) := by
    intro K' hK' p η' hη'
    obtain ⟨m₀, hm₀⟩ := tendsto_localPull_shifted_of_subseq hf F Cd hcan hPc hV hφF
      (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) hG0 hψ hconv hLip hsl0 hτ
      (σ := s ∘ ρ) hslim hs0 k hkc K' hK' p hη'
    refine ⟨m₀, fun m hm => ?_⟩
    obtain ⟨hi, -, hb⟩ := hm₀ m hm
    exact hb
  have hseqconv' := hseqconv.change_reference ((G sl).restrictOpen (V k))
  obtain ⟨m₁, hm₁⟩ := hseqconv' Kbig' hKbig'c 2 η hη
  have hψτ : Tendsto (fun m => ψ (σ (ρ m))) atTop atTop := (hψ.comp hτ).tendsto_atTop
  have hfψτ : Tendsto (fun m => f (ψ (σ (ρ m)))) atTop atTop :=
    (hf.comp (hψ.comp hτ)).tendsto_atTop
  obtain ⟨m, hmsurv, hmcap, hm1⟩ := ((hfψτ.eventually (hsurv k)).and
    ((hψτ.eventually hcapture).and (eventually_ge_atTop m₁))).exists
  have hmN' := hmN m
  obtain ⟨hWset, a, hat, ha, fs, hfs, hinj, hcross, hlast, hp⟩ := hmsurv
  obtain ⟨-, hcap⟩ := hmcap
  have hRn := hR (f (ψ (σ (ρ m))))
  have hsqR : 0 < Real.sqrt (R (f (ψ (σ (ρ m))))) := Real.sqrt_pos.mpr hRn
  have hxA : x (ρ m) ∈ riemannianClosedBallOf (X.obj (f (ψ (σ (ρ m))))).metric
      (F.map (ψ (σ (ρ m))) P.basepoint) A := by
    have hb : F.map (ψ (σ (ρ m))) P.basepoint = (X.obj (f (ψ (σ (ρ m))))).basepoint :=
      F.basepoint_map _
    rw [hb]
    change riemannianEDistOf (scaleMetric (R (f (ψ (σ (ρ m))))) (hR _) _) (y _) (x (ρ m)) ≤
      ENNReal.ofReal A
    rw [edistOf_scale]
    calc ENNReal.ofReal (Real.sqrt (R (f (ψ (σ (ρ m)))))) *
          riemannianEDistOf _ (y (f (ψ (σ (ρ m))))) (x (ρ m))
        ≤ ENNReal.ofReal (Real.sqrt (R (f (ψ (σ (ρ m)))))) *
          ENNReal.ofReal (A / Real.sqrt (R (f (ψ (σ (ρ m)))))) := by
          gcongr
          exact (hx (ρ m)).le
      _ = ENNReal.ofReal A := by
          rw [← ENNReal.ofReal_mul hsqR.le, mul_div_cancel₀ _ hsqR.ne']
  obtain ⟨-, hzsrc, hz2A, hzmap⟩ := hcap _ hxA
  set z : P.M := (F.partialDiffeomorph (ψ (σ (ρ m)))).symm (x (ρ m)) with hz_def
  have hzK₀ : z ∈ riemannianClosedBallOf P.metric P.basepoint (2 * A + 1) :=
    riemannianClosedBallOf_mono _ _ (by linarith) hz2A
  have hzKbig : z ∈ riemannianClosedBallOf (G sl) P.basepoint (D₀ + r) := hK₀Kbig hzK₀
  have hzD₀ : z ∈ riemannianClosedBallOf (G sl) P.basepoint D₀ := hK₀D₀ hzK₀
  have hzV : z ∈ V k := hKbigV hzKbig
  let zV : V k := ⟨z, hzV⟩
  have hφz : ((φ k (ψ (σ (ρ m))) hmN' zV : W k (f (ψ (σ (ρ m))))) : (X.obj _).M) = x (ρ m) := by
    rw [hφF]
    exact hzmap
  have hmemV : ∀ w : V k, (w : P.M) ∈ (V k : Set P.M) := fun w => w.2
  have hφinj : Function.Injective (φ k (ψ (σ (ρ m))) hmN') := by
    intro w w' hww
    have h1 : F.map (ψ (σ (ρ m))) w = F.map (ψ (σ (ρ m))) w' := by
      rw [← hφF k (ψ (σ (ρ m))) hmN' w, ← hφF k (ψ (σ (ρ m))) hmN' w', hww]
    exact Subtype.ext ((F.partialDiffeomorph (ψ (σ (ρ m)))).injOn
      (hVF k (ψ (σ (ρ m))) hmN' (hmemV w)) (hVF k (ψ (σ (ρ m))) hmN' (hmemV w')) h1)
  set xW : W k (f (ψ (σ (ρ m)))) := φ k (ψ (σ (ρ m))) hmN' zV with hxW
  have hav : a ≤ v (ρ m) := by
    change (a : ℝ) ≤ v (ρ m)
    rw [ha]
    have h1 := hv1 (ρ m)
    have h2 : T' / R (f (ψ (σ (ρ m)))) ≤ T / R (f (ψ (σ (ρ m)))) :=
      div_le_div_of_nonneg_right hT'.le hRn.le
    linarith
  let j : (H (f (ψ (σ (ρ m))))).StageInterval ((H (f (ψ (σ (ρ m))))).activeStage a)
      ((H (f (ψ (σ (ρ m))))).activeStage (t (f (ψ (σ (ρ m)))))) :=
    ⟨(H (f (ψ (σ (ρ m))))).activeStage (v (ρ m)), (H (f (ψ (σ (ρ m))))).activeStage_mono hav,
      (H (f (ψ (σ (ρ m))))).activeStage_mono (hvt (ρ m))⟩
  let B' : BackwardPointTrace (H (f (ψ (σ (ρ m))))) ((H (f (ψ (σ (ρ m))))).activeStage a)
      ((H (f (ψ (σ (ρ m))))).activeStage (t (f (ψ (σ (ρ m))))))
      ((H (f (ψ (σ (ρ m))))).activeStage_mono hat) (x (ρ m)) :=
    { point := fun j' hf' hl => fs ⟨j', hf', hl⟩ xW
      endpoint_eq := (hlast xW).trans hφz
      crossing := fun i hf' hl => hcross i hf' hl xW }
  have hBB : B (ρ m) = B'.restrictFirst ((H (f (ψ (σ (ρ m))))).activeStage_mono hav)
      ((H (f (ψ (σ (ρ m))))).activeStage_mono (hvt (ρ m))) := Subsingleton.elim _ _
  have hpt : (B (ρ m)).point ((H (f (ψ (σ (ρ m))))).activeStage (v (ρ m))) le_rfl
      ((H (f (ψ (σ (ρ m))))).activeStage_mono (hvt (ρ m))) = fs j xW := by
    rw [hBB]
    rfl
  have hcB₀ := hcB (ρ m)
  rw [hpt] at hcB₀
  set gv := (H (f (ψ (σ (ρ m))))).stageMetric ((H (f (ψ (σ (ρ m))))).activeStage (v (ρ m)))
    (v (ρ m)) with hgv
  set gs := scaleMetric (R (f (ψ (σ (ρ m))))) hRn gv with hgs
  have hkey : ∀ W₀ : SpatialCanonicalWitness gv ε C1 C2 (fs j xW),
      W₀.capTubeHasNeckChart ε →
      (∀ nk, W₀.alternative ≠ SpatialCanonicalAlternative.neck nk) → False := by
    intro W₀ hW₀ hWnot₀
    let Fm : V k → ((H (f (ψ (σ (ρ m))))).stage j.val).Carrier := fs j ∘ φ k (ψ (σ (ρ m))) hmN'
    have hFm : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Fm :=
      isLocalDiffeomorph_comp (hfs j) (hφ k (ψ (σ (ρ m))) hmN')
    have hFminj : Function.Injective Fm := (hinj j).comp hφinj
    have hsT : s (ρ m) ∈ Icc (-T) 0 := ⟨by linarith [(hs (ρ m)).1], (hs (ρ m)).2⟩
    have hvs : (t (f (ψ (σ (ρ m)))) : ℝ) + s (ρ m) / R (f (ψ (σ (ρ m)))) = v (ρ m) := by
      simp only [s]
      field_simp
      ring
    have hdom : (t (f (ψ (σ (ρ m)))) : ℝ) + s (ρ m) / R (f (ψ (σ (ρ m)))) ∈
        (H (f (ψ (σ (ρ m))))).stageDomain j.val := by
      rw [hvs]
      exact (H (f (ψ (σ (ρ m))))).activeStage_mem (v (ρ m))
    have hp' := hp (s (ρ m)) hsT j hdom
    rw [hvs] at hp'
    have hpull : localPullMetric (h k (f (ψ (σ (ρ m)))) (s (ρ m))) (φ k (ψ (σ (ρ m))) hmN')
        (hφ k (ψ (σ (ρ m))) hmN') = localPullMetric gs Fm hFm := by
      rw [hp', ← localPullMetric_scaleMetric, localPullMetric_comp _ _ _ _ _ hFm]
    have hbound := hm₁ m hm1
    have hseqm : seq m = localPullMetric gs Fm hFm := hpull
    rw [hseqm] at hbound
    have hsub : riemannianClosedBallOf (G sl) z r ⊆ V k := by
      intro w hw
      apply hKbigV
      change riemannianEDistOf (G sl) P.basepoint w ≤ ENNReal.ofReal (D₀ + r)
      calc riemannianEDistOf (G sl) P.basepoint w
          ≤ riemannianEDistOf (G sl) P.basepoint z + riemannianEDistOf (G sl) z w :=
            riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal D₀ + ENNReal.ofReal r := add_le_add hzD₀ hw
        _ = ENNReal.ofReal (D₀ + r) := (ENNReal.ofReal_add hD₀ hr.le).symm
    have hclose : ∀ w : V k, w.val ∈ riemannianClosedBallOf (G sl) z r → ∀ m' : ℕ, m' ≤ 2 →
        metricDerivNorm m' (localPullMetric gs Fm hFm) ((G sl).restrictOpen (V k))
          ((G sl).restrictOpen (V k)) w ≤ η := by
      intro w hw m' hm'
      have hwK : w ∈ Kbig' := by
        change w.val ∈ riemannianClosedBallOf (G sl) P.basepoint (D₀ + r)
        calc riemannianEDistOf (G sl) P.basepoint w.val
            ≤ riemannianEDistOf (G sl) P.basepoint z + riemannianEDistOf (G sl) z w.val :=
              riemannianEDistOf_triangle _ _ _ _
          _ ≤ ENNReal.ofReal D₀ + ENNReal.ofReal r := add_le_add hzD₀ hw
          _ = ENNReal.ofReal (D₀ + r) := (ENNReal.ofReal_add hD₀ hr.le).symm
      exact (derivNorm_le_sup hKbig'c hm' _ _ _ hwK).trans hbound.le
    have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
    have hC2eq : C2' = C2 := max_eq_left hC2
    have hRs : metricScalarAt gs (Fm zV) =
        (R (f (ψ (σ (ρ m)))))⁻¹ * metricScalarAt gv (fs j xW) := by
      rw [hgs, metricScalarAt_scaleMetric]
      rfl
    have hRsc : c ≤ metricScalarAt gs (Fm zV) := by
      rw [hRs]
      have h1 : (R (f (ψ (σ (ρ m)))))⁻¹ * (c * R (f (ψ (σ (ρ m))))) = c := by
        field_simp
      rw [← h1]
      exact mul_le_mul_of_nonneg_left hcB₀ (inv_nonneg.mpr hRn.le)
    have hRspos : 0 < metricScalarAt gs (Fm zV) := hc.trans_le hRsc
    have hsmall : 720 * η < C2⁻¹ * metricScalarAt gs (Fm zV) / 16 := by
      have h1 : 720 * η ≤ C2⁻¹ * c / 32 := by
        have hm : η ≤ c / (23040 * C2') := min_le_right _ _
        rw [hC2eq] at hm
        have heq : 720 * (c / (23040 * C2)) = C2⁻¹ * c / 32 := by
          field_simp
          ring
        linarith
      have hpos : 0 < C2⁻¹ * c := mul_pos (inv_pos.mpr (by linarith)) hc
      have h2 : C2⁻¹ * c ≤ C2⁻¹ * metricScalarAt gs (Fm zV) :=
        mul_le_mul_of_nonneg_left hRsc (inv_nonneg.mpr (by linarith))
      linarith
    have hC1 : 1 ≤ C1 := by
      have h := W₀.radius_lower.trans W₀.radius_upper
      have hsq : 0 < Real.sqrt (metricScalarAt gv (fs j xW)) :=
        Real.sqrt_pos.mpr W₀.Q_pos
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hsq] at h
      exact h
    have hC1eq : C1' = C1 := max_eq_left (by linarith)
    have hrad : 2 * Real.sqrt 2 * (C1 / Real.sqrt (metricScalarAt gs (Fm zV))) < r := by
      have h1 : C1 / Real.sqrt (metricScalarAt gs (Fm zV)) ≤ C1 / Real.sqrt c :=
        div_le_div_of_nonneg_left (by linarith) hsqc (Real.sqrt_le_sqrt hRsc)
      have h2 : 0 ≤ 2 * Real.sqrt 2 := by positivity
      rw [hr_def, hC1eq]
      nlinarith
    have hGsl' : RiemannianMetricComplete (G sl) := hGsl
    obtain ⟨neck, hneck⟩ :=
      (W₀.scaleMetric (R (f (ψ (σ (ρ m))))) hRn).exists_localNeck_of_localPull_product_close gs
        (G sl) hFm hFminj (hN sl) finrank_euclideanSpace_fin Phi (hprod sl hsl) zV hr hη8
        (hGsl'.closedEBall_isCompact z r) hsub hclose (hW₀.scaleMetric (c := R _) (hc := hRn)) hε
        hsmall hrad
    obtain ⟨nk, hnk⟩ := W₀.exists_neck_of_scaleMetric hRn ⟨neck, hneck⟩
    exact hWnot₀ nk hnk
  have hWt₀ := hWt (ρ m)
  have hWnot₀ := hWnot (ρ m)
  revert hWt₀ hWnot₀
  generalize Wt (ρ m) = W₀
  revert W₀
  rw [hpt]
  exact hkey

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
