import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitShiftedTransfer
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

universe v

private theorem exists_neck_alternatives_transfer_constants_near {alpha : ℝ} (halpha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) {C : ℝ} (hC : 1 ≤ C) {a : ℝ} (ha : 0 < a) :
    ∃ R delta ε : ℝ, 0 < R ∧ 0 < delta ∧ 0 < ε ∧ ε ≤ a / 8 ∧
      ∀ {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M),
        RiemannianMetricComplete g → ∀ (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
        {Wm : Type v} [TopologicalSpace Wm] [ChartedSpace ThreeSpace Wm] [IsManifold I3 ∞ Wm]
        [T2Space Wm] [SigmaCompactSpace Wm] (hm : SmoothRiemannianMetric I3 Wm) (φ : V → Wm)
        (hφ : IsLocalDiffeomorph I3 I3 ∞ φ), Function.Injective φ → ∀ x : V,
        metricScalarAt g (x : M) = a →
        riemannianClosedBallOf g (x : M) (2 * R) ⊆ V →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ v : TangentSpace I3 y,
          (g.restrictOpen V).inner y v v ≤ 2 * (localPullMetric hm φ hφ).inner y v v) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ r : ℕ,
          r ≤ ⌈(2 * alpha)⁻¹⌉₊ → CheegerGromovCompactness.metricDerivNorm r
            (g.restrictOpen V) (localPullMetric hm φ hφ) (localPullMetric hm φ hφ) y ≤ delta) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) →
          |metricScalarAt (g.restrictOpen V) y - metricScalarAt (localPullMetric hm φ hφ) y| <
            ε) →
        (Nonempty (SpatialNeck hm (neckModelTolerance alpha) (φ x)) ∨
          (∃ w : Wm, Nonempty (SpatialNeck hm (neckModelTolerance alpha) w) ∧
            metricScalarAt hm (φ x) ≤ C * metricScalarAt hm w ∧
            metricScalarAt hm w ≤ C * metricScalarAt hm (φ x) ∧
            riemannianEDistOf hm (φ x) w <
              ENNReal.ofReal (C / Real.sqrt (metricScalarAt hm (φ x))))) →
        Nonempty (SpatialNeck g (2 * alpha) (x : M)) ∨
          (∃ w : M, Nonempty (SpatialNeck g (2 * alpha) w) ∧
            metricScalarAt g (x : M) ≤ 4 * max C 1 * metricScalarAt g w ∧
            riemannianEDistOf g (x : M) w < ENNReal.ofReal (4 * max C 1 / Real.sqrt a)) := by
  set C' := max C 1 with hC'_def
  have hC' : 1 ≤ C' := le_max_right _ _
  have hCle : C ≤ C' := le_max_left _ _
  set r₀ := a / (2 * C') with hr₀_def
  set r₁ := 2 * C' * a with hr₁_def
  have hr₀ : 0 < r₀ := by positivity
  obtain ⟨D, δ, η, hD, hδ, hη, hNT⟩ :=
    exists_neck_transfer_of_edist_lt (r₀ := r₀) (r₁ := r₁) halpha hsmall hr₀
  set ε := min η (a / (8 * C')) with hε_def
  have hε : 0 < ε := lt_min hη (by positivity)
  have hεη : ε ≤ η := min_le_left _ _
  have hεa : ε ≤ a / (8 * C') := min_le_right _ _
  have hεa' : ε ≤ a / 8 := hεa.trans (div_le_div_of_nonneg_left ha.le (by norm_num)
    (by linarith))
  set eps := neckModelTolerance alpha with heps_def
  have heps0 : 0 < eps := neckModelTolerance_pos halpha
  set Dn := (D + 2 * eps⁻¹) / Real.sqrt r₀ with hDn_def
  have hDn : 0 ≤ Dn := by positivity
  set d := |C| / Real.sqrt (a / 2) with hd_def
  have hd : 0 ≤ d := by positivity
  set R := Real.sqrt 2 * (d + Dn + 1) with hR_def
  have hR : 0 < R := by positivity
  have hRρ : R / Real.sqrt 2 = d + Dn + 1 := by
    rw [hR_def]
    field_simp
  refine ⟨R, δ, ε, hR, hδ, hε, hεa', ?_⟩
  intro M _ _ _ _ _ g hg V _ Wm _ _ _ _ _ hm φ hφ hinj x hxa hball hquad hjet hscal halt
  have hscV : ∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) →
      |metricScalarAt (g.restrictOpen V) y - metricScalarAt (localPullMetric hm φ hφ) y| < η :=
    fun y hy => (hscal y hy).trans_le hεη
  have hxball : (x : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) := by
    change riemannianEDistOf g (x : M) (x : M) ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hax : |a - metricScalarAt hm (φ x)| < ε := by
    have := hscal x hxball
    rwa [CheegerGromovCompactness.metricScalarAt_restrictOpen, metricScalarAt_localPull,
      hxa] at this
  have hz_lo : 7 * a / 8 < metricScalarAt hm (φ x) := by linarith [(abs_lt.mp hax).2]
  have hz_hi : metricScalarAt hm (φ x) < 9 * a / 8 := by linarith [(abs_lt.mp hax).1]
  have hr0a : r₀ ≤ a / 2 := div_le_div_of_nonneg_left ha.le (by norm_num) (by linarith)
  rcases halt with hnk | ⟨v, hnkv, hzv, hvz, hdist⟩
  · obtain ⟨nk⟩ := hnk
    have hzr1 : metricScalarAt hm (φ x) ≤ r₁ := by nlinarith
    obtain ⟨w, hwz, -, hnkw⟩ := hNT g hg V hm φ hφ hinj x hR hball hquad hjet hscV nk
      (by linarith) hzr1 (d := 1) (by
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr one_pos) (by rw [hRρ]; linarith)
    left
    rw [hinj hwz] at hnkw
    exact hnkw
  · obtain ⟨nk⟩ := hnkv
    have hv0 : 0 ≤ metricScalarAt hm v :=
      (pos_of_mul_pos_right (lt_of_lt_of_le (by linarith) hzv) (by linarith)).le
    have hzC : metricScalarAt hm (φ x) ≤ C' * metricScalarAt hm v :=
      hzv.trans (mul_le_mul_of_nonneg_right hCle hv0)
    have hvr0 : r₀ ≤ metricScalarAt hm v := by
      rw [hr₀_def, div_le_iff₀ (by positivity)]
      nlinarith
    have hvr1 : metricScalarAt hm v ≤ r₁ := by
      have h1 : metricScalarAt hm v ≤ C' * metricScalarAt hm (φ x) :=
        hvz.trans (mul_le_mul_of_nonneg_right hCle (by linarith))
      rw [hr₁_def]
      nlinarith
    have hsa : Real.sqrt (a / 2) ≤ Real.sqrt (metricScalarAt hm (φ x)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsa0 : 0 < Real.sqrt (a / 2) := Real.sqrt_pos.mpr (by positivity)
    have hdist' : riemannianEDistOf hm (φ x) v < ENNReal.ofReal d := by
      refine hdist.trans_le (ENNReal.ofReal_le_ofReal ?_)
      exact (div_le_div_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left (abs_nonneg C) hsa0 hsa)
    obtain ⟨w, hwv, hwball, hnkw⟩ := hNT g hg V hm φ hφ hinj x hR hball hquad hjet hscV nk
      hvr0 hvr1 hdist' (by rw [hRρ]; linarith)
    right
    refine ⟨(w : M), hnkw, ?_, ?_⟩
    · have hwK : (w : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) :=
        riemannianClosedBallOf_mono _ _ (by linarith) hwball
      have hw_sc := hscal w hwK
      rw [CheegerGromovCompactness.metricScalarAt_restrictOpen, metricScalarAt_localPull,
        hwv] at hw_sc
      rw [hxa]
      exact le_four_mul_of_near_neck_scalars ha hC' hax hzC hw_sc hvr0 hεa
    · obtain ⟨z, hzdef⟩ : ∃ z, z = metricScalarAt hm (φ x) := ⟨_, rfl⟩
      rw [← hzdef] at hdist hsa hz_lo
      have hz0 : 0 < z := by linarith
      have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz0
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
      have hC0 : 0 < C := by linarith
      obtain ⟨rr, hrr_def⟩ : ∃ rr, rr = Real.sqrt 2 * (C / Real.sqrt z) := ⟨_, rfl⟩
      have hrr : 0 < rr := by rw [hrr_def]; exact mul_pos hs2 (div_pos hC0 hsz)
      have hdC : d = C / Real.sqrt (a / 2) := by rw [hd_def, abs_of_pos hC0]
      have hrrd : rr ≤ Real.sqrt 2 * d := by
        rw [hrr_def, hdC]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC0.le hsa0 hsa) hs2.le
      have hrrR : rr ≤ 2 * R := by
        have hRd : Real.sqrt 2 * d ≤ R := by
          have h1 : d ≤ d + Dn + 1 := by linarith
          have h2 := mul_le_mul_of_nonneg_left h1 hs2.le
          have h3 : R = Real.sqrt 2 * (d + Dn + 1) := hR_def
          linarith
        linarith
      have hsub : riemannianClosedBallOf g (x : M) rr ⊆ V :=
        (riemannianClosedBallOf_mono _ _ hrrR).trans hball
      have hcap := DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
        hm g V φ hφ hinj x hrr hs2 (RiemannianMetricComplete.closedEBall_isCompact hg (x : M) rr)
        hsub (fun y hy v' => by
          have h1 := hquad y (riemannianClosedBallOf_mono _ _ hrrR hy) v'
          rw [localPullMetric_inner] at h1
          rw [Real.sq_sqrt zero_le_two]
          exact h1)
      have hvball : v ∈ riemannianBallOf hm (φ x) (rr / Real.sqrt 2) := by
        have hrr2 : rr / Real.sqrt 2 = C / Real.sqrt z := by
          rw [hrr_def]
          field_simp
        change riemannianEDistOf hm (φ x) v < _
        rw [hrr2]
        exact hdist
      obtain ⟨w', hw', hw'v⟩ := hcap hvball
      have hww : w' = w := hinj (hw'v.trans hwv.symm)
      rw [← hww]
      refine lt_of_le_of_lt hw' ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
      have hsa' : Real.sqrt a / 2 ≤ Real.sqrt z := by
        have h4 : Real.sqrt a / 2 = Real.sqrt (a / 4) := by
          rw [Real.sqrt_div' a (by norm_num : (0 : ℝ) ≤ 4),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        rw [h4]
        exact Real.sqrt_le_sqrt (by linarith)
      have hsa1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
      have hs2lt : Real.sqrt 2 < 2 := by
        rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [hrr_def, lt_div_iff₀ hsa1]
      have h1 : C / Real.sqrt z ≤ 2 * C / Real.sqrt a := by
        rw [div_le_div_iff₀ hsz hsa1]
        have h5 := mul_le_mul_of_nonneg_left (by linarith : Real.sqrt a ≤ 2 * Real.sqrt z) hC0.le
        linarith
      have h2 : Real.sqrt 2 * (C / Real.sqrt z) * Real.sqrt a ≤
          Real.sqrt 2 * (2 * C / Real.sqrt a) * Real.sqrt a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hs2.le) hsa1.le
      have h3 : Real.sqrt 2 * (2 * C / Real.sqrt a) * Real.sqrt a = 2 * Real.sqrt 2 * C := by
        field_simp
      have h4 := mul_lt_mul_of_pos_right hs2lt hC0
      have h5 : C ≤ max C 1 := le_max_left _ _
      linarith

private theorem compactSpace_of_isCompact_isOpen_subset_target {A B : Type*}
    [TopologicalSpace A] [T2Space A] [ConnectedSpace A] [TopologicalSpace B]
    (e : OpenPartialHomeomorph A B) {Z : Set B} (hZc : IsCompact Z) (hZo : IsOpen Z)
    (hZt : Z ⊆ e.target) {x : A} (hx : x ∈ e.source) (hxZ : e x ∈ Z) : CompactSpace A := by
  have hS : e.symm '' Z = e.source ∩ e ⁻¹' Z := e.symm_image_eq_source_inter_preimage hZt
  have hcpt : IsCompact (e.symm '' Z) :=
    hZc.image_of_continuousOn (e.continuousOn_symm.mono hZt)
  have hclopen : IsClopen (e.symm '' Z) :=
    ⟨hcpt.isClosed, by rw [hS]; exact e.isOpen_inter_preimage hZo⟩
  have huniv := hclopen.eq_univ ⟨x, by rw [hS]; exact ⟨hx, hxZ⟩⟩
  exact ⟨huniv ▸ hcpt⟩

private local instance opensSigmaCompactWindow {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem neck_alternatives_of_local_flow_limit_on_window {alpha : ℝ} (halpha : 0 < alpha)
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
    (hWF : ∀ k, ∀ᶠ j in atTop, ((W k (f j) : Set (X.obj (f j)).M)) ⊆ F.target j)
    {T : ℝ} {c : ℕ → ℝ} (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {σ : ℝ → ℕ → ℝ}
    (hconvσ : ∀ s ∈ Ioc (-T) 0, ∀ k : ℕ, -c k < s → ∀ (K : Set (V k)), IsCompact K →
      ∀ p : ℕ, ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        σ s (f (ψ i)) ∈ Icc (-c k) 0 ∧
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t)) {E : ℕ → Set ℝ}
    (hσE : ∀ s ∈ Ioc (-T) 0, ∀ᶠ n in atTop, σ s n ∉ E n) {q C2 : ℝ} (hC2 : 1 ≤ C2)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      q < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        IsCompact (connectedComponent z)) :
    ∀ s ∈ Ioc (-T) 0, ∀ x : P.M, 4 * max q 1 < metricScalarAt (G s) x →
      Nonempty (SpatialNeck (G s) (2 * alpha) x) ∨
      (∃ w : P.M, Nonempty (SpatialNeck (G s) (2 * alpha) w) ∧
        metricScalarAt (G s) x ≤ 4 * max C2 1 * metricScalarAt (G s) w ∧
        riemannianEDistOf (G s) x w <
          ENNReal.ofReal (4 * max C2 1 / Real.sqrt (metricScalarAt (G s) x))) ∨
      CompactSpace P.M := by
  intro s hs x hxq
  set a := metricScalarAt (G s) x with ha_def
  set C2' := max C2 1 with hC2'_def
  have ha : 0 < a := by linarith [le_max_right q 1]
  have hqa : q < a / 4 := by linarith [le_max_left q 1]
  by_cases hcptP : CompactSpace P.M
  · exact Or.inr (Or.inr hcptP)
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hgs := hcomplete s hs
  obtain ⟨R, δ, ε, hR, hδ, hε, hεa, hcore⟩ :=
    exists_neck_alternatives_transfer_constants_near.{w} halpha hsmall hC2 ha
  have hcpt2R : IsCompact (riemannianClosedBallOf (G s) x (2 * R)) :=
    RiemannianMetricComplete.closedEBall_isCompact hgs x (2 * R)
  obtain ⟨k₁, hk₁⟩ := hcpt2R.elim_directed_cover (fun k => (V k : Set P.M))
    (fun k => (V k).isOpen) (fun z _ => mem_iUnion.mpr (hVcover z)) hVmono.directed_le
  obtain ⟨k₂, hk₂⟩ := hcT s hs
  set k := max k₁ k₂ with hk_def
  have hball_k : riemannianClosedBallOf (G s) x (2 * R) ⊆ V k :=
    hk₁.trans (hVmono (le_max_left _ _))
  have hxself : x ∈ riemannianClosedBallOf (G s) x (2 * R) := by
    change riemannianEDistOf (G s) x x ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hs_k : -c k < s := lt_of_le_of_lt (neg_le_neg (hcmono (le_max_right _ _))) hk₂
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  let seq : ℕ → SmoothRiemannianMetric I3 (V k) := fun i =>
    if hi : N k ≤ ψ i then
      localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G s).restrictOpen (V k)
  have hseq_eq : ∀ i (hi : N k ≤ ψ i),
      seq i = localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi) :=
    fun i hi => dite_eq_left hi
  have hconvk : MetricCInfConvergenceOnCompacts seq
      ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
    intro K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconvσ s hs k hs_k K hK p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', -, hb⟩ := hj₀ i hi
    rw [hseq_eq i hi']
    exact hb
  have hσI : ∀ᶠ i in atTop, σ s (f (ψ i)) ∈ Icc (-c k) 0 := by
    obtain ⟨j₀, hj₀⟩ := hconvσ s hs k hs_k ∅ isCompact_empty 0 1 one_pos
    exact eventually_atTop.mpr ⟨j₀, fun i hi => (hj₀ i hi).choose_spec.1⟩
  have hinj : ∀ j (hj : N k ≤ j), Function.Injective (φ k j hj) := by
    intro j hj z z' hzz
    have h1 : F.map j z = F.map j z' := by
      rw [← hφF k j hj z, ← hφF k j hj z', hzz]
    exact Subtype.ext ((F.partialDiffeomorph j).injOn (hVF k j hj z.2) (hVF k j hj z'.2) h1)
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  set xk : V k := ⟨x, hball_k hxself⟩ with hxk_def
  let Kbig : Set (V k) := Subtype.val ⁻¹' riemannianClosedBallOf (G s) x (2 * R)
  have hKbig : IsCompact Kbig := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' Kbig = riemannianClosedBallOf (G s) x (2 * R) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hball_k hz⟩, hz, rfl⟩
    rw [himg]
    exact hcpt2R
  have hunif := (hconvk Kbig hKbig 2).tendstoUniformlyOn_metricScalarAt hKbig
  have hquad := (hconvk Kbig hKbig 0).eventually_quadratic_bounds hKbig
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hjet := eventually_metricDerivNorm_swap_le hconvk hKbig
    ⌈(2 * alpha)⁻¹⌉₊ hδ
  have hkr : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  have himage := F.eventually_image_closed_ball_subset Cd href hPc P.basepoint hkr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hxball : x ∈ riemannianClosedBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2) := by
    have hx' : x ∈ (V k : Set P.M) := xk.2
    rw [hV] at hx'
    exact (show riemannianEDistOf P.metric P.basepoint x < _ from hx').le
  have hEv := (hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
    ((hfψ.eventually ((hW k).and (hσE s hs))).and (hσI.and
      ((hψ.tendsto_atTop.eventually himage).and
        ((hψ.tendsto_atTop.eventually (hWF k)).and
          ((Metric.tendstoUniformlyOn_iff.mp hunif ε hε).and (hquad.and hjet))))))
  obtain ⟨i, hi, ⟨hWi, hsE⟩, hσIi, himg, hWFi, hsc, hq2, hj⟩ := hEv.exists
  have hseq := hseq_eq i hi
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
  rcases hWi (σ s (f (ψ i))) hσIi hsE _ hzball hzq with h1 | h2 | hZ
  rotate_left 2
  · refine (hcptP ?_).elim
    have : LocallyConnectedSpace (W k (f (ψ i))) :=
      ChartedSpace.locallyConnectedSpace ThreeSpace _
    let e := (F.partialDiffeomorph (ψ i)).toOpenPartialHomeomorph
    have hZo : IsOpen (Subtype.val '' connectedComponent (φ k (ψ i) hi xk) :
        Set (X.obj (f (ψ i))).M) :=
      (W k (f (ψ i))).isOpen.isOpenMap_subtype_val _ isOpen_connectedComponent
    refine compactSpace_of_isCompact_isOpen_subset_target e (hZ.image continuous_subtype_val)
      hZo (fun y hy => ?_) (hVF k (ψ i) hi xk.2) ?_
    · obtain ⟨y', -, rfl⟩ := hy
      exact hWFi y'.2
    · refine ⟨φ k (ψ i) hi xk, mem_connectedComponent, ?_⟩
      exact hφF k (ψ i) hi xk
  all_goals
    have hcases := hcore (G s) hgs (V k) (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi)
      (hφ k (ψ i) hi)
      (hinj (ψ i) hi) xk rfl hball_k
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
      (by first | exact Or.inl h1 | exact Or.inr h2)
    rcases hcases with h1 | ⟨w, hw, hxw, hdw⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨w, hw, hxw, hdw⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
