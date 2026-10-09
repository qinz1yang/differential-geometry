import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowScalarBoundNeckAlternatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalFlowLimitWindowTransfer
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitWindowNeckAlternatives

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_metricNoncollapsed_of_parabolic_of_curvatureOperator_nonnegative
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {T : ℝ} (hT : 0 < T)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)))
    (hG0 : G 0 = P.metric)
    (hcone : ∀ τ ∈ Ioc (-T) 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G τ) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    {q Ctime κ : ℝ} (hκ : 0 < κ)
    (hderiv : ∀ τ ∈ Ioo (-T) 0, ∀ x : P.M, q < metricScalarAt (G τ) x →
      |derivWithin (fun v => metricScalarAt (G v) x) (Iic τ) τ| ≤
        Ctime * metricScalarAt (G τ) x ^ 2)
    (hpar : Perelman.ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } :
      SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) κ 1) :
    ∃ κ' : ℝ, 0 < κ' ∧ MetricNoncollapsed P κ' (Ioc 0 1) := by
  let D := RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩
  let S : SolutionOn (I := I3) (M := P.M) D := { base.metric := G }
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  set K := max Ctime 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  set c₄ := 10 + max q 0 with hc₄def
  have hc₄ : 10 ≤ c₄ := by have := le_max_right q 0; linarith
  obtain ⟨C₀sq, hC₀def⟩ : ∃ C₀sq : ℝ, C₀sq = 200 * c₄ + 2 * (K + 1) * c₄ + 1 / T + 1 :=
    ⟨_, rfl⟩
  have hc₄0 : 0 ≤ c₄ := by linarith
  have hKc : 0 ≤ 2 * (K + 1) * c₄ := by positivity
  have hT1 : 0 < 1 / T := by positivity
  have hC₀sq : 0 < C₀sq := by rw [hC₀def]; positivity
  set C₀ := Real.sqrt C₀sq with hC₀
  have hC₀pos : 0 < C₀ := Real.sqrt_pos.mpr hC₀sq
  have hC₀sq' : C₀ ^ 2 = C₀sq := Real.sq_sqrt hC₀sq.le
  refine ⟨κ / C₀ ^ 3, by positivity, ?_⟩
  intro x r hr hr0 hbound
  have hr1 : r ≤ 1 := hr.2
  set r' := r / C₀ with hr'def
  have hr'0 : 0 < r' := div_pos hr0 hC₀pos
  have hr'sq : r' ^ 2 = r ^ 2 / C₀sq := by rw [hr'def, div_pow, hC₀sq']
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hr20 : 0 < r ^ 2 := by positivity
  set B := 9 / r ^ 2 + max q 0 + 1 with hBdef
  have hB0 : 0 < B := by positivity
  have hBc : B ≤ c₄ / r ^ 2 := by
    rw [hBdef, hc₄def, le_div_iff₀ hr20]
    have h1 : (9 / r ^ 2 + max q 0 + 1) * r ^ 2 = 9 + (max q 0 + 1) * r ^ 2 := by
      field_simp
      ring
    rw [h1]
    have h2 : (max q 0 + 1) * r ^ 2 ≤ max q 0 + 1 :=
      mul_le_of_le_one_right (by positivity) hr2
    linarith
  have hqB : q < B := by
    have := le_max_left q 0
    have : 0 ≤ 9 / r ^ 2 := by positivity
    linarith
  have hC₀ge1 : 1 ≤ C₀sq := by linarith
  have hC₀ge : 1 ≤ C₀ := by
    rw [hC₀, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hC₀ge1
  have hr'T : r' ^ 2 < T := by
    rw [hr'sq, div_lt_iff₀ hC₀sq]
    have hTC : 1 < T * C₀sq := by
      have h1 : T * C₀sq = T * (200 * c₄ + 2 * (K + 1) * c₄) + T * (1 / T) + T := by
        rw [hC₀def]
        ring
      have h2 : T * (1 / T) = 1 := by field_simp
      have h3 : 0 ≤ T * (200 * c₄ + 2 * (K + 1) * c₄) := by positivity
      linarith
    nlinarith
  have hlen : K * (0 - -r' ^ 2) ≤ 1 / (2 * B) := by
    rw [sub_neg_eq_add, zero_add, hr'sq, le_div_iff₀ (by positivity)]
    have h1 : K * (r ^ 2 / C₀sq) * (2 * B) ≤ K * (r ^ 2 / C₀sq) * (2 * (c₄ / r ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : K * (r ^ 2 / C₀sq) * (2 * (c₄ / r ^ 2)) = 2 * K * c₄ / C₀sq := by
      field_simp
    have h3 : 2 * K * c₄ ≤ C₀sq := by
      have : 2 * K * c₄ ≤ 2 * (K + 1) * c₄ := by nlinarith
      linarith
    have h4 : 2 * K * c₄ / C₀sq ≤ 1 := (div_le_one hC₀sq).mpr h3
    linarith
  have hmemD : ∀ s ∈ Icc (-r' ^ 2) 0, s ∈ Ioc (-T) 0 := fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hR0 : ∀ y ∈ riemannianBallOf P.metric x r, metricScalarAt (G 0) y ≤ 9 / r ^ 2 := by
    intro y hy
    have h1 := hbound y hy
    have h2 := scalar_abs_le_rm P.metric y
    have hdimy : (Module.finrank ℝ (TangentSpace I3 y) : ℝ) = 3 := by
      change (Module.finrank ℝ ThreeSpace : ℝ) = 3
      rw [hdim]
      norm_num
    rw [hdimy] at h2
    have h3 : Real.sqrt (Tensor0SBundle.normSq0S P.metric y 4 (metricRm04At P.metric y)) ≤
        1 / r ^ 2 := by
      rw [Real.sqrt_le_left (by positivity), div_pow, one_pow, le_div_iff₀ (by positivity)]
      calc Tensor0SBundle.normSq0S P.metric y 4 (metricRm04At P.metric y) * (r ^ 2) ^ 2
          = r ^ 4 * Tensor0SBundle.normSq0S P.metric y 4 (metricRm04At P.metric y) := by ring
        _ ≤ 1 := h1
    rw [hG0]
    have h4 := (abs_le.mp h2).2
    have h5 : (3 : ℝ) ^ 2 * (1 / r ^ 2) = 9 / r ^ 2 := by ring
    nlinarith
  have hball' : riemannianBallOf P.metric x r' ⊆ riemannianBallOf P.metric x r :=
    riemannianBallOf_mono _ _ (div_le_self hr0.le hC₀ge)
  have hRs : ∀ y ∈ riemannianBallOf P.metric x r', ∀ s ∈ Icc (-r' ^ 2) 0,
      metricScalarAt (G s) y ≤ 2 * B := by
    intro y hy
    have hcont : ContinuousOn (fun w => metricScalarAt (G w) y) (Icc (-r' ^ 2) 0) := by
      have hc : ContinuousOn (fun w : ℝ => S.scalar w y) (Ioc (-T) 0) :=
        hG.scalarCont.comp (f := fun w : ℝ => (w, y))
          (continuousOn_id.prodMk continuousOn_const) (fun w hw => ⟨hw, mem_univ y⟩)
      exact hc.mono hmemD
    have hdiffAt : ∀ v ∈ Ioo (-r' ^ 2) 0,
        DifferentiableAt ℝ (fun w => metricScalarAt (G w) y) v := by
      intro v hv
      have hv' : v ∈ Ioo (-T) 0 := ⟨by linarith [hv.1], hv.2⟩
      have h := hG.scalarTime (K := Ioo (-T) 0) (t := v) hv' (fun w hw => ⟨hw.1, hw.2.le⟩) y
      exact h.differentiableAt (Ioo_mem_nhds hv'.1 hv'.2)
    refine le_two_mul_of_abs_deriv_le_mul_sq_of_continuousOn_of_right_le hB0 hK hcont hdiffAt
      ?_ ((hR0 y (hball' hy)).trans (by linarith [le_max_right q 0])) hlen
    intro v hv hBv
    have hv' : v ∈ Ioo (-T) 0 := ⟨by linarith [hv.1], hv.2⟩
    have h := hderiv v hv' y (hqB.trans hBv)
    rw [(hdiffAt v hv).derivWithin (uniqueDiffWithinAt_Iic v)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have h0D : (0 : ℝ) ∈ D.carrier := ⟨neg_lt_zero.mpr hT, le_rfl⟩
  let B' : Perelman.FlowMetricBall S ⟨0, h0D⟩ := ⟨x, r', hr'0⟩
  have hctrl : B'.IsParabolicallyRmControlled := by
    refine ⟨fun s hs => ?_, fun s hs y hy => ?_⟩
    · change s ∈ Icc ((0 : ℝ) - r' ^ 2) 0 at hs
      exact hmemD s ⟨by linarith [hs.1], hs.2⟩
    change s ∈ Icc ((0 : ℝ) - r' ^ 2) 0 at hs
    have hs' : s ∈ Icc (-r' ^ 2) 0 := ⟨by linarith [hs.1], hs.2⟩
    have hy' : y ∈ riemannianBallOf P.metric x r' := by
      change riemannianEDistOf (G 0) x y < ENNReal.ofReal r' at hy
      rw [hG0] at hy
      exact hy
    have hRy := hRs y hy' s hs'
    have hcone' := hcone s (hmemD s hs') y
    have hnorm := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
      (G s) y hdim hcone'
    have hnn := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative (G s) y hcone'
    change r' ^ 4 * Tensor0SBundle.normSq0S (G s) y 4 (metricRm04 (G s) y) ≤ 1
    have h1 : Tensor0SBundle.normSq0S (G s) y 4 (metricRm04 (G s) y) ≤ 100 ^ 2 * (2 * B) ^ 2 :=
      hnorm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hRy 2) (by norm_num))
    have h2 : r' ^ 2 * (200 * B) ≤ 1 := by
      rw [hr'sq]
      have h3 : r ^ 2 / C₀sq * (200 * B) ≤ r ^ 2 / C₀sq * (200 * (c₄ / r ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : r ^ 2 / C₀sq * (200 * (c₄ / r ^ 2)) = 200 * c₄ / C₀sq := by field_simp
      have h5 : 200 * c₄ ≤ C₀sq := by linarith
      have h6 : 200 * c₄ / C₀sq ≤ 1 := (div_le_one hC₀sq).mpr h5
      linarith
    have hn0 : 0 ≤ Tensor0SBundle.normSq0S (G s) y 4 (metricRm04 (G s) y) :=
      Tensor0SBundle.normSq0S_nonneg _ _ _ _
    have h7 : r' ^ 4 * (100 ^ 2 * (2 * B) ^ 2) = (r' ^ 2 * (200 * B)) ^ 2 := by ring
    have h8 : (r' ^ 2 * (200 * B)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) h2
    calc r' ^ 4 * Tensor0SBundle.normSq0S (G s) y 4 (metricRm04 (G s) y)
        ≤ r' ^ 4 * (100 ^ 2 * (2 * B) ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 := by rw [h7]; exact h8
  have hr'1 : B'.radius ≤ 1 := (div_le_self hr0.le hC₀ge).trans hr1
  obtain ⟨-, hvol⟩ := hpar.2 ⟨0, h0D⟩ B' hr'1 hctrl
  have hvolB : B'.volume = Integral.Measure.riemannianVolumeMeasure I3 P.M P.metric
      (riemannianBallOf P.metric x r') := by
    simp only [Perelman.FlowMetricBall.volume, Perelman.FlowMetricBall.set,
      Perelman.FlowMetricBall.setAt, Integral.Measure.volumeMeasureOn_eq_metric,
      SolutionOn.family_metric]
    change Integral.Measure.riemannianVolumeMeasure I3 P.M (G 0)
      (riemannianBallOf (G 0) x r') = _
    rw [hG0]
  rw [hvolB, hdim] at hvol
  refine le_trans ?_ (hvol.trans (MeasureTheory.measure_mono hball'))
  change ENNReal.ofReal (κ / C₀ ^ 3 * r ^ 3) ≤ ENNReal.ofReal κ * ENNReal.ofReal (r / C₀) ^ 3
  rw [← ENNReal.ofReal_pow hr'0.le, ← ENNReal.ofReal_mul hκ.le]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [div_pow]
  field_simp

private local instance opensSigmaCompactMaximalWindow {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : TopologicalSpace.Opens Y) :
    SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem scalar_le_at_distance_of_local_flow_limit_on_window
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    {V : ℕ → TopologicalSpace.Opens P.M} (hVmono : Monotone V) (hVcover : ∀ x : P.M, ∃ k, x ∈ V k)
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hinj : ∀ k j (hj : N k ≤ j), Function.Injective (φ k j hj))
    {T : ℝ} {c : ℕ → ℝ} (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (happrox : ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ τ ∈ Icc (-c k) 0, τ < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n τ) z ≤ A →
        riemannianEDistOf (h k n τ) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n τ) x ≤ C) :
    ∀ A Dd : ℝ, ∃ C : ℝ, ∀ τ ∈ Ioo (-T) 0, ∀ z x : P.M,
      metricScalarAt (G τ) z ≤ A → riemannianEDistOf (G τ) z x < ENNReal.ofReal Dd →
        metricScalarAt (G τ) x ≤ C := by
  intro A Dd
  obtain ⟨C', hC'⟩ := happrox (A + 1) (Dd + 1)
  refine ⟨C' + 1, fun τ hτ z x hz hzx => ?_⟩
  have hDd : 0 < Dd := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hzx)
  have hτ' : τ ∈ Ioc (-T) 0 := ⟨hτ.1, hτ.2.le⟩
  have hgs := hcomplete τ hτ'
  set r := Dd + 1 / 2 with hrdef
  have hr : 0 < r := by positivity
  have hcptr : IsCompact (riemannianClosedBallOf (G τ) z r) :=
    RiemannianMetricComplete.closedEBall_isCompact hgs z r
  obtain ⟨k₁, hk₁⟩ := hcptr.elim_directed_cover (fun k => (V k : Set P.M))
    (fun k => (V k).isOpen) (fun w _ => mem_iUnion.mpr (hVcover w)) hVmono.directed_le
  obtain ⟨k₂, hk₂⟩ := hcT τ hτ'
  set k := max k₁ k₂ with hk_def
  have hball_k : riemannianClosedBallOf (G τ) z r ⊆ V k :=
    hk₁.trans (hVmono (le_max_left _ _))
  have hτk : τ ∈ Icc (-c k) 0 :=
    ⟨((neg_le_neg (hcmono (le_max_right _ _))).trans hk₂.le), hτ.2.le⟩
  have hzself : z ∈ riemannianClosedBallOf (G τ) z r := by
    change riemannianEDistOf (G τ) z z ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hdzx : riemannianEDistOf (G τ) z x < ENNReal.ofReal r :=
    hzx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hxself : x ∈ riemannianClosedBallOf (G τ) z r := hdzx.le
  set zk : V k := ⟨z, hball_k hzself⟩ with hzk_def
  set xk : V k := ⟨x, hball_k hxself⟩ with hxk_def
  let Kbig : Set (V k) := Subtype.val ⁻¹' riemannianClosedBallOf (G τ) z r
  have hKbig : IsCompact Kbig := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' Kbig = riemannianClosedBallOf (G τ) z r := by
      ext w
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hw'
      · intro hw
        exact ⟨⟨w, hball_k hw⟩, hw, rfl⟩
    rw [himg]
    exact hcptr
  let seq : ℕ → SmoothRiemannianMetric I3 (V k) := fun i =>
    if hi : N k ≤ ψ i then
      localPullMetric (h k (f (ψ i)) τ) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G τ).restrictOpen (V k)
  have hseq_eq : ∀ i (hi : N k ≤ ψ i),
      seq i = localPullMetric (h k (f (ψ i)) τ) (φ k (ψ i) hi) (hφ k (ψ i) hi) :=
    fun i hi => dite_eq_left hi
  have hconvk : MetricCInfConvergenceOnCompacts seq
      ((G τ).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
    intro K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K hK p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    rw [hseq_eq i hi']
    exact hb τ hτk
  set ε₀ := min 1 (1 / Dd) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min one_pos (by positivity)
  have hunif := (hconvk Kbig hKbig 2).tendstoUniformlyOn_metricScalarAt hKbig
  have hquad := hconvk.eventually_quadratic_bounds hKbig hε₀
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  obtain ⟨i, hi, hsc, hq2, happ⟩ :=
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((Metric.tendstoUniformlyOn_iff.mp hunif (1 / 2) (by norm_num)).and
        (hquad.and (hfψ.eventually (hC' k τ hτk hτ.2))))).exists
  have hseq := hseq_eq i hi
  set L := Real.sqrt (1 + ε₀) with hLdef
  have hL : 0 < L := Real.sqrt_pos.mpr (by linarith)
  have hdist := DifferentialGeometry.Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens
    (h k (f (ψ i)) τ) (G τ) (V k) (φ k (ψ i) hi) (hφ k (ψ i) hi) (hinj k (ψ i) hi) zk xk hr hL
    hball_k (fun y hy v => by
      have h1 := (hq2 y hy v).2
      rw [hseq, localPullMetric_inner] at h1
      rw [hLdef, Real.sq_sqrt (by linarith)]
      exact h1) hdzx
  have hdist' : riemannianEDistOf (h k (f (ψ i)) τ) (φ k (ψ i) hi zk) (φ k (ψ i) hi xk) <
      ENNReal.ofReal (Dd + 1) := by
    refine lt_of_le_of_lt hdist ?_
    have hne : riemannianEDistOf (G τ) z x ≠ ⊤ := ne_top_of_lt hzx
    rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_mul hL.le]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_
    have hd : (riemannianEDistOf (G τ) z x).toReal < Dd :=
      (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr hzx |>.trans_le
        (le_of_eq (ENNReal.toReal_ofReal hDd.le))
    have hLDd : L * Dd ≤ Dd + 1 := by
      have h1 : L * Dd = Real.sqrt ((1 + ε₀) * Dd ^ 2) := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hDd.le]
      have hζD : ε₀ * Dd ≤ 1 := by
        calc ε₀ * Dd ≤ 1 / Dd * Dd := mul_le_mul_of_nonneg_right (min_le_right _ _) hDd.le
          _ = 1 := by field_simp
      have h2 : (1 + ε₀) * Dd ^ 2 ≤ (Dd + 1) ^ 2 := by nlinarith
      rw [h1]
      calc Real.sqrt ((1 + ε₀) * Dd ^ 2) ≤ Real.sqrt ((Dd + 1) ^ 2) := Real.sqrt_le_sqrt h2
        _ = Dd + 1 := Real.sqrt_sq (by linarith)
    have h3 : L * (riemannianEDistOf (G τ) z x).toReal < L * Dd :=
      mul_lt_mul_of_pos_left hd hL
    linarith
  have hzsc : metricScalarAt (h k (f (ψ i)) τ) (φ k (ψ i) hi zk) ≤ A + 1 := by
    have h1 := hsc zk hzself
    rw [Real.dist_eq, hseq, metricScalarAt_localPull, metricScalarAt_restrictOpen] at h1
    have h2 := (abs_lt.mp h1).1
    change metricScalarAt (G τ) z ≤ A at hz
    linarith
  have hxsc := happ _ _ hzsc hdist'
  have h1 := hsc xk hxself
  rw [Real.dist_eq, hseq, metricScalarAt_localPull, metricScalarAt_restrictOpen] at h1
  have h2 := (abs_lt.mp h1).2
  change metricScalarAt (G τ) x - _ < _ at h2
  linarith

def crossingWindowNeckAccuracy : ℝ :=
  neckModelTolerance (min (windowNeckAccuracy.{u} / 2) (1 / 44))

theorem crossingWindowNeckAccuracy_pos : 0 < crossingWindowNeckAccuracy.{u} :=
  neckModelTolerance_pos (lt_min (half_pos windowNeckAccuracy_pos) (by norm_num))

theorem exists_uniform_scalar_bound_of_local_flow_limit_on_window
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → TopologicalSpace.Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    (hWF : ∀ k, ∀ᶠ j in atTop, ((W k (f j) : Set (X.obj (f j)).M)) ⊆ F.target j)
    {T : ℝ} (hT : 0 < T) {c τ : ℕ → ℝ} (hτ : ∀ k, 0 < τ k) (hcτ : ∀ k, c k < τ k)
    (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
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
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (Perelman.rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x)))
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-c k) 0,
      ∀ σ' ∈ Icc (-c k) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {E : ℕ → Set ℝ} {ζ : ℕ → ℝ} (hζ : Tendsto ζ atTop (𝓝 0))
    (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite)
    {eps qW C2 qD Ctime κ : ℝ} (heps : eps ≤ crossingWindowNeckAccuracy.{u}) (hC2 : 1 ≤ C2)
    (hκ : 0 < κ)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) eps z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        IsCompact (connectedComponent z))
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2)
    (hpar : (∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t)) →
      Perelman.ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } :
        SolutionOn (I := I3) (M := P.M)
          (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) κ 1)
    (happrox : ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ τ ∈ Icc (-c k) 0, τ < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n τ) z ≤ A →
        riemannianEDistOf (h k n τ) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n τ) x ≤ C) :
    ∃ C : ℝ, ∀ t ∈ Ioc (-T) 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C := by
  set alpha := min (windowNeckAccuracy.{u} / 2) (1 / 44) with halpha_def
  have halpha : 0 < alpha := lt_min (half_pos windowNeckAccuracy_pos) (by norm_num)
  have h2α : 2 * alpha ≤ windowNeckAccuracy.{u} := by
    have := min_le_left (windowNeckAccuracy.{u} / 2) (1 / 44 : ℝ)
    linarith
  have hsmall : 2 * alpha < 1 / 11 := by
    have := min_le_right (windowNeckAccuracy.{u} / 2) (1 / 44 : ℝ)
    linarith
  have hnmt : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hcone := curvatureOperator_nonnegative_of_local_pinching_limit_on_window hf hVmono hVcover
    hcmono hcT hψ hconv hQ hPhi hpinch
  have hcompl0 : RiemannianMetricComplete (G 0) := by
    rw [hG0]
    exact ⟨CheegerGromovCompactness.MetricComplete.complete P hPc⟩
  have hcomplete : ∀ t ∈ Ioc (-T) 0, RiemannianMetricComplete (G t) := fun t ht =>
    complete_at_earlier_time_of_ricci_nonnegative
      ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) hGsol
      (a := t) (b := 0) (fun r hr => ⟨ht.1.trans_le hr.1, hr.2⟩)
      (fun r hr => ⟨ht.1.trans hr.1, hr.2⟩)
      (fun r hr x v => metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
        (G r) x (hcone r ⟨ht.1.trans hr.1, hr.2.le⟩ x) v) hcompl0 ⟨le_rfl, ht.2⟩
  have hder := abs_derivWithin_scalar_le_of_local_flow_limit_of_shrinking_sliver_on_window hf
    hVmono hVcover hT hτ hcτ hcmono hcT hGsol hψ hconv hsol hζ hE hderiv
  obtain ⟨κ', hκ', hnc⟩ := exists_metricNoncollapsed_of_parabolic_of_curvatureOperator_nonnegative
    hT hGsol hG0 hcone hκ hder (hpar hcomplete)
  have hinj : ∀ k j (hj : N k ≤ j), Function.Injective (φ k j hj) := by
    intro k j hj z z' hzz
    have h1 : F.map j z = F.map j z' := by
      rw [← hφF k j hj z, ← hφF k j hj z', hzz]
    exact Subtype.ext ((F.partialDiffeomorph j).injOn (hVF k j hj z.2) (hVF k j hj z'.2) h1)
  have hRP := scalar_le_at_distance_of_local_flow_limit_on_window hf hVmono hVcover hinj hcmono
    hcT hcomplete hψ hconv happrox
  have hsel : ∀ s : ℝ, ∃ σ : ℕ → ℝ, s ≤ 0 →
      Tendsto σ atTop (𝓝 s) ∧ ∀ n, σ n ≤ s ∧ σ n ∉ E n := fun s =>
    if hs : s ≤ 0 then (exists_tendsto_forall_notMem_of_finite_diff_Icc hζ hE hs).imp
      fun _ hσ _ => hσ
    else ⟨0, fun h => absurd h hs⟩
  choose σ hσ using hsel
  have hσE : ∀ s ∈ Ioc (-T) 0, ∀ᶠ n in atTop, σ s n ∉ E n := fun s hs =>
    Eventually.of_forall fun n => ((hσ s hs.2).2 n).2
  have hconvσ : ∀ s ∈ Ioc (-T) 0, ∀ k : ℕ, -c k < s → ∀ (K : Set (V k)), IsCompact K →
      ∀ p : ℕ, ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        σ s (f (ψ i)) ∈ Icc (-c k) 0 ∧
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η :=
    fun s hs k hk K hK p η hη =>
      tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz_on_window hf F Cd hcan hPc
        hV hφF hG0 hψ hconv hLip hs.2 (hσ s hs.2).1 (fun n => ((hσ s hs.2).2 n).1) k hk K hK p hη
  have hW' : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        IsCompact (connectedComponent z) := by
    intro k
    filter_upwards [hW k] with n hn s hs hsE z hz hq
    rcases hn s hs hsE z hz hq with hnk | ⟨w, hnk, h1⟩ | h3
    · obtain ⟨nk⟩ := hnk
      exact Or.inl ⟨nk.mono heps hnmt⟩
    · obtain ⟨nk⟩ := hnk
      exact Or.inr (Or.inl ⟨w, ⟨nk.mono heps hnmt⟩, h1⟩)
    · exact Or.inr (Or.inr h3)
  have halt := neck_alternatives_of_local_flow_limit_on_window halpha hsmall hf F Cd hcan hPc hconn
    hV hVF hφF hWF hcmono hcT hψ hconvσ hcomplete hσE hC2 hW'
  set C4 := 4 * max C2 1 with hC4def
  set qA := max (4 * max qW 1) (max (4 * max qD 1) ((2 * max C2 1) ^ 2)) with hqAdef
  have hqW : 4 * max qW 1 ≤ qA := le_max_left _ _
  have hqD : 4 * max qD 1 ≤ qA := (le_max_left _ _).trans (le_max_right _ _)
  have hqC : (2 * max C2 1) ^ 2 ≤ qA := (le_max_right _ _).trans (le_max_right _ _)
  have hW4 : ∀ t ∈ Ioc (-T) 0, ∀ x : P.M, qA < metricScalarAt (G t) x →
      Nonempty (SpatialNeck (G t) (2 * alpha) x) ∨
      (∃ w : P.M, Nonempty (SpatialNeck (G t) (2 * alpha) w) ∧
        metricScalarAt (G t) x ≤ C4 * metricScalarAt (G t) w ∧
        riemannianEDistOf (G t) x w < ENNReal.ofReal 2) ∨
      CompactSpace P.M := by
    intro t ht x hx
    rcases halt t ht x (hqW.trans_lt hx) with h1 | ⟨w, hw, hxw, hd⟩ | h3
    · exact Or.inl h1
    · refine Or.inr (Or.inl ⟨w, hw, hxw, hd.trans_le (ENNReal.ofReal_le_ofReal ?_)⟩)
      have hC1 : 0 < max C2 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      have hsq : 2 * max C2 1 < Real.sqrt (metricScalarAt (G t) x) :=
        (Real.lt_sqrt (by positivity)).mpr (hqC.trans_lt hx)
      have hs0 : 0 < Real.sqrt (metricScalarAt (G t) x) := by linarith
      rw [div_le_iff₀ hs0, hC4def]
      linarith
    · exact Or.inr (Or.inr h3)
  have hC0 : 0 ≤ 16 * max Ctime 0 := by positivity
  have hder4 : ∀ t ∈ Ioo (-T) 0, ∀ x : P.M, qA < metricScalarAt (G t) x →
      |derivWithin (fun v => metricScalarAt (G v) x) (Iic t) t| ≤
        ((⟨16 * max Ctime 0, hC0⟩ : ℝ≥0) : ℝ) * metricScalarAt (G t) x ^ 2 :=
    fun t ht x hx => hder t ht x (hqD.trans_lt hx)
  let _ : ConnectedSpace P.M := hconn
  exact exists_uniform_scalar_bound_on_openClosed_window_of_neck_alternatives.{u}.choose_spec.2
    hT G hGsol hG0 hcomplete hcone ⟨κ', hκ', hnc⟩ h2α hW4 hder4 hRP

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
