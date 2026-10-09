import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingToSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabContinuationDeepInside
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.BallVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem inner_le_exp_two_mul_inner_of_normSq_le {t₀ τ b K : ℝ} (ha : a ≤ t₀) (hτ : t₀ ≤ τ)
    (hτb : τ ≤ b) (hbs : b < s) (hK : 0 ≤ K)
    (hRm : ∀ u ∈ Icc t₀ b, ∀ x : P.Carrier,
      Tensor0SBundle.normSq0S (G.flow.base.metric u) x 4 (G.flow.base.rm04 u x) ≤ K ^ 2)
    (hKτ : 9 * K * (τ - t₀) ≤ 1) (x : P.Carrier) (v : TangentSpace ThreeModel x) :
    (G.flow.base.metric τ).inner x v v ≤ Real.exp 2 * (G.flow.base.metric t₀).inner x v v := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hcar : Icc t₀ b ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier :=
    fun u hu => ⟨ha.trans hu.1, hu.2.trans_lt hbs⟩
  have hreg : Ioo t₀ b ⊆ (RealTimeInterval.closedOpen a s G.lt).regular :=
    fun u hu => ⟨ha.trans_lt hu.1, hu.2.trans hbs⟩
  have h := (metric_inner_exp_bounds_of_curvature_bound G.flow G.equation hcar hreg x
    (s := τ) (t := t₀) (fun u hu => hRm u hu x) ⟨hτ, hτb⟩ ⟨le_rfl, hτ.trans hτb⟩ v).2
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (metric_inner_self_nonneg _ _ _))
  rw [hdim, Real.sqrt_sq hK, abs_of_nonneg (sub_nonneg.mpr hτ)]
  push_cast
  nlinarith

theorem riemannianBallOf_subset_exp_one_mul_of_normSq_le {t₀ τ b K : ℝ} (ha : a ≤ t₀)
    (hτ : t₀ ≤ τ) (hτb : τ ≤ b) (hbs : b < s) (hK : 0 ≤ K)
    (hRm : ∀ u ∈ Icc t₀ b, ∀ x : P.Carrier,
      Tensor0SBundle.normSq0S (G.flow.base.metric u) x 4 (G.flow.base.rm04 u x) ≤ K ^ 2)
    (hKτ : 9 * K * (τ - t₀) ≤ 1) (p : P.Carrier) (ρ : ℝ) :
    riemannianBallOf (G.flow.base.metric t₀) p ρ ⊆
      riemannianBallOf (G.flow.base.metric τ) p (Real.exp 1 * ρ) := by
  have h2 : Real.sqrt (Real.exp 2) = Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos 1).le]
  have h := riemannianBallOf_subset_of_inner_le_mul (G.flow.base.metric t₀)
    (G.flow.base.metric τ) p (r := ρ) (Real.exp_pos 2)
    (fun q _ v => G.inner_le_exp_two_mul_inner_of_normSq_le ha hτ hτb hbs hK hRm hKτ q v)
  rwa [h2] at h

theorem volume_riemannianBallOf_le_exp_three_mul_of_normSq_le {t₀ τ b K : ℝ} (ha : a ≤ t₀)
    (hτ : t₀ ≤ τ) (hτb : τ ≤ b) (hbs : b < s) (hK : 0 ≤ K)
    (hRm : ∀ u ∈ Icc t₀ b, ∀ x : P.Carrier,
      Tensor0SBundle.normSq0S (G.flow.base.metric u) x 4 (G.flow.base.rm04 u x) ≤ K ^ 2)
    (hKτ : 9 * K * (τ - t₀) ≤ 1) (p : P.Carrier) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t₀)
        (riemannianBallOf (G.flow.base.metric t₀) p ρ) ≤
      ENNReal.ofReal (Real.exp 3) * riemannianVolumeMeasure ThreeModel P.Carrier
        (G.flow.base.metric τ) (riemannianBallOf (G.flow.base.metric τ) p (Real.exp 1 * ρ)) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hcar : Icc t₀ b ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier :=
    fun u hu => ⟨ha.trans hu.1, hu.2.trans_lt hbs⟩
  have hreg : Ioo t₀ b ⊆ (RealTimeInterval.closedOpen a s G.lt).regular :=
    fun u hu => ⟨ha.trans_lt hu.1, hu.2.trans hbs⟩
  have h := riemannianVolumeMeasure_ball_le_exp_mul_of_curvature_bound G.flow G.equation
    (s := t₀) (t := τ) hcar hreg hRm ⟨le_rfl, hτ.trans hτb⟩ ⟨hτ, hτb⟩ p ρ
  rw [hdim, Real.sqrt_sq hK, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hτ)] at h
  push_cast at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    (MeasureTheory.measure_mono (riemannianBallOf_mono _ _
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hρ))))
  · nlinarith
  · nlinarith

private theorem ofReal_mul_exp_neg_six_mul_pow_le {κ r : ℝ} {V : ENNReal} (hκ : 0 < κ)
    (hr : 0 < r)
    (h : ENNReal.ofReal κ * ENNReal.ofReal (r / Real.exp 1) ^ 3 ≤
      ENNReal.ofReal (Real.exp 3) * V) :
    ENNReal.ofReal (κ * Real.exp (-6)) * ENNReal.ofReal r ^ 3 ≤ V := by
  have he := Real.exp_pos 1
  have hexp : Real.exp (-6) * Real.exp 1 ^ 3 = Real.exp (-3) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have key : ENNReal.ofReal (κ * Real.exp (-6)) * ENNReal.ofReal r ^ 3 =
      ENNReal.ofReal (Real.exp (-3)) *
        (ENNReal.ofReal κ * ENNReal.ofReal (r / Real.exp 1) ^ 3) := by
    rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_pow (div_pos hr he).le,
      ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul (mul_pos hκ (Real.exp_pos _)).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [div_pow, ← hexp]
    field_simp
  rw [key]
  calc ENNReal.ofReal (Real.exp (-3)) *
        (ENNReal.ofReal κ * ENNReal.ofReal (r / Real.exp 1) ^ 3)
      ≤ ENNReal.ofReal (Real.exp (-3)) * (ENNReal.ofReal (Real.exp 3) * V) :=
        mul_le_mul' le_rfl h
    _ = V := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      norm_num

theorem exists_isKappaNoncollapsed_forward_of_before {κ ρ t₀ : ℝ} (ht₀ : a < t₀) (ht₀s : t₀ < s)
    (hnc : ∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
      (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) ≤ t₀ → B.radius ≤ ρ →
        B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
      (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) < t₀ + η → B.radius ≤ ρ →
        B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed (κ * Real.exp (-6)) := by
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (t₀ + s) / 2 := ⟨_, rfl⟩
  have hbs : b < s := by rw [hbdef]; linarith
  have ht₀b : t₀ < b := by rw [hbdef]; linarith
  obtain ⟨K₀, hK₀⟩ := G.exists_forall_Icc_riemannNorm_le hbs
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max K₀ 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK₀K : K₀ ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK : 0 < K := one_pos.trans_le hK1
  have hsq : ∀ u ∈ Icc a b, ∀ x : P.Carrier,
      Perelman.FlowMetricBall.rmNormSq G.flow u x ≤ K ^ 2 := by
    intro u hu x
    have h1 : Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow u x) ≤ K :=
      (hK₀ u hu x).trans hK₀K
    exact (Real.sqrt_le_iff.mp h1).2
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (min ((t₀ - a) / 2) (b - t₀)) (1 / (9 * K)) :=
    ⟨_, rfl⟩
  have hη1 : η ≤ (t₀ - a) / 2 := by
    rw [hηdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ b - t₀ := by
    rw [hηdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ 1 / (9 * K) := by rw [hηdef]; exact min_le_right _ _
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hKη : 9 * K * η ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hη3 (by positivity : (0 : ℝ) ≤ 9 * K)
    rwa [mul_one_div_cancel (by positivity)] at h
  clear hηdef hη3 hK₀ hK₀K hKdef hbdef
  refine ⟨η, hηpos, fun τ B hτ hr hB => ?_⟩
  rcases le_or_gt (τ : ℝ) t₀ with hτt | hτt
  · have h := hnc τ B hτt hr hB
    refine ⟨mul_pos h.1 (Real.exp_pos _), le_trans ?_ h.2⟩
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    exact mul_le_of_le_one_right h.1.le (Real.exp_le_one_iff.mpr (by norm_num))
  set r := B.radius with hrdef
  have hr0 : 0 < r := B.radius_pos
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hre : r / Real.exp 1 ≤ r := div_le_self hr0.le (by linarith)
  have hre2 : r / Real.exp 1 ≤ r / 2 := div_le_div_of_nonneg_left hr0.le two_pos he2
  have hre0 : 0 < r / Real.exp 1 := div_pos hr0 he
  have hcancel : Real.exp 1 * (r / Real.exp 1) = r := mul_div_cancel₀ _ he.ne'
  have hτb : (τ : ℝ) ≤ b := by linarith
  have hRm : ∀ u ∈ Icc t₀ b, ∀ x : P.Carrier,
      Tensor0SBundle.normSq0S (G.flow.base.metric u) x 4 (G.flow.base.rm04 u x) ≤ K ^ 2 :=
    fun u hu x => hsq u ⟨ht₀.le.trans hu.1, hu.2⟩ x
  have hKgap : 9 * K * ((τ : ℝ) - t₀) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (show (τ : ℝ) - t₀ ≤ η by linarith)
      (by positivity : (0 : ℝ) ≤ 9 * K)
    linarith
  have hsub : riemannianBallOf (G.flow.base.metric t₀) B.center (r / Real.exp 1) ⊆
      riemannianBallOf (G.flow.base.metric τ) B.center r := by
    have h := G.riemannianBallOf_subset_exp_one_mul_of_normSq_le ht₀.le hτt.le hτb hbs hK.le
      hRm hKgap B.center (r / Real.exp 1)
    rwa [hcancel] at h
  have hvol := G.volume_riemannianBallOf_le_exp_three_mul_of_normSq_le ht₀.le hτt.le hτb hbs
    hK.le hRm hKgap B.center hre0.le
  rw [hcancel] at hvol
  let τ₀ : (RealTimeInterval.closedOpen a s G.lt).FlowTime := ⟨t₀, ⟨ht₀.le, ht₀s⟩⟩
  let B₀ : Perelman.FlowMetricBall G.flow τ₀ := ⟨B.center, r / Real.exp 1, hre0⟩
  have hB₀ : B₀.IsParabolicallyRmControlled := by
    by_cases hwin : (τ : ℝ) - r ^ 2 ≤ t₀ - (r / Real.exp 1) ^ 2
    · have hwin' : Icc (t₀ - (r / Real.exp 1) ^ 2) t₀ ⊆ Icc ((τ : ℝ) - r ^ 2) τ :=
        fun u hu => ⟨hwin.trans hu.1, hu.2.trans hτt.le⟩
      refine ⟨fun u hu => hB.1 (hwin' hu), fun u hu x hx => ?_⟩
      have h := hB.2 u (hwin' hu) x (hsub hx)
      have hpow : (r / Real.exp 1) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hre0.le hre 4
      exact le_trans (mul_le_mul_of_nonneg_right hpow
        (Tensor0SBundle.normSq0S_nonneg _ _ _ _)) h
    · have hwin2 := not_le.mp hwin
      have hq : (r / Real.exp 1) ^ 2 ≤ r ^ 2 / 4 :=
        (pow_le_pow_left₀ hre0.le hre2 2).trans_eq (by ring)
      have hsmall : r ^ 2 < 2 * η := by linarith
      have hre4 : (r / Real.exp 1) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hre0.le hre 2
      refine ⟨fun u hu => ⟨?_, hu.2.trans_lt ht₀s⟩, fun u hu x _ => ?_⟩
      · have hu1 : t₀ - (r / Real.exp 1) ^ 2 ≤ u := hu.1
        linarith
      · have hu1 : t₀ - (r / Real.exp 1) ^ 2 ≤ u := hu.1
        have hu2 : u ≤ t₀ := hu.2
        have hx := hsq u ⟨by linarith, hu2.trans ht₀b.le⟩ x
        have hw0 : 0 ≤ (r / Real.exp 1) ^ 2 * K := mul_nonneg (sq_nonneg _) hK.le
        have hwK : (r / Real.exp 1) ^ 2 * K ≤ 1 := by
          have h := mul_le_mul_of_nonneg_right (hre4.trans hsmall.le) hK.le
          linarith
        change (r / Real.exp 1) ^ 4 * Perelman.FlowMetricBall.rmNormSq G.flow u x ≤ 1
        calc (r / Real.exp 1) ^ 4 * Perelman.FlowMetricBall.rmNormSq G.flow u x
            ≤ (r / Real.exp 1) ^ 4 * K ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity)
          _ = ((r / Real.exp 1) ^ 2 * K) ^ 2 := by ring
          _ ≤ 1 := pow_le_one₀ hw0 hwK
  have h0 := hnc τ₀ B₀ le_rfl (hre.trans hr) hB₀
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨hκ, h0v⟩ := h0
  refine ⟨mul_pos hκ (Real.exp_pos _), ?_⟩
  rw [hdim] at h0v ⊢
  exact ofReal_mul_exp_neg_six_mul_pow_le hκ hr0 (h0v.trans hvol)

end OrientedThreeStage.IncomingSlab

open OrientedThreeStage.IncomingSlab
  (exists_uniform_canonical_threshold_of_parabolically_noncollapsed) in
theorem deepContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    DeepContinuation P₀ g₀ := by
  intro B ε _ hε hε'
  obtain ⟨C, hC, -, hU⟩ :=
    exists_uniform_canonical_threshold_of_parabolically_noncollapsed.{u} hε hε'
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, C, 1, ⟨C, hC0⟩, ⟨C, hC0⟩, hC, hC, one_pos, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1 hC2 _ hCt hCg κ phi hκ hphi
  have hCt' : C ≤ (Ctime : ℝ) := NNReal.coe_le_coe.mpr hCt
  have hCg' : C ≤ (Cgrad : ℝ) := NNReal.coe_le_coe.mpr hCg
  obtain ⟨Q₀, theta, hQ₀, htheta, hW⟩ :=
    hU (κ * Real.exp (-6)) (mul_pos hκ (Real.exp_pos _)) ε hε phi hphi
  have key : ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s) (qcan t₀ : ℝ),
      Q₀ ≤ qcan → Perelman.PhiAlmostNonnegative G.flow (Ico a s) phi → t₀ ∈ Ico a s →
      (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
        (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) ≤ t₀ → B.radius ≤ ε →
          B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) →
      ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
        fun y t => 2 * theta ≤ G.flow.scalar t y * (t - a) := by
    intro P a s G qcan t₀ hq hpinch ht₀ hnc
    have hbounds : ∀ η : ℝ, (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
        (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) < t₀ + η → B.radius ≤ ε →
          B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed (κ * Real.exp (-6))) →
        G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
          fun y t => 2 * theta ≤ G.flow.scalar t y * (t - a) := by
      intro η hncη y t _ _ htη hts hR hage
      have hRpos : 0 < G.flow.scalar t y := hQ₀.trans_le (hq.trans hR.le)
      have hwin : a ≤ t - theta / G.flow.scalar t y := by
        have h : theta / G.flow.scalar t y ≤ t - a := by
          rw [div_le_iff₀ hRpos]
          nlinarith
        linarith
      obtain ⟨W, hWc⟩ := hW P a s G y t hts (hq.trans hR.le) hwin
        (fun v hv z => hpinch v ⟨hwin.trans hv.1, hv.2.trans_lt hts⟩ z)
        (fun τ B _ h2 h3 h4 => hncη τ B (h2.trans_lt htη) h3 h4)
      refine ⟨fun _ => ⟨W.enlargeConstants hC1 hC2, hWc.enlarge_constants hC1 hC2⟩, ?_, ?_⟩
      · exact W.time_derivative.trans (mul_le_mul_of_nonneg_right hCt' (sq_nonneg _))
      · intro v
        exact (W.gradient v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCg' hRpos.le)
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · obtain ⟨K, hK⟩ := G.exists_forall_Icc_scalar_le (b := (a + s) / 2) (by linarith [G.lt])
      have hM : 0 < max K 1 := one_pos.trans_le (le_max_right _ _)
      refine ⟨min ((s - a) / 2) (theta / max K 1),
        lt_min (by linarith [G.lt]) (div_pos htheta hM), ?_⟩
      intro y t _ ht₀' htη _ hR hage
      exfalso
      have hle1 := min_le_left ((s - a) / 2) (theta / max K 1)
      have hle2 := min_le_right ((s - a) / 2) (theta / max K 1)
      have htb : t ∈ Icc a ((a + s) / 2) := ⟨by linarith, by linarith⟩
      have hRK : G.flow.scalar t y ≤ max K 1 := (hK t htb y).trans (le_max_left _ _)
      have hta : t - a < theta / max K 1 := by linarith
      have h1 : G.flow.scalar t y * (t - a) ≤ max K 1 * (t - a) :=
        mul_le_mul_of_nonneg_right hRK (by linarith)
      have h2 : max K 1 * (t - a) < theta := by
        rw [lt_div_iff₀ hM] at hta
        linarith
      linarith
    · obtain ⟨η, hη, hfw⟩ := G.exists_isKappaNoncollapsed_forward_of_before h ht₀.2 hnc
      exact ⟨η, hη, hbounds η hfw⟩
  refine ⟨2 * theta, Q₀, 1, 1, 1, 1, 0, mul_pos two_pos htheta, hQ₀, one_pos, one_pos, one_pos,
    one_pos, ?_⟩
  intro qcan hq p₀ δbound ρbound _ _ _ _ _ H hH hpinch
  refine ⟨fun j _ _ _ t₀ ht₀ _ _ _ hnc => ?_, fun s G hG hpG _ _ _ _ t₀ ht₀ _ _ _ hnc => ?_⟩
  · exact key _ _ _ (H.toHistory.event j).incoming qcan t₀ hq (hpinch j) ht₀
      (H.isKappaNoncollapsed_of_noncollapsedBefore hκ hnc j)
  · exact key _ _ _ G qcan t₀ hq hpG ht₀
      (H.isKappaNoncollapsed_of_terminalNoncollapsedBefore hH.2.1 G hG.2 hκ hnc)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
