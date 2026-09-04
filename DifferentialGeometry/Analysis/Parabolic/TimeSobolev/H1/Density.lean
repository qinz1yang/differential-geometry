import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.FlatDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Function Set intervalIntegral
open scoped ContDiff ENNReal Topology
open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

noncomputable section

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

private def unitBump (T : ℝ) (hT : 0 < T) : ContDiffBump (T / 2) :=
  ⟨T / 8, T / 4, by positivity, by linarith⟩

private lemma unitBump_int (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, (unitBump T hT).normed volume t = 1 := by
  let b := unitBump T hT
  have hsupp : Function.support (b.normed volume) ⊆ Icc (0 : ℝ) T := by
    rw [b.support_normed_eq]
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    dsimp [b, unitBump] at ht
    constructor <;> linarith [abs_lt.mp ht]
  have hind : (Icc (0 : ℝ) T).indicator (b.normed volume) = b.normed volume := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · simp only [indicator_of_mem ht]
    · have hz : b.normed volume t = 0 := by
        by_contra hne
        exact ht (hsupp hne)
      simp only [indicator_of_notMem ht, hz]
  change ∫ t in (0 : ℝ)..T, b.normed volume t = 1
  rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Icc, hind]
  exact b.integral_normed

private lemma unitBump_zero (T : ℝ) (hT : 0 < T) :
    (unitBump T hT).normed volume =ᶠ[𝓝 (0 : ℝ)] 0 ∧
      (unitBump T hT).normed volume =ᶠ[𝓝 T] 0 := by
  let b := unitBump T hT
  have hzero (a : ℝ) (ha : a ∉ Metric.closedBall (T / 2) b.rOut) :
      b.normed volume =ᶠ[𝓝 a] 0 := by
    have hnhds : (Metric.closedBall (T / 2) b.rOut)ᶜ ∈ 𝓝 a :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds ha
    filter_upwards [hnhds] with t ht
    have ht' : t ∉ Function.support (b.normed volume) := by
      rw [b.support_normed_eq]
      exact fun hball => ht (Metric.ball_subset_closedBall hball)
    exact notMem_support.mp ht'
  constructor
  · apply hzero 0
    rw [Metric.mem_closedBall, Real.dist_eq]
    dsimp [b, unitBump]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · apply hzero T
    rw [Metric.mem_closedBall, Real.dist_eq]
    dsimp [b, unitBump]
    rw [abs_of_nonneg (by linarith)]
    linarith

omit [FiniteDimensional ℝ X] in
private lemma int_eq_time
    {T : ℝ} (hT : 0 ≤ T) {v : timeL2 X T} {g : ℝ → X}
    (hvg : v =ᵐ[timeMeasure T] g) :
    ∫ t in (0 : ℝ)..T, g t = TimeSobolev.timeIntegral X T v := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    TimeSobolev.timeIntegral_apply]
  simpa only [timeMeasure] using integral_congr_ae hvg.symm

private lemma prim_germ
    {g : ℝ → X} (hg : Continuous g) {a : ℝ} (ha : g =ᶠ[𝓝 a] 0) (c : X) :
    (fun t => c + ∫ s in a..t, g s) =ᶠ[𝓝 a] fun _ => c := by
  change {t | g t = 0} ∈ 𝓝 a at ha
  rcases Metric.mem_nhds_iff.mp ha with ⟨r, hr, hra⟩
  let F : ℝ → X := fun t => c + ∫ s in a..t, g s
  have hFdiff : Differentiable ℝ F :=
    (differentiable_const c).add (intervalIntegral.differentiable_integral_of_continuous hg)
  have hFderiv : EqOn (_root_.deriv F) (_root_.deriv fun _ : ℝ => c) (Metric.ball a r) := by
    intro t ht
    have hgt : g t = 0 := hra ht
    rw [show _root_.deriv F t = g t by
      exact ((intervalIntegral.integral_hasDerivAt_right
        (hg.intervalIntegrable a t)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add c).deriv]
    simp only [hgt, deriv_const]
  have heq : EqOn F (fun _ : ℝ => c) (Metric.ball a r) :=
    Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball a r).isPreconnected
      hFdiff.differentiableOn (differentiable_const c).differentiableOn hFderiv
      (Metric.mem_ball_self hr) (by simp only [F, intervalIntegral.integral_same, add_zero])
  exact mem_of_superset (Metric.ball_mem_nhds a hr) heq

omit [FiniteDimensional ℝ X] in
private lemma germ_deriv
    {T : ℝ} (hT : 0 < T) (v : timeL2 X T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℝ → X) (d : timeL2 X T),
      ContDiff ℝ ∞ q ∧ d =ᵐ[timeMeasure T] q ∧
        q =ᶠ[𝓝 (0 : ℝ)] 0 ∧ q =ᶠ[𝓝 T] 0 ∧ dist d v < ε := by
  classical
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨q, d, hq, _hq_support, hdq, hdv⟩ := exists_flat_deriv hT v hη
  have hqLp : MemLp q 2 (timeMeasure T) := (Lp.memLp d).ae_eq hdq
  obtain ⟨δ, hδ, hsmall⟩ :=
    hqLp.eLpNorm_indicator_le (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hη
  let ρ : ℝ := min (T / 8) (δ / 4)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by linarith)
  have hρT : ρ ≤ T / 8 := min_le_left _ _
  have h2ρδ : 2 * ρ ≤ δ := by
    have hρδ : ρ ≤ δ / 4 := min_le_right _ _
    linarith
  let S : Set ℝ := Icc 0 ρ ∪ Icc (T - ρ) T
  have hSmeas : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  have hμS : timeMeasure T S ≤ ENNReal.ofReal δ := by
    calc
      timeMeasure T S ≤ volume S := Measure.restrict_le_self S
      _ ≤ volume (Icc 0 ρ) + volume (Icc (T - ρ) T) := measure_union_le _ _
      _ = ENNReal.ofReal ρ + ENNReal.ofReal ρ := by
        rw [Real.volume_Icc, Real.volume_Icc]
        congr 2 <;> ring
      _ = ENNReal.ofReal (2 * ρ) := by
        rw [show 2 * ρ = ρ + ρ by ring, ENNReal.ofReal_add hρ.le]
        exact hρ.le
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h2ρδ
  have hSsmall : eLpNorm (S.indicator q) 2 (timeMeasure T) ≤ ENNReal.ofReal η :=
    hsmall S hSmeas hμS
  let χ : ContDiffBump (T / 2) :=
    ⟨T / 2 - ρ, T / 2 - ρ / 2, by linarith [hρT], by linarith [hρ]⟩
  let q' : ℝ → X := fun t => χ t • q t
  have hq' : ContDiff ℝ ∞ q' := χ.contDiff.smul hq
  have hq'mem : MemLp q' 2 (timeMeasure T) :=
    memLp_of_continuousOn hq'.continuous.continuousOn
  have hq'q : eLpNorm (q' - q) 2 (timeMeasure T) ≤ ENNReal.ofReal η := by
    refine (eLpNorm_mono_ae ?_).trans hSsmall
    unfold timeMeasure
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    by_cases htS : t ∈ S
    · rw [Set.indicator_of_mem htS]
      change ‖χ t • q t - q t‖ ≤ ‖q t‖
      rw [show χ t • q t - q t = (χ t - 1) • q t by module,
        norm_smul, Real.norm_eq_abs]
      have habs : |χ t - 1| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr χ.le_one)]
        linarith [χ.nonneg (x := t)]
      nlinarith [norm_nonneg (q t)]
    · rw [Set.indicator_of_notMem htS]
      have hleft : ρ ≤ t := by
        by_contra h
        apply htS
        left
        exact ⟨ht.1, le_of_not_ge h⟩
      have hright : t ≤ T - ρ := by
        by_contra h
        apply htS
        right
        exact ⟨le_of_not_ge h, ht.2⟩
      have htclosed : t ∈ Metric.closedBall (T / 2) χ.rIn := by
        rw [Real.closedBall_eq_Icc]
        dsimp [χ]
        constructor <;> linarith
      rw [norm_zero]
      simp only [q', Pi.sub_apply, χ.one_of_mem_closedBall htclosed,
        one_smul, sub_self, norm_zero]
      exact le_rfl
  let d' : timeL2 X T := ofContinuousOn hq'.continuous.continuousOn
  have hd'q : d' =ᵐ[timeMeasure T] q' := coeFn_ofContinuousOn _
  have hd'd : dist d' d ≤ η := by
    rw [Lp.dist_def]
    refine ENNReal.toReal_le_of_le_ofReal hη.le ?_
    calc
      eLpNorm ((d' : ℝ → X) - (d : ℝ → X)) 2 (timeMeasure T) =
          eLpNorm (q' - q) 2 (timeMeasure T) := by
            apply eLpNorm_congr_ae
            exact hd'q.sub hdq
      _ ≤ ENNReal.ofReal η := hq'q
  have hzero (a : ℝ) (ha : a ∉ Metric.closedBall (T / 2) χ.rOut) :
      q' =ᶠ[𝓝 a] 0 := by
    have hnhds : (Metric.closedBall (T / 2) χ.rOut)ᶜ ∈ 𝓝 a :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds ha
    filter_upwards [hnhds] with t ht
    have hχt : χ t = 0 := χ.zero_of_le_dist (le_of_not_ge ht)
    simp only [q', hχt, zero_smul, Pi.zero_apply]
  have hq'0 : q' =ᶠ[𝓝 (0 : ℝ)] 0 := by
    apply hzero 0
    rw [Metric.mem_closedBall, Real.dist_eq]
    dsimp [χ]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hq'T : q' =ᶠ[𝓝 T] 0 := by
    apply hzero T
    rw [Metric.mem_closedBall, Real.dist_eq]
    dsimp [χ]
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine ⟨q', d', hq', hd'q, hq'0, hq'T, ?_⟩
  calc
    dist d' v ≤ dist d' d + dist d v := dist_triangle _ _ _
    _ < η + η := add_lt_add_of_le_of_lt hd'd hdv
    _ = ε := by dsimp [η]; ring

omit [FiniteDimensional ℝ X] in
private lemma flat_seq
    {T : ℝ} (hT : 0 < T) (v : timeL2 X T) :
    ∃ z : ℕ → timeL2 X T, ∃ g : ℕ → ℝ → X,
      (∀ n, z n =ᵐ[timeMeasure T] g n) ∧
        (∀ n, ContDiff ℝ ∞ (g n)) ∧
        (∀ n, g n =ᶠ[𝓝 (0 : ℝ)] 0) ∧
        (∀ n, g n =ᶠ[𝓝 T] 0) ∧ Tendsto z atTop (𝓝 v) := by
  choose g z hg hzg hg0 hgT hdist using fun n : ℕ =>
    germ_deriv hT v (show 0 < (1 : ℝ) / (n + 1) by positivity)
  refine ⟨z, g, hzg, hg, hg0, hgT, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent := tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  exact ⟨N, fun n hn => (hdist n).trans (hN n hn)⟩

theorem exists_flat_dense
    {T : ℝ} (hT : 0 < T) (u : timeH1 X T) :
    ∃ w : ℕ → timeH1 X T, ∃ f : ℕ → ℝ → X,
      (∀ n, ContDiff ℝ 1 (f n)) ∧
        (∀ n, EqOn (w n).toFun (f n) (Icc (0 : ℝ) T)) ∧
        (∀ n, f n 0 = u.toFun 0) ∧ (∀ n, f n T = u.toFun T) ∧
        (∀ n, f n =ᶠ[𝓝 (0 : ℝ)] fun _ => u.toFun 0) ∧
        (∀ n, f n =ᶠ[𝓝 T] fun _ => u.toFun T) ∧
        Tendsto w atTop (𝓝 u) ∧
        Tendsto (fun n => (w n).deriv) atTop (𝓝 u.deriv) := by
  classical
  obtain ⟨z, g, hzg, hg, hg0, hgT, hz⟩ := flat_seq hT u.deriv
  let b : ℝ → ℝ := (unitBump T hT).normed volume
  let δ : ℕ → X := fun n => TimeSobolev.timeIntegral X T (u.deriv - z n)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => u.deriv - z n) atTop (𝓝 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => u.deriv) atTop (𝓝 u.deriv)).sub hz
    have hmap : Tendsto (TimeSobolev.timeIntegral X T) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (TimeSobolev.timeIntegral X T)
          (0 : timeL2 X T) :=
        (TimeSobolev.timeIntegral X T).continuous.continuousAt
      change Tendsto (TimeSobolev.timeIntegral X T) (𝓝 (0 : timeL2 X T))
        (𝓝 (TimeSobolev.timeIntegral X T (0 : timeL2 X T))) at hcont
      simpa only [map_zero] using hcont
    exact hmap.comp hsub
  let c : ℕ → timeL2 X T := fun n =>
    TimeSobolev.ofContinuousOn
      (f := fun t => b t • δ n)
      ((show Continuous (fun t => b t • δ n) from
        (show Continuous b from (unitBump T hT).continuous_normed).smul
          continuous_const).continuousOn)
  have hc0 : Tendsto c atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let B : ℝ := 1 / volume.real
      (Metric.closedBall (T / 2) (unitBump T hT).rIn)
    have hbound : ∀ n, ‖c n‖ ≤ Real.sqrt T * (B * ‖δ n‖) := by
      intro n
      apply TimeSobolev.norm_ofContinuousOn_le_of_bound
      intro t ht
      have hb0 : 0 ≤ b t := (unitBump T hT).nonneg_normed t
      have hbB : b t ≤ B :=
        (unitBump T hT).normed_le_div_measure_closedBall_rIn volume t
      simp only [b, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0]
      exact mul_le_mul_of_nonneg_right hbB (norm_nonneg _)
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg (c n))
      (Eventually.of_forall hbound) ?_
    have hnormδ : Tendsto (fun n => ‖δ n‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hδ.norm
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hnormδ))
  let d : ℕ → ℝ → X := fun n t => g n t + b t • δ n
  have hd : ∀ n, ContDiff ℝ ∞ (d n) := fun n =>
    (hg n).add ((unitBump T hT).contDiff_normed.smul_const (δ n))
  have hd0 : ∀ n, d n =ᶠ[𝓝 (0 : ℝ)] 0 := by
    intro n
    filter_upwards [hg0 n, (unitBump_zero T hT).1] with t hgt hbt
    simp only [d, b, hgt, hbt, Pi.zero_apply, zero_smul, add_zero]
  have hdT : ∀ n, d n =ᶠ[𝓝 T] 0 := by
    intro n
    filter_upwards [hgT n, (unitBump_zero T hT).2] with t hgt hbt
    simp only [d, b, hgt, hbt, Pi.zero_apply, zero_smul, add_zero]
  let f : ℕ → ℝ → X := fun n t => u.toFun 0 + ∫ s in (0 : ℝ)..t, d n s
  have hf : ∀ n, ContDiff ℝ 1 (f n) := by
    intro n
    rw [contDiff_one_iff_deriv]
    constructor
    · exact (differentiable_const (c := u.toFun 0)).add
        (intervalIntegral.differentiable_integral_of_continuous (hd n).continuous)
    · have hderiv : _root_.deriv (f n) = d n := by
        funext t
        exact ((intervalIntegral.integral_hasDerivAt_right
          ((hd n).continuous.intervalIntegrable 0 t)
          (hd n).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
          (hd n).continuous.continuousAt).const_add (u.toFun 0)).deriv
      rw [hderiv]
      exact (hd n).continuous
  have hf0 : ∀ n, f n 0 = u.toFun 0 := fun n => by simp only [f, integral_same, add_zero]
  have htime : ∀ n, ∫ t in (0 : ℝ)..T, d n t =
      TimeSobolev.timeIntegral X T u.deriv := by
    intro n
    have hsplit : (∫ t in (0 : ℝ)..T, d n t) =
        (∫ t in (0 : ℝ)..T, g n t) + ∫ t in (0 : ℝ)..T, b t • δ n := by
      have hbcont : Continuous b := by
        dsimp only [b]
        exact (unitBump T hT).continuous_normed
      have hbdcont : Continuous (fun t : ℝ => b t • δ n) :=
        hbcont.smul continuous_const
      exact intervalIntegral.integral_add
        ((hg n).continuous.intervalIntegrable 0 T)
        (hbdcont.intervalIntegrable 0 T)
    rw [hsplit]
    rw [int_eq_time hT.le (hzg n), intervalIntegral.integral_smul_const,
      unitBump_int T hT, one_smul]
    dsimp only [δ]
    rw [map_sub, add_sub_cancel]
  have hfT : ∀ n, f n T = u.toFun T := by
    intro n
    rw [show f n T = u.toFun 0 + ∫ s in (0 : ℝ)..T, d n s from rfl, htime n]
    have huend := u.toFun_sub_toFun
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT.le⟩)
      (show T ∈ Icc (0 : ℝ) T from ⟨hT.le, le_rfl⟩)
    rw [int_eq_time hT.le
      (EventuallyEq.rfl : u.deriv =ᵐ[timeMeasure T] (u.deriv : ℝ → X))] at huend
    rw [← huend]
    abel
  have hfg0 : ∀ n, f n =ᶠ[𝓝 (0 : ℝ)] fun _ => u.toFun 0 := fun n =>
    prim_germ (hd n).continuous (hd0 n) (u.toFun 0)
  have hfgT : ∀ n, f n =ᶠ[𝓝 T] fun _ => u.toFun T := by
    intro n
    have hrebase : f n = fun t => f n T + ∫ s in T..t, d n s := by
      funext t
      have hint : (∫ s in (0 : ℝ)..t, d n s) - ∫ s in (0 : ℝ)..T, d n s =
          ∫ s in T..t, d n s := intervalIntegral.integral_interval_sub_left
        ((hd n).continuous.intervalIntegrable 0 t)
        ((hd n).continuous.intervalIntegrable 0 T)
      dsimp only [f]
      rw [← hint]
      abel
    rw [hrebase]
    simpa only [hfT n] using prim_germ (hd n).continuous (hdT n) (f n T)
  let w : ℕ → timeH1 X T := fun n =>
    timeH1.ofContDiffOn hT.le (f n) (hf n).contDiffOn
  have hc_rep : ∀ n, c n =ᵐ[timeMeasure T] fun t => b t • δ n := by
    intro n
    dsimp only [c]
    exact TimeSobolev.coeFn_ofContinuousOn
      ((show Continuous (fun t => b t • δ n) from
        (show Continuous b from (unitBump T hT).continuous_normed).smul
          continuous_const).continuousOn)
  have hwderiv : ∀ n, (w n).deriv = z n + c n := by
    intro n
    apply Lp.ext
    filter_upwards [timeH1.deriv_ofContDiffOn hT.le (f n) (hf n).contDiffOn,
      hzg n, hc_rep n, Lp.coeFn_add (z n) (c n)]
      with t hwt hzt hct hsum
    have hderiv : _root_.deriv (f n) t = d n t := by
      exact ((intervalIntegral.integral_hasDerivAt_right
        ((hd n).continuous.intervalIntegrable 0 t)
        (hd n).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        (hd n).continuous.continuousAt).const_add (u.toFun 0)).deriv
    rw [hwt, hderiv]
    rw [hsum, Pi.add_apply, hzt, hct]
  have hwD : Tendsto (fun n => (w n).deriv) atTop (𝓝 u.deriv) := by
    simpa only [hwderiv, add_zero] using hz.add hc0
  have hwinit : ∀ n, (w n).init = u.init := by
    intro n
    rw [show (w n).init = f n 0 by
      simp only [w, timeH1.ofContDiffOn, timeH1.init_mk]]
    rw [hf0 n, timeH1.toFun_zero]
  have hw : Tendsto w atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnormD : Tendsto (fun n => ‖(w n).deriv - u.deriv‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hwD
    have hnorm : ∀ n, ‖w n - u‖ = ‖(w n).deriv - u.deriv‖ := by
      intro n
      have hsquare := timeH1.norm_sq_eq (w n - u)
      change ‖w n - u‖ ^ 2 = ‖(w n).init - u.init‖ ^ 2 +
        ‖(w n).deriv - u.deriv‖ ^ 2 at hsquare
      rw [hwinit n, sub_self, norm_zero] at hsquare
      norm_num at hsquare
      nlinarith [norm_nonneg (w n - u), norm_nonneg ((w n).deriv - u.deriv)]
    simpa only [hnorm] using hnormD
  refine ⟨w, f, hf, ?_, hf0, hfT, hfg0, hfgT, hw, hwD⟩
  exact fun n => timeH1.toFun_ofContDiffOn hT.le (f n) (hf n).contDiffOn

end

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
