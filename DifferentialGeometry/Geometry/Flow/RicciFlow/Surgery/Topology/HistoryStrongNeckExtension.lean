import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceConcat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionBackwardStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable {H : ObservedHistory.{u}}

private theorem le_mul_add_of_abs_inv_mul_sub_le {R X c δ : ℝ} (hR : 0 < R)
    (h : |R⁻¹ * X - c| ≤ δ) : X ≤ R * (c + δ) := by
  have h1 := (abs_le.mp h).2
  have hX : X = R * (R⁻¹ * X) := by field_simp
  rw [hX]
  exact mul_le_mul_of_nonneg_left (by linarith) hR.le

private theorem mul_sub_le_of_abs_inv_mul_sub_le {R X c δ : ℝ} (hR : 0 < R)
    (h : |R⁻¹ * X - c| ≤ δ) : R * (c - δ) ≤ X := by
  have h1 := (abs_le.mp h).1
  have hX : X = R * (R⁻¹ * X) := by field_simp
  rw [hX]
  exact mul_le_mul_of_nonneg_left (by linarith) hR.le

private theorem inv_one_sub_le_one {r : ℝ} (hr : r ≤ 0) : (1 - r)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith)

private theorem inv_one_sub_le_ten_div_eleven {r : ℝ} (hr : r ≤ -(1 / 10)) :
    (1 - r)⁻¹ ≤ 10 / 11 := by
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  norm_num
  linarith

private theorem five_div_six_le_inv_one_sub {r : ℝ} (hr : -(1 / 5) ≤ r) (hr0 : r ≤ 0) :
    5 / 6 ≤ (1 - r)⁻¹ := by
  rw [le_inv_comm₀ (by norm_num) (by linarith)]
  norm_num
  linarith

theorem exists_backwardPointTrace_scalar_le_of_hasStrongNeckAt {eps L : ℝ}
    (heps : eps ≤ 1 / 30000) (hL0 : 0 < L) {t a : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier} (htop : H.time (H.activeStage t) < t)
    (hL : L ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y *
      (3 / 4) ^ ⌈10 * metricScalarAt (H.stageMetric (H.activeStage t) t) y *
        ((t : ℝ) - a)⌉₊)
    (hsupply : ∀ v : Icc (0 : ℝ) H.horizon, a ≤ v → ∀ hvt : v ≤ t,
      H.time (H.activeStage v) < v →
      ∀ B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) y,
        L ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
          (B.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) →
        H.HasStrongNeckAt eps v (B.point (H.activeStage v) le_rfl (H.activeStage_mono hvt))) :
    ∃ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t),
      (b : ℝ) = a - (10 * metricScalarAt (H.stageMetric (H.activeStage t) t) y)⁻¹ ∧
      ∃ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) y,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) ≤
            2 * metricScalarAt (H.stageMetric (H.activeStage t) t) y := by
  set Q := metricScalarAt (H.stageMetric (H.activeStage t) t) y with hQdef
  set N := ⌈10 * Q * ((t : ℝ) - a)⌉₊ with hNdef
  have hpow0 : 0 < ((3 : ℝ) / 4) ^ N := by positivity
  have hQ : 0 < Q := by
    by_contra hQ
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hQ) hpow0.le
    linarith
  have hδ : 2400 * eps ≤ 2 / 25 := by linarith
  have h10Q : 0 < 10 * Q := by linarith
  have h10Qi : 0 ≤ (10 * Q)⁻¹ := inv_nonneg.mpr h10Q.le
  let Done : Prop :=
    ∃ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = a - (10 * Q)⁻¹ ∧
      ∃ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) y,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) ≤
            2 * Q
  let Slice (n : ℕ) : Prop :=
    ∃ (w : Icc (0 : ℝ) H.horizon) (hwt : w ≤ t), a ≤ w ∧ H.time (H.activeStage w) < w ∧
      (w : ℝ) ≤ t - n / (10 * Q) ∧
      ∃ B : BackwardPointTrace H (H.activeStage w) (H.activeStage t) (H.activeStage_mono hwt) y,
        (∀ (v : Icc (0 : ℝ) H.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (B.point (H.activeStage v) (H.activeStage_mono hwv) (H.activeStage_mono hvt)) ≤
            2 * Q) ∧
        Q * (3 / 4) ^ n ≤ metricScalarAt (H.stageMetric (H.activeStage w) w)
          (B.point (H.activeStage w) le_rfl (H.activeStage_mono hwt)) ∧
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (B.point (H.activeStage w) le_rfl (H.activeStage_mono hwt)) ≤ Q
  have hbase : Slice 0 := by
    refine ⟨t, le_rfl, hat, htop, by simp, BackwardPointTrace.singleton H (H.activeStage t) y,
      ?_, ?_, ?_⟩
    · intro v htv hvt
      have hv : v = t := le_antisymm hvt htv
      subst hv
      have hp := (BackwardPointTrace.singleton H (H.activeStage v) y).endpoint_eq
      rw [hp]
      linarith
    · have hp := (BackwardPointTrace.singleton H (H.activeStage t) y).endpoint_eq
      rw [hp, pow_zero, mul_one]
    · have hp := (BackwardPointTrace.singleton H (H.activeStage t) y).endpoint_eq
      rw [hp]
  have hstep : ∀ n, Slice n → Done ∨ Slice (n + 1) := by
    intro n ⟨w, hwt, haw, hev, hdepth, B, hBbound, hRlow, hRup⟩
    set p := B.point (H.activeStage w) le_rfl (H.activeStage_mono hwt) with hpdef
    set R := metricScalarAt (H.stageMetric (H.activeStage w) w) p with hRdef
    have hnN : n ≤ N := by
      have h1 : (n : ℝ) / (10 * Q) ≤ (t : ℝ) - a := by
        have := hdepth
        have : (a : ℝ) ≤ w := haw
        linarith
      have h2 : (n : ℝ) ≤ 10 * Q * ((t : ℝ) - a) := by
        rw [div_le_iff₀ h10Q] at h1
        linarith
      exact_mod_cast h2.trans (Nat.le_ceil _)
    have hLR : L ≤ R := by
      have hpow : ((3 : ℝ) / 4) ^ N ≤ (3 / 4) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hnN
      calc L ≤ Q * (3 / 4) ^ N := hL
        _ ≤ Q * (3 / 4) ^ n := mul_le_mul_of_nonneg_left hpow hQ.le
        _ ≤ R := hRlow
    obtain ⟨hRpos, c, hcw, hc, A', hA'⟩ :=
      exists_backwardPointTrace_scalar_bounds_of_hasStrongNeckAt
        (hsupply w haw hwt hev B hLR)
    rw [← hRdef] at hc hA'
    have hRne : R ≠ 0 := hRpos.ne'
    let C := B.concat A'
    have hCbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hcv : c ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.stageMetric (H.activeStage v) v)
          (C.point (H.activeStage v) (H.activeStage_mono hcv) (H.activeStage_mono hvt)) ≤
          2 * Q := by
      intro v hcv hvt
      by_cases hwv : w ≤ v
      · rw [BackwardPointTrace.concat_point_of_ge B A' _ _ _ (H.activeStage_mono hwv)]
        exact hBbound v hwv hvt
      · have hvw : v ≤ w := (lt_of_not_ge hwv).le
        rw [BackwardPointTrace.concat_point_of_le B A' _ _ _ (H.activeStage_mono hvw)]
        have hb := le_mul_add_of_abs_inv_mul_sub_le hRpos (hA' v hcv hvw)
        have hr : R * ((v : ℝ) - w) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hRpos.le (by have : (v : ℝ) ≤ w := hvw; linarith)
        have hc1 := inv_one_sub_le_one hr
        calc _ ≤ R * ((1 - R * ((v : ℝ) - w))⁻¹ + 2400 * eps) := hb
          _ ≤ R * 2 := mul_le_mul_of_nonneg_left (by linarith) hRpos.le
          _ ≤ 2 * Q := by linarith
    have hRQ : (10 * Q)⁻¹ ≤ (10 * R)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    by_cases hcase : (w : ℝ) - (10 * R)⁻¹ ≤ a
    · left
      have hcb : (c : ℝ) ≤ a - (10 * Q)⁻¹ := by
        have h5 : (5 * R)⁻¹ = (10 * R)⁻¹ + (10 * R)⁻¹ := by field_simp; ring
        rw [hc, h5]
        linarith
      let b : Icc (0 : ℝ) H.horizon := ⟨a - (10 * Q)⁻¹, c.2.1.trans hcb,
        (sub_le_self _ h10Qi).trans a.2.2⟩
      have hcb' : c ≤ b := hcb
      have hbt : b ≤ t := show (a : ℝ) - (10 * Q)⁻¹ ≤ t from
        (sub_le_self _ h10Qi).trans hat
      refine ⟨b, hbt, rfl,
        C.restrictFirst (H.activeStage_mono hcb') (H.activeStage_mono hbt), ?_⟩
      intro v hbv hvt
      exact hCbound v (hcb'.trans hbv) hvt
    · right
      have hlohi : max (a : ℝ) (w - (5 * R)⁻¹) < (w : ℝ) - (10 * R)⁻¹ := by
        apply max_lt (lt_of_not_ge hcase)
        have : (10 * R)⁻¹ < (5 * R)⁻¹ := inv_strictAnti₀ (by linarith) (by linarith)
        linarith
      obtain ⟨u', ⟨hu'lo, hu'hi⟩, hu'ev⟩ :=
        ((Set.Icc_infinite hlohi).sdiff (Set.finite_range H.time)).nonempty
      have hau' : (a : ℝ) ≤ u' := (le_max_left _ _).trans hu'lo
      have hcu' : (w : ℝ) - (5 * R)⁻¹ ≤ u' := (le_max_right _ _).trans hu'lo
      have hu'w : u' ≤ (w : ℝ) :=
        hu'hi.trans (sub_le_self _ (inv_nonneg.mpr (by linarith)))
      let v' : Icc (0 : ℝ) H.horizon := ⟨u', a.2.1.trans hau', hu'w.trans w.2.2⟩
      have hav' : a ≤ v' := hau'
      have hcv' : c ≤ v' := show (c : ℝ) ≤ u' by rw [hc]; exact hcu'
      have hv'w : v' ≤ w := hu'w
      have hv't : v' ≤ t := hv'w.trans hwt
      have hev' : H.time (H.activeStage v') < v' := by
        refine lt_of_le_of_ne (H.activeStage_time_le v') ?_
        intro heq
        exact hu'ev ⟨H.activeStage v', heq⟩
      refine ⟨v', hv't, hav', hev', ?_,
        C.restrictFirst (H.activeStage_mono hcv') (H.activeStage_mono hv't), ?_, ?_, ?_⟩
      · have : (w : ℝ) - (10 * R)⁻¹ ≤ w - (10 * Q)⁻¹ := by linarith
        have hn : ((n + 1 : ℕ) : ℝ) / (10 * Q) = n / (10 * Q) + (10 * Q)⁻¹ := by
          push_cast
          field_simp
        change (u' : ℝ) ≤ t - ((n + 1 : ℕ) : ℝ) / (10 * Q)
        rw [hn]
        linarith
      · intro v hv'v hvt
        exact hCbound v (hcv'.trans hv'v) hvt
      · change Q * (3 / 4) ^ (n + 1) ≤ metricScalarAt (H.stageMetric (H.activeStage v') v')
          (C.point (H.activeStage v') (H.activeStage_mono hcv') (H.activeStage_mono hv't))
        rw [BackwardPointTrace.concat_point_of_le B A' _ _ _ (H.activeStage_mono hv'w)]
        have hb := mul_sub_le_of_abs_inv_mul_sub_le hRpos (hA' v' hcv' hv'w)
        have hr1 : -(1 / 5 : ℝ) ≤ R * ((v' : ℝ) - w) := by
          have hmul := mul_le_mul_of_nonneg_left
            (show -(5 * R)⁻¹ ≤ (v' : ℝ) - w by change -(5 * R)⁻¹ ≤ (u' : ℝ) - w; linarith)
            hRpos.le
          have hq : R * -(5 * R)⁻¹ = -(1 / 5) := by field_simp
          linarith
        have hr0 : R * ((v' : ℝ) - w) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hRpos.le (by change (u' : ℝ) - w ≤ 0; linarith)
        have hc56 := five_div_six_le_inv_one_sub hr1 hr0
        calc Q * (3 / 4) ^ (n + 1) = (3 / 4) * (Q * (3 / 4) ^ n) := by ring
          _ ≤ (3 / 4) * R := mul_le_mul_of_nonneg_left hRlow (by norm_num)
          _ ≤ R * ((1 - R * ((v' : ℝ) - w))⁻¹ - 2400 * eps) := by nlinarith
          _ ≤ _ := hb
      · change metricScalarAt (H.stageMetric (H.activeStage v') v')
          (C.point (H.activeStage v') (H.activeStage_mono hcv') (H.activeStage_mono hv't)) ≤ Q
        rw [BackwardPointTrace.concat_point_of_le B A' _ _ _ (H.activeStage_mono hv'w)]
        have hb := le_mul_add_of_abs_inv_mul_sub_le hRpos (hA' v' hcv' hv'w)
        have hr : R * ((v' : ℝ) - w) ≤ -(1 / 10) := by
          have hmul := mul_le_mul_of_nonneg_left
            (show (v' : ℝ) - w ≤ -(10 * R)⁻¹ by change (u' : ℝ) - w ≤ -(10 * R)⁻¹; linarith)
            hRpos.le
          have hq : R * -(10 * R)⁻¹ = -(1 / 10) := by field_simp
          linarith
        have hc1011 := inv_one_sub_le_ten_div_eleven hr
        calc _ ≤ R * ((1 - R * ((v' : ℝ) - w))⁻¹ + 2400 * eps) := hb
          _ ≤ R * 1 := mul_le_mul_of_nonneg_left (by linarith) hRpos.le
          _ ≤ Q := by linarith
  have hall : ∀ n, Done ∨ Slice n := by
    intro n
    induction n with
    | zero => exact Or.inr hbase
    | succ n ih =>
      rcases ih with h | h
      · exact Or.inl h
      · exact hstep n h
  rcases hall (N + 1) with h | ⟨w, hwt, haw, -, hdepth, -⟩
  · exact h
  · exfalso
    have haw' : (a : ℝ) ≤ w := haw
    have h1 : ((N + 1 : ℕ) : ℝ) / (10 * Q) ≤ (t : ℝ) - a := by linarith
    rw [div_le_iff₀ h10Q] at h1
    have h2 := Nat.le_ceil (10 * Q * ((t : ℝ) - a))
    rw [← hNdef] at h2
    push_cast at h1
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable (H : RetainedCoreHistory.{u})

theorem isTracedRegion_of_hasStrongNeckAt {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {t : Icc (0 : ℝ) H.toHistory.horizon}
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (htop : H.time (H.toHistory.activeStage t) < t)
    {p : (H.toHistory.stageAt t).Carrier} {ρ T Qlow Qup L eps : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T)
    (hTt : T ≤ (t : ℝ)) (heps : eps ≤ 1 / 30000) (hL0 : 0 < L)
    (hlow : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
      Qlow ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x)
    (hup : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ Qup)
    (hL : L ≤ Qlow * (3 / 4) ^ ⌈10 * Qup * T⌉₊)
    (hsupply : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
      ∀ v : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) - T ≤ v → ∀ hvt : v ≤ t,
      H.time (H.toHistory.activeStage v) < v →
      ∀ B : BackwardPointTrace H.toHistory (H.toHistory.activeStage v)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hvt) x,
        L ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)) →
        H.toHistory.HasStrongNeckAt eps v
          (B.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt))) :
    H.toHistory.isTracedRegion t p ρ (T + (10 * Qup)⁻¹)
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * max Qup 1) := by
  let g := H.toHistory.stageMetric (H.toHistory.activeStage t) t
  let a : Icc (0 : ℝ) H.toHistory.horizon := ⟨t - T, by linarith, by linarith [t.2.2]⟩
  have hat : a ≤ t := show (t : ℝ) - T ≤ t by linarith
  have hpball : p ∈ riemannianBallOf g p ρ := by
    change riemannianEDistOf g p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hpow (n : ℕ) : 0 < ((3 : ℝ) / 4) ^ n := by positivity
  have hQlow : 0 < Qlow := by
    by_contra hq
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) (hpow ⌈10 * Qup * T⌉₊).le
    linarith
  have hQup : 0 < Qup := hQlow.trans_le ((hlow p hpball).trans (hup p hpball))
  have hengine (x : (H.toHistory.stageAt t).Carrier) (hx : x ∈ riemannianBallOf g p ρ) :=
    H.toHistory.exists_backwardPointTrace_scalar_le_of_hasStrongNeckAt heps hL0 hat htop
      (y := x) (by
        have hQx := hlow x hx
        have hQx' := hup x hx
        have hc : ⌈10 * metricScalarAt g x * ((t : ℝ) - a)⌉₊ ≤ ⌈10 * Qup * T⌉₊ := by
          apply Nat.ceil_mono
          change 10 * metricScalarAt g x * ((t : ℝ) - (t - T)) ≤ 10 * Qup * T
          have : (t : ℝ) - (t - T) = T := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (by linarith) hT
        have hp1 := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num) hc
        calc L ≤ Qlow * (3 / 4) ^ ⌈10 * Qup * T⌉₊ := hL
          _ ≤ metricScalarAt g x * (3 / 4) ^ ⌈10 * Qup * T⌉₊ :=
            mul_le_mul_of_nonneg_right hQx (hpow _).le
          _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (hQlow.le.trans hQx))
      (fun v hav hvt hev B hB => hsupply x hx v hav hvt hev B hB)
  have hQinv (x : (H.toHistory.stageAt t).Carrier) (hx : x ∈ riemannianBallOf g p ρ) :
      (10 * Qup)⁻¹ ≤ (10 * metricScalarAt g x)⁻¹ :=
    inv_anti₀ (by linarith [hlow x hx]) (by linarith [hup x hx])
  obtain ⟨bp, -, hbp, -⟩ := hengine p hpball
  have ha'0 : 0 ≤ (t : ℝ) - (T + (10 * Qup)⁻¹) := by
    have := bp.2.1
    have := hQinv p hpball
    change (bp : ℝ) = (t : ℝ) - T - (10 * metricScalarAt g p)⁻¹ at hbp
    linarith
  have hQi : 0 ≤ (10 * Qup)⁻¹ := inv_nonneg.mpr (by linarith)
  let a' : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨t - (T + (10 * Qup)⁻¹), ha'0, by linarith [t.2.2]⟩
  have ha't : a' ≤ t := show (t : ℝ) - (T + (10 * Qup)⁻¹) ≤ t by linarith
  refine ⟨hρ, by positivity, a', ha't, rfl, ?_⟩
  intro x hx
  obtain ⟨b, hbt, hb, A, hA⟩ := hengine x hx
  have hba' : b ≤ a' := by
    change (b : ℝ) ≤ (t : ℝ) - (T + (10 * Qup)⁻¹)
    change (b : ℝ) = (t : ℝ) - T - (10 * metricScalarAt g x)⁻¹ at hb
    linarith [hQinv x hx]
  let A' := A.restrictFirst (H.toHistory.activeStage_mono hba')
    (H.toHistory.activeStage_mono ha't)
  have hM : (1 : ℝ) ≤ max Qup 1 := le_max_right _ _
  have hscal : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a' ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A'.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * max Qup 1 := by
    intro v hav hvt
    have h := hA v (hba'.trans hav) hvt
    have hx' : metricScalarAt g x ≤ max Qup 1 := (hup x hx).trans (le_max_left _ _)
    exact h.trans (by linarith)
  obtain ⟨hall, hcross⟩ := H.normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul hphi hpinch
    ha't hlast A' hM hscal
  exact ⟨A', hall, hcross⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
