import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckClassSupply

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

section Single

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

theorem hasStrongNeckAt_of_forall_neckAlternative {ε ε₁ C1 C2 qcan : ℝ}
    (hclass : H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount))
    (v : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt v).Carrier)
    (hev : H.time (H.toHistory.activeStage v) < v)
    (hterm : H.toHistory.activeStage v = Fin.last H.eventCount →
      ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
          (H.time (H.toHistory.activeStage v)) s),
        (v : ℝ) < s ∧
        (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
          G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
        H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s)
    (hq : qcan < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p)
    (hneck : ∀ W : SpatialCanonicalWitness
        (H.toHistory.stageMetric (H.toHistory.activeStage v) v) ε C1 C2 p,
      W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) :
    H.toHistory.HasStrongNeckAt ε₁ v p := by
  obtain ⟨s, G, hvs, hG, hbefore⟩ := H.exists_currentSlab_stronglyCanonicalBefore hclass v hterm
  have hGv : G.flow.base.metric v = H.toHistory.stageMetric (H.toHistory.activeStage v) v :=
    hG v ⟨H.toHistory.activeStage_time_le v, le_rfl⟩
  have hq' : qcan < G.flow.scalar v p := by
    change qcan < metricScalarAt (G.flow.base.metric v) p
    rw [hGv]
    exact hq
  obtain ⟨W, hW, himp⟩ := hbefore p v ⟨hev, hvs⟩ hq'
  have key : ∀ g, g = H.toHistory.stageMetric (H.toHistory.activeStage v) v →
      ∀ W' : SpatialCanonicalWitness g ε C1 C2 p, W'.capTubeHasNeckChart ε →
        ∃ nk, W'.alternative = SpatialCanonicalAlternative.neck nk := by
    rintro g rfl W' hW'
    exact hneck W' hW'
  exact ⟨s, G, hvs, hG, himp (key _ hGv W hW)⟩

theorem isTracedRegion_of_forall_neckAlternative {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {ε ε₁ C1 C2 qcan : ℝ} (hε₁ : ε₁ ≤ 1 / 30000)
    (hclass : H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount))
    {t : Icc (0 : ℝ) H.toHistory.horizon}
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (htop : H.time (H.toHistory.activeStage t) < t)
    {p : (H.toHistory.stageAt t).Carrier} {ρ T Qlow Qup L : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T)
    (hTt : T ≤ (t : ℝ)) (hL0 : 0 < L) (hqL : qcan < L)
    (hlow : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
      Qlow ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x)
    (hup : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ Qup)
    (hL : L ≤ Qlow * (3 / 4) ^ ⌈10 * Qup * T⌉₊)
    (hterm : ∀ v : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) - T ≤ v → v ≤ t →
      H.time (H.toHistory.activeStage v) < v →
      H.toHistory.activeStage v = Fin.last H.eventCount →
        ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
            (H.time (H.toHistory.activeStage v)) s),
          (v : ℝ) < s ∧
          (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
            G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
          H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s)
    (hneck : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
      ∀ v : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) - T ≤ v → ∀ hvt : v ≤ t,
      H.time (H.toHistory.activeStage v) < v →
      ∀ B : BackwardPointTrace H.toHistory (H.toHistory.activeStage v)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hvt) x,
        L ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)) →
        ∀ W : SpatialCanonicalWitness (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ε C1 C2
            (B.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)),
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) :
    H.toHistory.isTracedRegion t p ρ (T + (10 * Qup)⁻¹)
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * max Qup 1) := by
  apply H.isTracedRegion_of_hasStrongNeckAt hphi hpinch hlast htop hρ hT hTt hε₁ hL0 hlow hup hL
  intro x hx v hav hvt hev B hB
  exact H.hasStrongNeckAt_of_forall_neckAlternative hclass v _ hev (hterm v hav hvt hev)
    (hqL.trans_le hB) (hneck x hx v hav hvt hev B hB)

end Single

theorem exists_isTracedRegion_of_forall_neckAlternative_of_depth_induction
    {P₀ : ℕ → OrientedThreeStage.{u}} (H : ∀ n, RetainedCoreHistory (P₀ n))
    (t : ∀ n, Icc (0 : ℝ) (H n).toHistory.horizon)
    (y : ∀ n, ((H n).toHistory.stageAt (t n)).Carrier) (R : ℕ → ℝ)
    (hRlim : Tendsto R atTop atTop) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hlast : ∀ n, (H n).toHistory.activeStage (t n) = Fin.last (H n).eventCount →
      ∃ h : (H n).time (Fin.last (H n).eventCount) < (H n).horizon,
        Perelman.PhiAlmostNonnegative ((H n).finalSlab h).flow
          (Icc ((H n).time (Fin.last (H n).eventCount)) (H n).horizon) phi)
    (htop : ∀ n, (H n).time ((H n).toHistory.activeStage (t n)) < t n)
    {ε ε₁ C1 C2 : ℝ} {qcan : ℕ → ℝ} (hε₁ : ε₁ ≤ 1 / 30000)
    (hq : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, qcan n < c * R n)
    (hclass : ∀ n,
      (H n).EventSlabsStronglyCanonical ε ε₁ C1 C2 (qcan n) (Fin.last (H n).eventCount))
    (hterm : ∀ n (v : Icc (0 : ℝ) (H n).toHistory.horizon), v ≤ t n →
      (H n).time ((H n).toHistory.activeStage v) < v →
      (H n).toHistory.activeStage v = Fin.last (H n).eventCount →
        ∃ (s : ℝ) (G : ((H n).stage ((H n).toHistory.activeStage v)).IncomingSlab
            ((H n).time ((H n).toHistory.activeStage v)) s),
          (v : ℝ) < s ∧
          (∀ τ ∈ Icc ((H n).time ((H n).toHistory.activeStage v)) (v : ℝ),
            G.flow.base.metric τ =
              (H n).toHistory.stageMetric ((H n).toHistory.activeStage v) τ) ∧
          (H n).StronglyCanonicalBefore ((H n).toHistory.activeStage v) G ε ε₁ C1 C2 (qcan n) s)
    {Qup : ℝ}
    (hball : ∀ A : ℝ, 0 < A → ∃ Qlow : ℝ, 0 < Qlow ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        Qlow * R n ≤ metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) x ∧
          metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) x ≤
              Qup * R n)
    (hsupply : ∀ T : ℝ, 0 ≤ T →
      (∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n) (K * R n)) →
      ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
            (A / Real.sqrt (R n)),
        ∀ v : Icc (0 : ℝ) (H n).toHistory.horizon, (t n : ℝ) - T / R n ≤ v →
        ∀ hvt : v ≤ t n, (H n).time ((H n).toHistory.activeStage v) < v →
        ∀ B : BackwardPointTrace (H n).toHistory ((H n).toHistory.activeStage v)
            ((H n).toHistory.activeStage (t n)) ((H n).toHistory.activeStage_mono hvt) x,
          c * R n ≤ metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v)
            (B.point ((H n).toHistory.activeStage v) le_rfl
              ((H n).toHistory.activeStage_mono hvt)) →
          ∀ W : SpatialCanonicalWitness
              ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v) ε C1 C2
              (B.point ((H n).toHistory.activeStage v) le_rfl
                ((H n).toHistory.activeStage_mono hvt)),
            W.capTubeHasNeckChart ε →
              ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) :
    ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n) := by
  have hRpos : ∀ᶠ n in atTop, 0 < R n := hRlim.eventually_gt_atTop 0
  have hQup : 0 < Qup := by
    obtain ⟨Qlow, hQlow, hb⟩ := hball 1 one_pos
    obtain ⟨n, hn, hRn⟩ := (hb.and hRpos).exists
    have hy : y n ∈ riemannianBallOf
        ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
        (1 / Real.sqrt (R n)) := by
      change riemannianEDistOf _ (y n) (y n) < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have h := hn (y n) hy
    by_contra hneg
    nlinarith [h.1, h.2]
  have hphi0 : 0 ≤ 1 + phi 1 + phi 0 := by linarith [hphi.pos 1, hphi.pos 0]
  have step : ∀ T : ℝ, 0 ≤ T →
      (∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n)
          (K * R n)) →
      ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n))
          ((T + (10 * Qup)⁻¹) / R n)
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup * R n) := by
    intro T hT hprev A hA
    obtain ⟨Qlow, hQlow, hbA⟩ := hball A hA
    have hc : 0 < Qlow * (3 / 4) ^ ⌈10 * Qup * T⌉₊ := by positivity
    filter_upwards [hbA, hsupply T hT hprev A _ hA hc, hq _ hc, hRpos,
      hRlim.eventually_ge_atTop Qup⁻¹, hRt.eventually_ge_atTop T] with n hbn hSn hqn hRn hR1 hRtn
    have hR1' : 1 ≤ Qup * R n := by
      have := mul_le_mul_of_nonneg_left hR1 hQup.le
      rwa [mul_inv_cancel₀ hQup.ne'] at this
    have hceil : 10 * (Qup * R n) * (T / R n) = 10 * Qup * T := by
      field_simp
    have h := (H n).isTracedRegion_of_forall_neckAlternative hphi (hpinch n) hε₁ (hclass n)
      (hlast n) (htop n) (ρ := A / Real.sqrt (R n)) (T := T / R n) (Qlow := Qlow * R n)
      (Qup := Qup * R n) (L := Qlow * (3 / 4) ^ ⌈10 * Qup * T⌉₊ * R n) (by positivity)
      (by positivity) ((div_le_iff₀ hRn).mpr (by linarith [hRtn])) (by positivity) hqn
      (fun x hx => (hbn x hx).1) (fun x hx => (hbn x hx).2) (le_of_eq (by rw [hceil]; ring))
      (fun v _ hvt hev hl => hterm n v hvt hev hl)
      (fun x hx v hav hvt hev B hB => hSn x hx v hav hvt hev B hB)
    refine h.mono (by positivity) le_rfl (by positivity) (le_of_eq ?_) (by positivity)
      (le_of_eq ?_)
    · field_simp
    · rw [max_eq_left hR1']
      ring
  have claim : ∀ m : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
      (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n))
        (((m : ℝ) + 1) * (10 * Qup)⁻¹ / R n)
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup * R n) := by
    intro m
    induction m with
    | zero =>
      intro A hA
      have h := step 0 le_rfl (fun _ _ _ hT' hle => absurd hle (not_le.mpr hT')) A hA
      simpa using h
    | succ m ih =>
      intro A hA
      have hprev : ∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ ((m : ℝ) + 1) * (10 * Qup)⁻¹ →
          ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
            (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n)
              (K * R n) := by
        intro A' T' hA' hT' hle
        refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup, by positivity, ?_⟩
        filter_upwards [ih A' hA', hRpos] with n hn hRn
        exact hn.mono_depth (by positivity) (div_le_div_of_nonneg_right hle hRn.le)
      have h := step (((m : ℝ) + 1) * (10 * Qup)⁻¹) (by positivity) hprev A hA
      have e : ((m : ℝ) + 1) * (10 * Qup)⁻¹ + (10 * Qup)⁻¹ =
          (((m + 1 : ℕ) : ℝ) + 1) * (10 * Qup)⁻¹ := by
        push_cast
        ring
      rwa [e] at h
  intro A T hA hT
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup, by positivity, ?_⟩
  have hm : T ≤ ((⌈T * (10 * Qup)⌉₊ : ℝ) + 1) * (10 * Qup)⁻¹ := by
    have h1 := Nat.le_ceil (T * (10 * Qup))
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith
  filter_upwards [claim ⌈T * (10 * Qup)⌉₊ A hA, hRpos] with n hn hRn
  exact hn.mono_depth (by positivity) (div_le_div_of_nonneg_right hm hRn.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
