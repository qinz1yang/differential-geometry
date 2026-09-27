import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckDepthInduction

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_isTracedRegion_of_forall_neckAlternative_of_staggered_supply
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
    (htopneck : ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        c * R n ≤ metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) x →
        ∀ W : SpatialCanonicalWitness
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) ε C1 C2 x,
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk)
    (hdeep : ∀ T : ℝ, 0 < T →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n) (K * R n)) →
      ∀ T' : ℝ, 0 ≤ T' → T' < T → ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
            (A / Real.sqrt (R n)),
        ∀ v : Icc (0 : ℝ) (H n).toHistory.horizon, (t n : ℝ) - T' / R n ≤ v →
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
  have hδ : 0 < (10 * Qup)⁻¹ := by positivity
  have step : ∀ T' : ℝ, 0 ≤ T' →
      (∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
            (A / Real.sqrt (R n)),
        ∀ v : Icc (0 : ℝ) (H n).toHistory.horizon, (t n : ℝ) - T' / R n ≤ v →
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
              ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) →
      ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n))
          ((T' + (10 * Qup)⁻¹) / R n)
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup * R n) := by
    intro T' hT' hsup A hA
    obtain ⟨Qlow, hQlow, hbA⟩ := hball A hA
    have hc : 0 < Qlow * (3 / 4) ^ ⌈10 * Qup * T'⌉₊ := by positivity
    filter_upwards [hbA, hsup A _ hA hc, hq _ hc, hRpos, hRlim.eventually_ge_atTop Qup⁻¹,
      hRt.eventually_ge_atTop T'] with n hbn hSn hqn hRn hR1 hRtn
    have hR1' : 1 ≤ Qup * R n := by
      have := mul_le_mul_of_nonneg_left hR1 hQup.le
      rwa [mul_inv_cancel₀ hQup.ne'] at this
    have hceil : 10 * (Qup * R n) * (T' / R n) = 10 * Qup * T' := by
      field_simp
    have h := (H n).isTracedRegion_of_forall_neckAlternative hphi (hpinch n) hε₁ (hclass n)
      (hlast n) (htop n) (ρ := A / Real.sqrt (R n)) (T := T' / R n) (Qlow := Qlow * R n)
      (Qup := Qup * R n) (L := Qlow * (3 / 4) ^ ⌈10 * Qup * T'⌉₊ * R n) (by positivity)
      (by positivity) ((div_le_iff₀ hRn).mpr (by linarith [hRtn])) (by positivity) hqn
      (fun x hx => (hbn x hx).1) (fun x hx => (hbn x hx).2) (le_of_eq (by rw [hceil]; ring))
      (fun v _ hvt hev hl => hterm n v hvt hev hl)
      (fun x hx v hav hvt hev B hB => hSn x hx v hav hvt hev B hB)
    refine h.mono (by positivity) le_rfl (by positivity) (le_of_eq ?_) (by positivity)
      (le_of_eq ?_)
    · field_simp
    · rw [max_eq_left hR1']
      ring
  have htop0 : ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
      ∀ v : Icc (0 : ℝ) (H n).toHistory.horizon, (t n : ℝ) - 0 / R n ≤ v →
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
            ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
    intro A c hA hc
    filter_upwards [htopneck A c hA hc] with n hn
    intro x hx v hv1 hvt _ B hB W hW
    have hvt' : v = t n := Subtype.ext (le_antisymm hvt (by simpa using hv1))
    subst hvt'
    have hpt : B.point ((H n).toHistory.activeStage (t n)) le_rfl
        ((H n).toHistory.activeStage_mono hvt) = x := B.endpoint_eq
    rw [hpt] at hB
    revert W
    rw [hpt]
    exact fun W hW => hn x hx hB W hW
  have claim : ∀ m : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
      (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n))
        (((10 * Qup)⁻¹ + (m : ℝ) * ((10 * Qup)⁻¹ / 2)) / R n)
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup * R n) := by
    intro m
    induction m with
    | zero =>
      intro A hA
      have h := step 0 le_rfl htop0 A hA
      simpa using h
    | succ m ih =>
      intro A hA
      have hTm : 0 < (10 * Qup)⁻¹ + (m : ℝ) * ((10 * Qup)⁻¹ / 2) := by positivity
      have hprem : ∃ K : ℝ, 0 ≤ K ∧ ∀ A' T' : ℝ, 0 < A' → 0 < T' →
          T' ≤ (10 * Qup)⁻¹ + (m : ℝ) * ((10 * Qup)⁻¹ / 2) → ∀ᶠ n in atTop,
            (H n).toHistory.isTracedRegion (t n) (y n) (A' / Real.sqrt (R n)) (T' / R n)
              (K * R n) := by
        refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup, by positivity, ?_⟩
        intro A' T' hA' hT' hle
        filter_upwards [ih A' hA', hRpos] with n hn hRn
        exact hn.mono_depth (by positivity) (div_le_div_of_nonneg_right hle hRn.le)
      have hsup := hdeep _ hTm hprem ((10 * Qup)⁻¹ / 2 + (m : ℝ) * ((10 * Qup)⁻¹ / 2))
        (by positivity) (by linarith)
      have h := step _ (by positivity) hsup A hA
      have e : (10 * Qup)⁻¹ / 2 + (m : ℝ) * ((10 * Qup)⁻¹ / 2) + (10 * Qup)⁻¹ =
          (10 * Qup)⁻¹ + ((m + 1 : ℕ) : ℝ) * ((10 * Qup)⁻¹ / 2) := by
        push_cast
        ring
      rwa [e] at h
  intro A T hA hT
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Qup, by positivity, ?_⟩
  have hm : T ≤ (10 * Qup)⁻¹ + ((⌈T / ((10 * Qup)⁻¹ / 2)⌉₊ : ℝ)) * ((10 * Qup)⁻¹ / 2) := by
    have h1 := Nat.le_ceil (T / ((10 * Qup)⁻¹ / 2))
    have h2 : T / ((10 * Qup)⁻¹ / 2) * ((10 * Qup)⁻¹ / 2) = T := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (10 * Qup)⁻¹ / 2)]
  filter_upwards [claim ⌈T / ((10 * Qup)⁻¹ / 2)⌉₊ A hA, hRpos] with n hn hRn
  exact hn.mono_depth (by positivity) (div_le_div_of_nonneg_right hm hRn.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
