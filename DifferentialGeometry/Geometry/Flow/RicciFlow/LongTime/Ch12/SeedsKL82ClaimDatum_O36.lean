import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimTraced_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimSelect_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimGood_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimBlowVol_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82TraceScalar_CX11

/-!
# CH12-O36, G4b: blow-up datum of one claim-(C) counterexample

For a counterexample to claim (C) with constants `C₀ = B₀ = N` (D-R4-6: the sequence uses
`N = n + 1`): window-start device (`exists_late_bad_start_O30` + `kl82_good_mono_O30`, with
`η = N/(2 Rmax)`, `Rmax` from the `K`-traces), point selection `kl82_select_O30` on
`Σ v, carrier` (`κ = r0⁻²`, `C = B = N`, `r = 7r0/16`, `m = r0/16`), then
`kl82_blowup_traced_O36` (centre `X`, `a_* = t_* − T/Q`, `R0 = d_* + ℓ/4`) and
`kl82_selected_volume_O30` + `blowup_volume_of_local_O30` (`r1 = 15r0/32`, `r2 = 17r0/32`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **G4b.** The blow-up datum of one claim-(C) counterexample with constants `N`. -/
theorem kl82_blowup_datum_O36 (N : ℝ) (hN : 1 ≤ N) :
    ∃ τw : ℝ, 0 < τw ∧ τw ≤ 1 ∧
      ∀ (w : ℝ) (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon)
        (x0 : (H.stageAt top).Carrier) (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0),
        0 < w → 0 < r0 → 0 < τ → τ ≤ τw → (a : ℝ) = top - τ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        (∃ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v ∧
          ∃ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (3 * r0 / 8),
            N * (r0 ^ 2)⁻¹ + N * ((v : ℝ) - a)⁻¹ <
              metricScalarAt (H.stageMetric (H.activeStage v) v) q) →
        ∃ (ts : Icc (0 : ℝ) H.horizon) (y : (H.stageAt ts).Carrier) (Q : ℝ), 0 < Q ∧
          metricScalarAt (H.stageMetric (H.activeStage ts) ts) y = Q ∧ N ≤ Q * r0 ^ 2 ∧
          (∀ Aa T : ℝ, 0 < Aa → 0 < T → 8192 * (Aa + 16 * T + 1) ^ 2 < N → 2 * T ≤ N →
            H.isTracedRegion ts y (Aa / Real.sqrt Q) (T / Q) (8 * Real.sqrt 3 * Q) ∧
            ∀ (a'' : Icc (0 : ℝ) H.horizon) (ha'' : a'' ≤ ts), (a'' : ℝ) = ts - T / Q →
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage ts) ts) y (Aa / Real.sqrt Q),
              ∀ Y : BackwardPointTrace H (H.activeStage a'') (H.activeStage ts)
                  (H.activeStage_mono ha'') q,
              ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a'' ≤ v) (hvt : v ≤ ts),
                SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v)
                  (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
                  (-(r0 ^ 2)⁻¹)) ∧
          ∀ (D : ℝ) (hQ : 0 < Q), 0 < D → 1024 * D ^ 2 ≤ N →
            ∀ x ∈ riemannianClosedBallOf
                (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts)) y D,
            ∀ s : ℝ, 0 < s → s ≤ D →
              ENNReal.ofReal (w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16) * s ^ 3) ≤
                Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt ts).Carrier
                  (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts))
                  (riemannianBallOf (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts)) x s) := by
  classical
  have hN0 : 0 < N := by linarith
  obtain ⟨τw, hτw, hτw1, hV⟩ :=
    kl82_selected_volume_O30.{u} dist_trace_boot_S68.{u} N N hN0.le hN0.le
  refine ⟨τw, hτw, hτw1, ?_⟩
  intro w H top x0 r0 τ K a hat X hw hr0 hτ hττ ha hSF hsec hvol hbad
  have hκ : 0 < (r0 ^ 2)⁻¹ := by positivity
  -- scalar bound from the `K`-traces
  set Rmax : ℝ := max (9 * |K|) 1 with hRmax
  have hRmax0 : 0 < Rmax := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRle : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ Rmax := by
    intro v hav hvt z hz
    obtain ⟨A, hA⟩ := hSF v hav hvt z hz
    exact (le_abs_self _).trans ((scalar_abs_le_of_bounded_trace_CX11 H A hA).trans
      (le_max_left _ _))
  -- window device
  let good : ℝ → Prop := fun s => ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
    s < (v : ℝ) → ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
        (3 * r0 / 8),
      metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ N * (r0 ^ 2)⁻¹ + N * ((v : ℝ) - s)⁻¹
  have hη : 0 < N / (2 * Rmax) := by positivity
  obtain ⟨a', ha'a, ha'top, hbad', hgood⟩ := exists_late_bad_start_O30 good hη
    (show (a : ℝ) ≤ top from hat)
    (fun s s' hss hs => kl82_good_mono_O30 H top a hat X hN0.le hss hs)
    (fun v _ hvt hlt => absurd hvt (not_le.mpr hlt))
    (fun hg => by
      obtain ⟨v, hav, hvt, hav', q, hq, hlt⟩ := hbad
      exact absurd (hg v hav hvt hav' q hq) (not_le.mpr hlt))
  -- the seed
  simp only [good, not_forall, not_le, exists_prop] at hbad'
  obtain ⟨v0, hav0, hvt0, hv0, q0, hq0, hlt0⟩ := hbad'
  -- selection on `Σ v, carrier`
  let P := Σ v : Icc (0 : ℝ) H.horizon, (H.stageAt v).Carrier
  let ed : P → ℝ≥0∞ := fun p => if h : a ≤ p.1 ∧ p.1 ≤ top then
    riemannianEDistOf (H.stageMetric (H.activeStage p.1) p.1)
      (X.point (H.activeStage p.1) (H.activeStage_mono h.1) (H.activeStage_mono h.2)) p.2 else ⊤
  let TT : Set P := {p | a' < (p.1 : ℝ) ∧ a ≤ p.1 ∧ p.1 ≤ top ∧ ed p < ENNReal.ofReal (7 * r0 / 16)}
  let T0 : Set P := {p | a' < (p.1 : ℝ) ∧ a ≤ p.1 ∧ p.1 ≤ top ∧ ed p < ENNReal.ofReal (3 * r0 / 8)}
  let tm : P → ℝ := fun p => p.1
  let RR : P → ℝ := fun p => metricScalarAt (H.stageMetric (H.activeStage p.1) p.1) p.2
  let dd : P → ℝ := fun p => (ed p).toReal
  have hed : ∀ (p : P) (h1 : a ≤ p.1) (h2 : p.1 ≤ top), ed p = riemannianEDistOf
      (H.stageMetric (H.activeStage p.1) p.1)
      (X.point (H.activeStage p.1) (H.activeStage_mono h1) (H.activeStage_mono h2)) p.2 :=
    fun p h1 h2 => by simp only [ed, h1, h2, and_self, dite_true]
  have h716 : ENNReal.ofReal (7 * r0 / 16) ≤ ENNReal.ofReal r0 :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hTT : ∀ p ∈ TT, a' < tm p ∧ 0 ≤ dd p ∧ dd p < 7 * r0 / 16 :=
    fun p hp => ⟨hp.1, ENNReal.toReal_nonneg, ENNReal.toReal_lt_of_lt_ofReal hp.2.2.2⟩
  have hsel := kl82_select_O30 TT T0 tm RR dd (a := a') (κ := (r0 ^ 2)⁻¹) (C := N) (B := N)
    (r := 7 * r0 / 16) (m := r0 / 16) hκ hN0 hN0 (by positivity)
    (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))⟩) hTT
    (fun p hp => by
      have := ENNReal.toReal_lt_of_lt_ofReal hp.2.2.2
      change dd p + r0 / 16 ≤ 7 * r0 / 16
      linarith)
    ⟨Rmax, by
      rintro _ ⟨p, hp, rfl⟩
      exact hRle p.1 hp.2.1 hp.2.2.1 p.2 (by
        have := hp.2.2.2; rw [hed p hp.2.1 hp.2.2.1] at this; exact this.trans_le h716)⟩
    ⟨⟨v0, q0⟩, ⟨hv0, hav0, hvt0, by rw [hed _ hav0 hvt0]; exact hq0⟩, by
      change N * (r0 ^ 2)⁻¹ + N / ((v0 : ℝ) - a') < RR ⟨v0, q0⟩
      rw [div_eq_mul_inv]; exact hlt0⟩
  obtain ⟨x, hxT, hs1, hs2, -, hs4⟩ := hsel
  have hxa1 : a ≤ x.1 := hxT.2.1
  have hxt1 : x.1 ≤ top := hxT.2.2.1
  have hxe : ed x < ENNReal.ofReal (7 * r0 / 16) := hxT.2.2.2
  set Q : ℝ := RR x with hQdef
  set ds : ℝ := dd x with hdsdef
  have hxa : a' < (x.1 : ℝ) := hxT.1
  have hds0 : 0 ≤ ds := ENNReal.toReal_nonneg
  have hds7 : ds < 7 * r0 / 16 := (hTT x hxT).2.2
  have htpos : 0 < (x.1 : ℝ) - a' := by linarith
  have hNdiv : 0 < N / ((x.1 : ℝ) - a') := div_pos hN0 htpos
  have hQ : 0 < Q := by
    have : 0 < N * (r0 ^ 2)⁻¹ := by positivity
    change N * (r0 ^ 2)⁻¹ + N / ((x.1 : ℝ) - a') < Q at hs1
    linarith
  have hNQ : N ≤ Q * r0 ^ 2 := by
    have h1 : N * (r0 ^ 2)⁻¹ < Q := by
      change N * (r0 ^ 2)⁻¹ + N / ((x.1 : ℝ) - a') < Q at hs1; linarith
    have hr2 : 0 < r0 ^ 2 := by positivity
    have := (mul_lt_mul_of_pos_right h1 hr2)
    rw [mul_assoc, inv_mul_cancel₀ hr2.ne', mul_one] at this
    exact this.le
  have hκQ : (r0 ^ 2)⁻¹ ≤ Q := by
    have hr2 : 0 < r0 ^ 2 := by positivity
    rw [inv_le_iff_one_le_mul₀ hr2, mul_comm]; linarith
  -- time gap `t_* − a' > N/Q`
  have hgap : N / Q < (x.1 : ℝ) - a' := by
    change N * (r0 ^ 2)⁻¹ + N / ((x.1 : ℝ) - a') < Q at hs1
    have h1 : N / ((x.1 : ℝ) - a') < Q := by
      have : 0 < N * (r0 ^ 2)⁻¹ := by positivity
      linarith
    rw [div_lt_iff₀ htpos] at h1
    rw [div_lt_iff₀ hQ]; linarith
  have hQRmax : Q ≤ Rmax := hRle x.1 hxa1 hxt1 x.2 (by
    have := hxe; rw [hed x hxa1 hxt1] at this; exact this.trans_le h716)
  have hgoodx : good x.1 := by
    apply hgood
    have : N / (2 * Rmax) ≤ N / Q := by
      apply div_le_div_of_nonneg_left hN0.le hQ; linarith
    linarith
  have hyX : riemannianEDistOf (H.stageMetric (H.activeStage x.1) x.1)
      (X.point (H.activeStage x.1) (H.activeStage_mono hxa1) (H.activeStage_mono hxt1))
      x.2 < ENNReal.ofReal (7 * r0 / 16) := by
    have := hxe; rwa [hed x hxa1 hxt1] at this
  have hyds : riemannianEDistOf (H.stageMetric (H.activeStage x.1) x.1)
      (X.point (H.activeStage x.1) (H.activeStage_mono hxa1) (H.activeStage_mono hxt1))
      x.2 ≤ ENNReal.ofReal ds := by
    have hdsE : ds = (riemannianEDistOf (H.stageMetric (H.activeStage x.1) x.1)
        (X.point (H.activeStage x.1) (H.activeStage_mono hxa1) (H.activeStage_mono hxt1))
        x.2).toReal := by
      rw [hdsdef]; exact congrArg ENNReal.toReal (hed x hxa1 hxt1)
    rw [hdsE, ENNReal.ofReal_toReal (ne_top_of_lt hyX)]
  refine ⟨x.1, x.2, Q, hQ, rfl, hNQ, ?_, ?_⟩
  · intro Aa T hAa hT hNA hNT
    have hTQ : T / Q ≤ N / (2 * Q) := by
      rw [div_le_div_iff₀ hQ (by positivity)]; nlinarith
    have hNQ2 : N / (2 * Q) < N / Q := by
      apply div_lt_div_of_pos_left hN0 hQ; linarith
    have has0 : (a' : ℝ) < (x.1 : ℝ) - T / Q := by linarith
    have hasa : (a : ℝ) ≤ (x.1 : ℝ) - T / Q := by linarith
    let as : Icc (0 : ℝ) H.horizon := ⟨(x.1 : ℝ) - T / Q, a.2.1.trans hasa,
      (by have := div_pos hT hQ; linarith [x.1.2.2])⟩
    have has : a ≤ as := hasa
    have hast : as ≤ x.1 := by
      change (x.1 : ℝ) - T / Q ≤ x.1; linarith [div_pos hT hQ]
    -- margin from the selection
    have hℓ : 0 < 7 * r0 / 16 - ds := by linarith
    have hmarg : ds + (Aa + 16 * T + 1) / Real.sqrt Q < ds + (7 * r0 / 16 - ds) / 4 := by
      have hs2' : N * (r0 ^ 2)⁻¹ * (r0 / 16) ^ 2 / 2 < Q * (7 * r0 / 16 - ds) ^ 2 := hs2
      have he : N * (r0 ^ 2)⁻¹ * (r0 / 16) ^ 2 / 2 = N / 512 := by
        field_simp; ring
      rw [he] at hs2'
      have hsq : (4 * (Aa + 16 * T + 1)) ^ 2 < (Real.sqrt Q * (7 * r0 / 16 - ds)) ^ 2 := by
        have he2 : (Real.sqrt Q * (7 * r0 / 16 - ds)) ^ 2 = Q * (7 * r0 / 16 - ds) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hQ.le]
        rw [he2]; nlinarith
      have hlt := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
      have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
      have : (Aa + 16 * T + 1) / Real.sqrt Q < (7 * r0 / 16 - ds) / 4 := by
        rw [div_lt_div_iff₀ hsQ (by norm_num)]; linarith
      linarith
    have hR0 : ds + (7 * r0 / 16 - ds) / 4 ≤ r0 / 2 := by linarith only [hds7, hds0, hr0]
    have hwin : ((x.1 : Icc (0 : ℝ) H.horizon) : ℝ) - (as : ℝ) = T / Q := by
      change (x.1 : ℝ) - ((x.1 : ℝ) - T / Q) = T / Q; ring
    have hRx : RR x = Q := rfl
    have hscal' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : as ≤ v) (hvt : v ≤ x.1),
        ∀ z : (H.stageAt v).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono (has.trans hav))
              (H.activeStage_mono (hvt.trans hxt1))) z <
            ENNReal.ofReal (ds + (7 * r0 / 16 - ds) / 4) →
          metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ 4 * Q := by
      intro v hav hvt z hz
      have hav' : (x.1 : ℝ) - T / Q ≤ v := hav
      have hR0lt : ds + (7 * r0 / 16 - ds) / 4 < 7 * r0 / 16 := by linarith only [hds7]
      have hedv := hed ⟨v, z⟩ (has.trans hav) (hvt.trans hxt1)
      have hvT : (⟨v, z⟩ : P) ∈ TT := by
        refine ⟨lt_of_lt_of_le has0 hav', has.trans hav, hvt.trans hxt1, ?_⟩
        rw [hedv]
        exact hz.trans_le (ENNReal.ofReal_le_ofReal hR0lt.le)
      have htime : tm x - N / (2 * RR x) ≤ tm ⟨v, z⟩ := by
        change (x.1 : ℝ) - N / (2 * Q) ≤ v
        linarith only [hav', hTQ]
      have hdist : dd ⟨v, z⟩ ≤ dd x + (7 * r0 / 16 - dd x) / 4 := by
        change (ed ⟨v, z⟩).toReal ≤ ds + (7 * r0 / 16 - ds) / 4
        rw [hedv]
        exact ENNReal.toReal_le_of_le_ofReal (by linarith only [hds0, hds7]) hz.le
      exact hs4 ⟨v, z⟩ hvT htime hdist
    exact kl82_blowup_traced_O36 H hat X hr0 hSF hsec has hast hxt1 hQ hκQ hT hAa hds0
      hwin hyds hmarg hR0 hscal'
  · intro D hQ' hD hND x' hx' s hs hsD
    have hvolx := hV H top x0 r0 τ K w a hat X hw hr0 hτ hττ ha hSF hsec hvol x.1 hxa1 hxt1
      hgoodx
    have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
    have hDQ : D / Real.sqrt Q ≤ r0 / 32 := by
      rw [div_le_iff₀ hsQ]
      have he : (r0 / 32 * Real.sqrt Q * 32) ^ 2 = Q * r0 ^ 2 := by
        rw [show r0 / 32 * Real.sqrt Q * 32 = r0 * Real.sqrt Q by ring, mul_pow,
          Real.sq_sqrt hQ.le]
        ring
      have h1 : (32 * D) ^ 2 ≤ (r0 / 32 * Real.sqrt Q * 32) ^ 2 := by
        rw [he, show (32 * D) ^ 2 = 1024 * D ^ 2 by ring]
        linarith only [hND, hNQ]
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_sq (by linarith only [hD] : (0 : ℝ) ≤ 32 * D),
        Real.sqrt_sq (mul_nonneg (mul_nonneg (by linarith only [hr0]) (Real.sqrt_nonneg Q))
          (by norm_num) : (0 : ℝ) ≤ r0 / 32 * Real.sqrt Q * 32)] at h2
      linarith only [h2]
    refine blowup_volume_of_local_O30 (H.stageMetric (H.activeStage x.1) x.1)
      (X.point (H.activeStage x.1) (H.activeStage_mono hxa1) (H.activeStage_mono hxt1))
      x.2 (c := w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16)) (r1 := 15 * r0 / 32)
      (r2 := 17 * r0 / 32) hQ'
      (hyX.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hDQ])))
      (by linarith only [hDQ, hr0]) (fun z hz ρ hρ hρr => ?_) x' hx' s hs hsD
    have hc : w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16) * ρ ^ 3 =
        w / 10 * (2 / 17) ^ 3 * ρ ^ 3 / Real.exp (25 / 16) := by ring
    rw [hc]
    exact hvolx z hz ρ hρ hρr

end GC.LongTime.Ch12
