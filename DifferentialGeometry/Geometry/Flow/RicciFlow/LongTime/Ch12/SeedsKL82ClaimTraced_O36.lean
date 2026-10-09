import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimTerminal_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimBuffer_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimRmBound_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimWindow_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82DistBoot_S68

/-!
# CH12-O36, G4a: traced region and sectional bound at the blow-up scale

Given the claim-(C) counterexample data (the `K`-traces `hSF` and `sec ≥ -r0⁻²` on the
`r0`-balls around the base trace `X`), a window `[as, ts]` of length `T/Q`, a point `y` with
`d_ts(X(ts), y) ≤ ds`, the D-R4-6 margin `ds + (Aa + 16T + 1)/√Q < R0 ≤ r0/2`, and the selection
bound `R ≤ 4Q` on the `R0`-balls around `X(v)`, every point of `B_ts(y, Aa/√Q)` has a trace from
`as` with `|Rm| ≤ 8√3·Q` (`isTracedRegion`), and every trace from `as` of such a point stays in the
`r0`-ball where `sec ≥ -r0⁻²`.  Distance: `kl82_trace_buffer_O30` with `hboot :=
dist_trace_boot_S68`, `Λ = 4Q`, `C = 3T`, `ρ = r0`; curvature: `rm_normSq_le_of_sec_O30`; the
event-terminal clause: `isRmBoundedBy_of_stage_O36`.
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

/-- D-R4-6 error identity: with `C = 3T` and window `T/Q` the `hboot` error is `(16T+1)/√Q`. -/
theorem kl82_boot_error_O36 {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T) :
    16 * Real.sqrt (3 * T / 3) * Real.sqrt (T / Q) + Real.sqrt (3 * (T / Q) / (3 * T)) =
      (16 * T + 1) / Real.sqrt Q := by
  rw [show 3 * T / 3 = T by ring, show 3 * (T / Q) / (3 * T) = 1 / Q by field_simp,
    Real.sqrt_div hT.le, Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hT' : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  have h : 16 * Real.sqrt T * (Real.sqrt T / Real.sqrt Q) + 1 / Real.sqrt Q =
      (16 * (Real.sqrt T * Real.sqrt T) + 1) / Real.sqrt Q := by ring
  rw [h, hT']

/-- **G4a.** Traced region with `|Rm| ≤ 8√3·Q` and `sec ≥ -r0⁻²` along traces, at scale `Q`. -/
theorem kl82_blowup_traced_O36 (H : ObservedHistory.{u}) {top a : Icc (0 : ℝ) H.horizon}
    (hat : a ≤ top) {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top) (H.activeStage_mono hat) x0)
    {r0 K : ℝ} (hr0 : 0 < r0)
    (hSF : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K)
    (hsec : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹))
    {as ts : Icc (0 : ℝ) H.horizon} (has : a ≤ as) (hast : as ≤ ts) (hts : ts ≤ top)
    {Q T Aa ds R0 : ℝ} (hQ : 0 < Q) (hκQ : (r0 ^ 2)⁻¹ ≤ Q) (hT : 0 < T) (hAa : 0 < Aa)
    (hds : 0 ≤ ds) (hwin : (ts : ℝ) - as = T / Q)
    {y : (H.stageAt ts).Carrier}
    (hy : riemannianEDistOf (H.stageMetric (H.activeStage ts) ts)
      (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
        (H.activeStage_mono hts)) y ≤ ENNReal.ofReal ds)
    (hmarg : ds + (Aa + 16 * T + 1) / Real.sqrt Q < R0) (hR0 : R0 ≤ r0 / 2)
    (hscal : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : as ≤ v) (hvt : v ≤ ts),
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono (has.trans hav))
            (H.activeStage_mono (hvt.trans hts))) z < ENNReal.ofReal R0 →
        metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ 4 * Q) :
    H.isTracedRegion ts y (Aa / Real.sqrt Q) (T / Q) (8 * Real.sqrt 3 * Q) ∧
    ∀ (a'' : Icc (0 : ℝ) H.horizon) (ha'' : a'' ≤ ts), (a'' : ℝ) = ts - T / Q →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage ts) ts) y (Aa / Real.sqrt Q),
      ∀ Y : BackwardPointTrace H (H.activeStage a'') (H.activeStage ts)
          (H.activeStage_mono ha'') q,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a'' ≤ v) (hvt : v ≤ ts),
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v)
          (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (-(r0 ^ 2)⁻¹) := by
  classical
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hT3 : 0 < 3 * T := by positivity
  have hδ : 0 < Aa / Real.sqrt Q := div_pos hAa hsQ
  have herr := kl82_boot_error_O36 hQ hT
  rw [← hwin] at herr
  have hsq0 : 0 ≤ Real.sqrt (3 * ((ts : ℝ) - as) / (3 * T)) := Real.sqrt_nonneg _
  have hsplit : (Aa + 16 * T + 1) / Real.sqrt Q = Aa / Real.sqrt Q + (16 * T + 1) / Real.sqrt Q := by
    ring
  have hlt : ds + Aa / Real.sqrt Q + 16 * Real.sqrt (3 * T / 3) * Real.sqrt ((ts : ℝ) - as) < R0 := by
    linarith
  have hR0r : R0 < r0 := by linarith
  have hprod : 0 ≤ 16 * Real.sqrt (3 * T / 3) * Real.sqrt ((ts : ℝ) - as) := by positivity
  have hR0pos : 0 < R0 := by linarith
  let Xb := (traceRestrict_O30 X (H.activeStage_mono has)
      (H.activeStage_mono (hast.trans hts))).restrictLast (H.activeStage_mono hast)
      (H.activeStage_mono hts)
  have hΛC : (4 * Q / 2 + (r0 ^ 2)⁻¹) * ((ts : ℝ) - as) ≤ 3 * T := by
    rw [hwin]
    have h1 : (4 * Q / 2 + (r0 ^ 2)⁻¹) * (T / Q) ≤ (4 * Q / 2 + Q) * (T / Q) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hT.le hQ.le)
    have h2 : (4 * Q / 2 + Q) * (T / Q) = 3 * T := by field_simp; ring
    linarith
  have hbuf : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage ts) ts) y (Aa / Real.sqrt Q),
      ∀ Y : BackwardPointTrace H (H.activeStage as) (H.activeStage ts)
          (H.activeStage_mono hast) q,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : as ≤ v) (hvt : v ≤ ts),
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono (has.trans hav))
            (H.activeStage_mono (hvt.trans hts)))
          (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) <
          ENNReal.ofReal R0 := by
    intro q hq Y v hav hvt
    have h := kl82_trace_buffer_O30.{u} dist_trace_boot_S68.{u} H hast Xb Y
      (r0 := r0) (Λ := 4 * Q) (C := 3 * T) (d := ds) (δ := Aa / Real.sqrt Q) (ρ := r0)
      (R0 := R0) (by positivity) hT3 hr0 hds hΛC hR0r.le hy hq (by linarith) (by linarith)
      (fun v' hav' hvt' z hz => by
        obtain ⟨A, -⟩ := hSF v' (has.trans hav') (hvt'.trans hts) z hz
        exact ⟨traceRestrict_O30 A (H.activeStage_mono has) (H.activeStage_mono hav')⟩)
      (fun v' hav' hvt' z hz => hsec v' (has.trans hav') (hvt'.trans hts) z hz)
      (fun v' hav' hvt' _ z hz => hscal v' hav' hvt' z hz) v hav hvt
    exact lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff hR0pos).mpr hlt)
  refine ⟨⟨hδ, div_pos hT hQ, as, hast, by linarith, fun q hq => ?_⟩, ?_⟩
  · have hqr0 : q ∈ riemannianBallOf (H.stageMetric (H.activeStage ts) ts)
        (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
          (H.activeStage_mono hts)) r0 := by
      have htri := riemannianEDistOf_triangle (H.stageMetric (H.activeStage ts) ts)
        (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
          (H.activeStage_mono hts)) y q
      have hq' : riemannianEDistOf (H.stageMetric (H.activeStage ts) ts) y q <
          ENNReal.ofReal (Aa / Real.sqrt Q) := hq
      have hsum : riemannianEDistOf (H.stageMetric (H.activeStage ts) ts)
          (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
            (H.activeStage_mono hts)) y + riemannianEDistOf (H.stageMetric (H.activeStage ts) ts) y q
          < ENNReal.ofReal ds + ENNReal.ofReal (Aa / Real.sqrt Q) :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy) hy hq'
      rw [← ENNReal.ofReal_add hds hδ.le] at hsum
      change riemannianEDistOf (H.stageMetric (H.activeStage ts) ts) _ q < ENNReal.ofReal r0
      refine lt_of_le_of_lt htri (hsum.trans_le (ENNReal.ofReal_le_ofReal ?_))
      linarith [Real.sqrt_nonneg (3 * T / 3), Real.sqrt_nonneg ((ts : ℝ) - as),
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (Real.sqrt_nonneg (3 * T / 3)))
          (Real.sqrt_nonneg ((ts : ℝ) - as))]
    obtain ⟨A, -⟩ := hSF ts (has.trans hast) hts q hqr0
    refine ⟨traceRestrict_O30 A (H.activeStage_mono has) (H.activeStage_mono hast), ?_⟩
    apply isRmBoundedBy_of_stage_O36
    intro s has' hst'
    have hd := hbuf q hq (traceRestrict_O30 A (H.activeStage_mono has)
      (H.activeStage_mono hast)) s has' hst'
    have hR := hscal s has' hst' _ hd
    have hs := hsec s (has.trans has') (hst'.trans hts) _
      (lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal hR0r.le))
    refine (rm_normSq_le_of_sec_O30 _ _ (by positivity) (by positivity) hs hR).trans ?_
    have h3 : 0 ≤ 2 * Real.sqrt 3 := by positivity
    have hle : 2 * Real.sqrt 3 * (4 * Q / 2 + 2 * (r0 ^ 2)⁻¹) ≤ 8 * Real.sqrt 3 * Q := by
      have := mul_le_mul_of_nonneg_left
        (show 4 * Q / 2 + 2 * (r0 ^ 2)⁻¹ ≤ 4 * Q by linarith) h3
      linarith
    exact pow_le_pow_left₀ (mul_nonneg h3 (by positivity)) hle 2
  · intro a'' ha'' heq q hq Y v hav hvt
    have hEq : a'' = as := Subtype.ext (by rw [heq]; linarith)
    subst hEq
    have hd := hbuf q hq Y v hav hvt
    exact hsec v (has.trans hav) (hvt.trans hts) _
      (lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal hR0r.le))

end GC.LongTime.Ch12
