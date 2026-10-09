import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82RegVolume_O78
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimTraced_O36

/-!
# CH12-O78, G3a: regional blow-up traces

* `kl82_ric_of_scal_R_O78`: `R ≤ Λ` + `sec ≥ −r0⁻²` on the `R0`-balls ⇒ `Ric ≤ C/(v−a)` there
  (the Ricci block of `kl82_trace_buffer_O30`, stated separately).
* `kl82_trace_buffer_R_O78`: `kl82_trace_buffer_O30` with the boot `dist_trace_boot_R_O78`.
* `kl82_blowup_traced_R_O78`: `kl82_blowup_traced_O36` from the Reg-input: the traces of the
  `A Q^{-1/2}`-ball over the window `T Q^{-1}` are *produced* by `trace_start_R_O78` (review R6
  Q1.4: controlled local traces at the blow-up scales), not assumed.
Proof bodies follow O30/O36 line by line apart from these inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature.DimensionThree
  (metricRicciAt_le_of_sectionalBoundedBelowAt)
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **G3a-0.** `sec ≥ −r0⁻²` and `R ≤ Λ` on the `R0`-balls give `Ric ≤ C/(v−a)` there when
`(Λ/2 + r0⁻²)(t−a) ≤ C` (the Ricci input of the boot / trace start at the blow-up scale). -/
theorem kl82_ric_of_scal_R_O78 (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon}
    (hat : a ≤ t) {p : (H.stageAt t).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {r0 Λ C ρ R0 : ℝ} (hΛ : 0 ≤ Λ)
    (hΛC : (Λ / 2 + (r0 ^ 2)⁻¹) * ((t : ℝ) - a) ≤ C) (hR0ρ : R0 ≤ ρ)
    (hsec : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) z (-(r0 ^ 2)⁻¹))
    (hscal : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal R0 →
        metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ Λ) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal R0 →
        ∀ w : TangentSpace ThreeModel z,
          ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
            C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w := by
  intro v hav hvt hav' z hz w
  have hs : 0 < (v : ℝ) - a := by linarith
  have hvt' : (v : ℝ) ≤ t := hvt
  have hzρ : z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
      (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ :=
    lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hR0ρ)
  have hRic := metricRicciAt_le_of_sectionalBoundedBelowAt finrank_euclideanSpace_fin
    (hsec v hav hvt z hzρ) w
  rw [metricRicciAt_apply_eq_ricciTensor] at hRic
  have hgw : 0 ≤ (H.stageMetric (H.activeStage v) v).inner z w w :=
    metric_inner_self_nonneg _ z w
  have hR := hscal v hav hvt hav' z hz
  have hk : 0 ≤ Λ / 2 + (r0 ^ 2)⁻¹ := by positivity
  have hcoef : metricScalarAt (H.stageMetric (H.activeStage v) v) z / 2 + (r0 ^ 2)⁻¹ ≤
      C / ((v : ℝ) - a) := by
    rw [le_div_iff₀ hs]
    have h1 : (Λ / 2 + (r0 ^ 2)⁻¹) * ((v : ℝ) - a) ≤ (Λ / 2 + (r0 ^ 2)⁻¹) * ((t : ℝ) - a) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    have h2 : (metricScalarAt (H.stageMetric (H.activeStage v) v) z / 2 + (r0 ^ 2)⁻¹) *
        ((v : ℝ) - a) ≤ (Λ / 2 + (r0 ^ 2)⁻¹) * ((v : ℝ) - a) :=
      mul_le_mul_of_nonneg_right (by linarith) hs.le
    linarith
  exact hRic.trans (mul_le_mul_of_nonneg_right hcoef hgw)

/-- **G3a-1.** Regional `kl82_trace_buffer_O30` (boot = `dist_trace_boot_R_O78`). -/
theorem kl82_trace_buffer_R_O78
    (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p x q : (H.stageAt t).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {r0 Λ C d δ ρ R0 : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 < C) (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hΛC : (Λ / 2 + (r0 ^ 2)⁻¹) * ((t : ℝ) - a) ≤ C) (hR0ρ : R0 ≤ ρ)
    (hpx : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal d)
    (hxq : riemannianEDistOf (H.stageMetric (H.activeStage t) t) x q < ENNReal.ofReal δ)
    (hmargρ : d + δ + 16 * Real.sqrt (C / 3) *
      Real.sqrt ((t : ℝ) - a) < ρ / 2)
    (hmargR0 : d + δ + 16 * Real.sqrt (C / 3) *
      Real.sqrt ((t : ℝ) - a) +
        Real.sqrt (3 * ((t : ℝ) - a) / C) < R0)
    (hEvt : ∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
        (hit : i.succ ≤ H.activeStage t),
      riemannianBallOf (H.initialMetric i.succ)
          (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) ρ ⊆
        H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le)
    (hsec : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) z (-(r0 ^ 2)⁻¹))
    (hscal : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal R0 →
        metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ Λ) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        ENNReal.ofReal (d + δ + 16 * Real.sqrt (C / 3) *
          Real.sqrt ((t : ℝ) - a)) := by
  intro v hav hvt
  have hta : (a : ℝ) ≤ t := hat
  have hδ : 0 < δ := by
    have h0 := lt_of_le_of_lt zero_le hxq
    exact ENNReal.ofReal_pos.mp h0
  have hs0 : 0 ≤ 16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) := by positivity
  -- distance of the endpoints
  have hpq : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q ≤
      ENNReal.ofReal (d + δ) := by
    calc riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x +
            riemannianEDistOf (H.stageMetric (H.activeStage t) t) x q :=
          riemannianEDistOf_triangle _ p x q
      _ ≤ ENNReal.ofReal d + ENNReal.ofReal δ := add_le_add hpx hxq.le
      _ = ENNReal.ofReal (d + δ) := (ENNReal.ofReal_add hd hδ.le).symm
  have hpqR : (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal ≤ d + δ :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hpq
  have hpqρ : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q <
      ENNReal.ofReal ρ :=
    lt_of_le_of_lt hpq ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith))
  -- the Ricci input of the boot on the `R0`-ball around `X(v)`
  have hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal R0 →
        ∀ w : TangentSpace ThreeModel z,
          ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
            C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w := by
    intro v hav hvt hav' z hz w
    have hs : 0 < (v : ℝ) - a := by linarith
    have hvt' : (v : ℝ) ≤ t := hvt
    have hzρ : z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ :=
      lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hR0ρ)
    have hRic := metricRicciAt_le_of_sectionalBoundedBelowAt finrank_euclideanSpace_fin
      (hsec v hav hvt z hzρ) w
    rw [metricRicciAt_apply_eq_ricciTensor] at hRic
    have hgw : 0 ≤ (H.stageMetric (H.activeStage v) v).inner z w w :=
      metric_inner_self_nonneg _ z w
    have hR := hscal v hav hvt hav' z hz
    have hk : 0 ≤ Λ / 2 + (r0 ^ 2)⁻¹ := by positivity
    have hcoef : metricScalarAt (H.stageMetric (H.activeStage v) v) z / 2 + (r0 ^ 2)⁻¹ ≤
        C / ((v : ℝ) - a) := by
      rw [le_div_iff₀ hs]
      have h1 : (Λ / 2 + (r0 ^ 2)⁻¹) * ((v : ℝ) - a) ≤ (Λ / 2 + (r0 ^ 2)⁻¹) * ((t : ℝ) - a) :=
        mul_le_mul_of_nonneg_left (by linarith) hk
      have h2 : (metricScalarAt (H.stageMetric (H.activeStage v) v) z / 2 + (r0 ^ 2)⁻¹) *
          ((v : ℝ) - a) ≤ (Λ / 2 + (r0 ^ 2)⁻¹) * ((v : ℝ) - a) :=
        mul_le_mul_of_nonneg_right (by linarith) hs.le
      linarith
    exact hRic.trans (mul_le_mul_of_nonneg_right hcoef hgw)
  have hb := dist_trace_boot_R_O78 H hat X A (C := C) (ρ := ρ) (R0 := R0) hC hρ hpqρ
    (by linarith) (by linarith) hEvt hRic v hav hvt
  rw [traceEDist_at_stage_CX11 H X A v hav hvt (H.activeStage v) rfl
    (H.activeStage_mono hav) (H.activeStage_mono hvt)] at hb
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : 0 ≤ Real.sqrt ((v : ℝ) - a) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (C / 3) := Real.sqrt_nonneg _
  nlinarith

theorem kl82_blowup_traced_R_O78 (H : ObservedHistory.{u}) {top a : Icc (0 : ℝ) H.horizon}
    (hat : a ≤ top) {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top) (H.activeStage_mono hat) x0)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hEvt : ∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
        (hit : i.succ ≤ H.activeStage top),
      riemannianBallOf (H.initialMetric i.succ)
          (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) r0 ⊆
        H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le)
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
  have hEvtb : ∀ (i : Fin H.eventCount) (hai : H.activeStage as ≤ i.castSucc)
      (hit : i.succ ≤ H.activeStage ts),
      riemannianBallOf (H.initialMetric i.succ)
          (Xb.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) r0 ⊆
        H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le :=
    fun i hai hit => hEvt i ((H.activeStage_mono has).trans hai) (hit.trans (H.activeStage_mono hts))
  have hsecb : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : as ≤ v) (hvt : v ≤ ts),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Xb.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) z (-(r0 ^ 2)⁻¹) :=
    fun v' hav' hvt' z hz => hsec v' (has.trans hav') (hvt'.trans hts) z hz
  have hRicb := kl82_ric_of_scal_R_O78 H hast Xb (r0 := r0) (Λ := 4 * Q) (C := 3 * T) (ρ := r0)
    (R0 := R0) (by positivity) hΛC hR0r.le hsecb (fun v' hav' hvt' _ z hz => hscal v' hav' hvt' z hz)
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
    have h := kl82_trace_buffer_R_O78.{u} H hast Xb Y
      (r0 := r0) (Λ := 4 * Q) (C := 3 * T) (d := ds) (δ := Aa / Real.sqrt Q) (ρ := r0)
      (R0 := R0) (by positivity) hT3 hr0 hds hΛC hR0r.le hy hq (by linarith) (by linarith)
      hEvtb hsecb
      (fun v' hav' hvt' _ z hz => hscal v' hav' hvt' z hz) v hav hvt
    exact lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff hR0pos).mpr hlt)
  refine ⟨⟨hδ, div_pos hT hQ, as, hast, by linarith, fun q hq => ?_⟩, ?_⟩
  · have hqs : riemannianEDistOf (H.stageMetric (H.activeStage ts) ts)
        (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
          (H.activeStage_mono hts)) q < ENNReal.ofReal (ds + Aa / Real.sqrt Q) := by
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
      exact lt_of_le_of_lt htri hsum
    have hqsR : (riemannianEDistOf (H.stageMetric (H.activeStage ts) ts)
        (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
          (H.activeStage_mono hts)) q).toReal ≤ ds + Aa / Real.sqrt Q :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hqs.le
    have hqr0 : riemannianEDistOf (H.stageMetric (H.activeStage ts) ts)
        (X.point (H.activeStage ts) (H.activeStage_mono (has.trans hast))
          (H.activeStage_mono hts)) q < ENNReal.ofReal r0 :=
      hqs.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    have hqsR' : (riemannianEDistOf (H.stageMetric (H.activeStage ts) ts)
        ((traceRestrict_O30 X (H.activeStage_mono has)
          (H.activeStage_mono (hast.trans hts))).point (H.activeStage ts)
            (H.activeStage_mono hast) (H.activeStage_mono hts)) q).toReal ≤
        ds + Aa / Real.sqrt Q := hqsR
    obtain ⟨A⟩ := trace_start_R_O78 H hast Xb (C := 3 * T) (ρ := r0) (R0 := R0) hT3 hr0 hqr0
      (by linarith) (by linarith) hEvtb hRicb
    refine ⟨A, ?_⟩
    apply isRmBoundedBy_of_stage_O36
    intro s has' hst'
    have hd := hbuf q hq A s has' hst'
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
