import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimAssembly_O25

/-!
# CH12-O30, G3b-1: the traced points of the blow-up region stay in the radial buffer

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (blow-up step of the
proof of claim (C)); not a verbatim transcription.  The reference PDFs named in AGENTS.md are not
on this machine; locators follow the CX11 / O25 records in DELIVERIES.

**Ball alignment (answer to the external review R4 on the `hboot` margin).**  In the blow-up step
`hboot` is applied with the *base* trace `X` (centre `X(v)`, the trace of `x0` restricted to the
blow-up window `[t_x − T/Q, t_x]`) as its `p`-trace and the trace of a point `q` near the selected
point `x̄` as its `q`-trace.  Both radii of `hboot` are radii of balls **centred at `X(v)`**:
`ρ = r0` (where `hSF` provides traces) and `R0 = d̄ + (r − d̄)/4` (`r = 7r0/16`,
`d̄ = d_{t_x}(X(t_x), x̄) < r`), the radial buffer of `kl82_select_O30`, where its last conjunct
gives `R ≤ 4Q` inside the age window.  The radius `3r0/8` is **not** used here (it is only the
radius of claim (C) and of the window volume transfer); since `d̄` may exceed `3r0/8`, using
`R0 = 3r0/8` with `p = X(t_x)` would violate `hboot`'s hypothesis `d(p,q) + … < R0`.

`kl82_trace_buffer_O30` is this application of `hboot`: from a scalar bound `R ≤ Λ` on the
`R0`-ball around `X(v)` and `sec ≥ −r0⁻²` on the `ρ`-ball, the dimension-three Ricci bound
`Ric ≤ (R/2 + r0⁻²) g` gives `Ric ≤ C/(v − a)` for any `C ≥ (Λ/2 + r0⁻²)(t − a)` (blow-up:
`Λ = 4Q`, `r0⁻² ≤ Q`, `t − a = T/Q`, `C = 3T`, D-R4-6), and `hboot` keeps the trace of every `q ∈ B_t(x̄, δ)` within
`d + δ + 16√(C/3)√(t − a)` of `X(v)` (`d ≥ d_t(X(t), x̄)`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature.DimensionThree
  (metricRicciAt_le_of_sectionalBoundedBelowAt)
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **G3b-1**: `hboot` at the blow-up scale, centred at the base trace `X(v)`. -/
theorem kl82_trace_buffer_O30
    (hboot : ∀ (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
      {p q : (H.stageAt t).Carrier}
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
      (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
      {C ρ R0 : ℝ}, 0 < C → 0 < ρ →
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q < ENNReal.ofReal ρ →
      (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) < ρ / 2 →
      (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) +
          Real.sqrt (3 * ((t : ℝ) - a) / C) < R0 →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
          Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) z)) →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
        ∀ z : (H.stageAt v).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
            ENNReal.ofReal R0 →
          ∀ w : TangentSpace ThreeModel z,
            ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
              C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w) →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        traceEDist_CX11 H (hat := hat) X A v hav hvt ≤
          ENNReal.ofReal ((riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
            16 * Real.sqrt (C / 3) * (Real.sqrt ((t : ℝ) - a) - Real.sqrt ((v : ℝ) - a))))
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
    (hSF : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
          (H.activeStage_mono hav) z))
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
  -- the Ricci input of `hboot` on the `R0`-ball around `X(v)`
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
  have hb := hboot H hat X A (C := C) (ρ := ρ) (R0 := R0) hC hρ hpqρ (by linarith)
    (by linarith) hSF hRic v hav hvt
  rw [traceEDist_at_stage_CX11 H X A v hav hvt (H.activeStage v) rfl
    (H.activeStage_mono hav) (H.activeStage_mono hvt)] at hb
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : 0 ≤ Real.sqrt ((v : ℝ) - a) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (C / 3) := Real.sqrt_nonneg _
  nlinarith

end GC.LongTime.Ch12
