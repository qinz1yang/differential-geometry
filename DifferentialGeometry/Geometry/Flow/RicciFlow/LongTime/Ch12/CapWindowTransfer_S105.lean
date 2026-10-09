import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapBallInWindow_S73
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BarrierFromWindows_S95
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCurvatureJets

/-!
# CH12-S105, group 2 (event level): norm transfer, cap scalar lower bound, age clause

For a presented static cap `S` of an event (window radius `D`, accuracy `ε ≤ 3/4`):
* `window_hcmp_S105`: `std ≤ 4 · (q · outputMetric)(window ·)` on `‖w‖ < D` (from `window_closeness`);
* `ball_subset_window_S105` (A1, norm transfer): the `outputMetric`-ball of radius `ρ` about `window z0` is
  inside the window image of `{‖w‖ < ‖z0‖ + 2 √q ρ}` (S73 `ball_subset_image_window_S73`);
* `window_scalar_lower_S105` (A2): `c₀ q ≤ scalar_out(window x)` on `‖x‖ < D` for `ε ≤ ε₀`, `4 ≤ m`
  (the existing `exists_presentedStaticCap_window_curvature_bounds`, packaged as constants);
* `cap_of_lowscalar_S105`: a window point `u` of a low-scalar set `U ⊆ B(p, 20 r)` forces `p = window w'`,
  `‖w'‖ < Dc + 2`, and the age clause `a ≤ θ / q` (A3, `age_le_of_scalar_S95`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

section Event

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
  (S : E.PresentedStaticCap fixed D m ε b)

/-- The one-sided metric comparison needed by `ball_subset_image_window_S73`, from `window_closeness`. -/
theorem window_hcmp_S105 (hε : ε ≤ 3 / 4) (w : standardCapWindow D) (hw : ‖w.val‖ < D)
    (v : TangentSpace ThreeModel w) :
    StandardCap.metric.inner w.val v v ≤
      4 * (scaleMetric S.neck.scale S.neck.scale_pos E.outputMetric).inner (S.window w)
        (mfderiv ThreeModel ThreeModel S.window w v) (mfderiv ThreeModel ThreeModel S.window w v) := by
  have h1 := (DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le
    (StandardCap.metric.restrictOpen (standardCapWindow D)) S.witness.windowMetric w
    (S.metricDerivNorm_window_lt (Nat.zero_le m) w hw).le v).1
  have h2 : (StandardCap.metric.restrictOpen (standardCapWindow D)).inner w v v =
      StandardCap.metric.inner w.val v v := rfl
  have h3 : 0 ≤ StandardCap.metric.inner w.val v v := metric_inner_self_nonneg _ _ _
  rw [h2] at h1
  rw [scaleMetric_inner, ← S.window_inner]
  nlinarith only [h1, h3, hε]

/-- (A1) norm transfer: the `outputMetric`-ball of radius `ρ` about `window z0` lies in the window image of the
norm ball `‖w‖ < ‖z0‖ + 2 √q ρ`. -/
theorem ball_subset_window_S105 (hε : ε ≤ 3 / 4) (z0 : standardCapWindow D) {ρ : ℝ} (hρ : 0 < ρ)
    (hroom : ‖z0.val‖ + 2 * (Real.sqrt S.neck.scale * ρ) < D) :
    riemannianBallOf E.outputMetric (S.window z0) ρ ⊆
      S.window '' {w : standardCapWindow D | ‖w.val‖ < ‖z0.val‖ + 2 * (Real.sqrt S.neck.scale * ρ)} := by
  have hq := S.neck.scale_pos
  have hsq : 0 < Real.sqrt S.neck.scale := Real.sqrt_pos.mpr hq
  have key := ball_subset_image_window_S73 (scaleMetric S.neck.scale hq E.outputMetric) S.window
    S.window_isLocalDiffeomorph S.window_smooth.isEmbedding.injective
    (fun w hw v => window_hcmp_S105 S hε w hw v) z0 (a := Real.sqrt S.neck.scale * ρ)
    (mul_pos hsq hρ) hroom
  rw [riemannianBallOf_scaleMetric] at key
  exact key

end Event

/-- (A2) the cap scalar lower bound, packaged as constants: for accuracy `ε ≤ ε₀` and order `4 ≤ m`,
`c₀ · scale ≤ scalar_out (window x)` on `‖x‖ < D`.  (Same source as `hscale` of S53.) -/
theorem window_scalar_lower_S105 : ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε b), ε ≤ ε₀ → 4 ≤ m →
      ∀ x : standardCapWindow D, ‖x.val‖ < D →
        c₀ * S.neck.scale ≤ metricScalarAt E.outputMetric (S.window x) := by
  obtain ⟨ε₀, c, B, hε₀, hc, -, h⟩ := exists_presentedStaticCap_window_curvature_bounds.{u}
  exact ⟨ε₀, c, hε₀, hc, fun S hε hm x hx => (h S hε hm x hx).1⟩

/-- Event-level absorption: a window point `u = window w` (`‖w‖ < Dc + 1`) of a set `U ⊆ B(p, 20 r)` on which the
scalar is `≤ 9K/r²` forces `p = window w'` with `‖w'‖ < Dc + 2`, and the AGE clause `a ≤ θ/q` of CAP whenever
`a < τ r²` and `9 K τ ≤ c₀ θ`.  Inputs: the cap scalar lower bound `hscale` (A2), the birth shift `40 r √q ≤ 1`
(`hshift`), `Dc + 2 ≤ D`, `ε ≤ 3/4`. -/
theorem cap_of_lowscalar_S105 {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) (hε : ε ≤ 3 / 4)
    {Dc r K c₀ θ τ age : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hD : Dc + 2 ≤ D)
    (hscale : ∀ x : standardCapWindow D, ‖x.val‖ < Dc + 1 →
      c₀ * S.neck.scale ≤ metricScalarAt E.outputMetric (S.window x))
    (hshift : 40 * r * Real.sqrt S.neck.scale ≤ 1)
    (hage : age < τ * r ^ 2) (hτK : 9 * K * τ ≤ c₀ * θ)
    {p : Q.Carrier} {U : Set Q.Carrier}
    (hU : U ⊆ riemannianBallOf E.outputMetric p (20 * r))
    (hs : ∀ y ∈ U, metricScalarAt E.outputMetric y ≤ 9 * K / r ^ 2)
    {w : standardCapWindow D} (hw : ‖w.val‖ < Dc + 1) (huU : S.window w ∈ U) :
    ∃ w' : standardCapWindow D, ‖w'.val‖ < Dc + 2 ∧ S.window w' = p ∧ age ≤ θ * S.neck.scale⁻¹ := by
  have hq := S.neck.scale_pos
  have hsq : 0 < Real.sqrt S.neck.scale := Real.sqrt_pos.mpr hq
  have hball : p ∈ riemannianBallOf E.outputMetric (S.window w) (20 * r) := by
    have h := hU huU
    change riemannianEDistOf E.outputMetric p (S.window w) < ENNReal.ofReal (20 * r) at h
    change riemannianEDistOf E.outputMetric (S.window w) p < ENNReal.ofReal (20 * r)
    rwa [riemannianEDistOf_comm]
  have h40 : 2 * (Real.sqrt S.neck.scale * (20 * r)) = 40 * r * Real.sqrt S.neck.scale := by ring
  have hroom : ‖w.val‖ + 2 * (Real.sqrt S.neck.scale * (20 * r)) < D := by
    rw [h40]; linarith only [hw, hshift, hD]
  obtain ⟨w', hw'n, hw'e⟩ := ball_subset_window_S105 S hε w (by positivity) hroom hball
  refine ⟨w', ?_, hw'e, ?_⟩
  · have hw'n' : ‖w'.val‖ < ‖w.val‖ + 2 * (Real.sqrt S.neck.scale * (20 * r)) := hw'n
    rw [h40] at hw'n'
    linarith only [hw'n', hw, hshift]
  · have hlow := hscale w hw
    have hup := hs _ huU
    exact age_le_of_scalar_S95 hq hc₀ hr hτ hage hlow hup hτK

end GC.LongTime.Ch12
