import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowLocalInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapSeamScalarGlue

/-!
# S-CH11-FIX5 port of astra `CapPhysicalScalarGlue`（`PortC11P`）

来源：donor `CapPhysicalScalarGlue.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 6 个 error（`CapSeamScalarGlue` 落地后暴露），均为 Mathlib 引理名 / 隐式参数
约定的差异；本 port 只做 elaboration 层面修补（no statement / definition / proof idea altered），
全部在 `exists_uniform_actual_local_physical_scalar_glue_on_closed_core` 的证明内：
* 第一个目标 `1 ≤ capPhysicalScalarConstant Λ`：`exact le_max_left _ _` 前先 `change (1 : ℝ) ≤ max 1 …`
  （`ℝ≥0` 的 `LinearOrder` 实例在 `le_max_left _ _` 的 metavariable 上卡住）。
* `hK`：`le_add_of_nonneg_right (zero_le _)` → `le_add_of_nonneg_right zero_le`（`zero_le` 现在的参数
  是隐式）。
* 三处 `mul_le_mul_left'` / `mul_le_mul_right'`（本树里已不存在这两个名字）→ 对应的
  `mul_le_mul' le_rfl h` / `mul_le_mul' h le_rfl`（`hφ` 一步与 `calc` 的两步）。
* `hfactor`：`ENNReal.ofReal_coe_nnreal K` → `ENNReal.ofReal_coe_nnreal (p := K)`（`p` 现在是隐式参数）。
原路径 `CapPhysicalScalarGlue` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold Function
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- This bound contains fixed-model data only. Its argument is the uniform
ellipticity constant chosen before the event, neck scale and fine accuracy. -/
def capPhysicalScalarConstant (Λ : ℝ) : ℝ≥0 :=
  ⟨max 1 (Λ * (Real.pi / standardCapL +
    Real.sqrt 2 * capRadialDerivativeConstant)),
    zero_le_one.trans (le_max_left _ _)⟩

private theorem scalar_inverse_constant_cancel
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m η b) (Λ : ℝ) :
    ((S.boundaryExtensionConstant + S.neck.annulusDerivativeConstant : ℝ≥0) : ℝ) *
      (Λ * Real.sqrt S.neck.scale) =
        Λ * (Real.pi / standardCapL + Real.sqrt 2 * capRadialDerivativeConstant) := by
  change (Real.pi / (standardCapL * Real.sqrt S.neck.scale) +
    Real.sqrt 2 * capRadialDerivativeConstant / Real.sqrt S.neck.scale) *
      (Λ * Real.sqrt S.neck.scale) = _
  calc
    _ = ((Real.pi / standardCapL + Real.sqrt 2 * capRadialDerivativeConstant) /
        Real.sqrt S.neck.scale) * (Λ * Real.sqrt S.neck.scale) := by
      rw [add_div, div_div]
    _ = Λ * (((Real.pi / standardCapL + Real.sqrt 2 * capRadialDerivativeConstant) /
        Real.sqrt S.neck.scale) * Real.sqrt S.neck.scale) := mul_left_comm _ _ _
    _ = _ := by rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr S.neck.scale_pos).ne']

/-- The SAME coordinate extension, selected before every closed-cap point, admits local
realizations on the actual postmetric with one fixed Lipschitz bound. The radial
companion is supplied alongside this same cap by the concrete finite constructor.
This is local: no global output scalar or whole-event distance inequality is asserted. -/
theorem exists_uniform_actual_local_physical_scalar_glue_on_closed_core :
    ∃ C : ℝ≥0, 1 ≤ C ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m η b)
        (hOld : E.old = E.transition.trace.retainedCore),
        S.witness.HasRadialCoordinates → S.hasCanonicalWindow → η ≤ 1 / 2 →
        standardCapL + 1 ≤ D → ∀ (p : E.incoming.terminalRegularOpen) (R : ℝ≥0),
        ∃ (f φ : ThreeSpace → ℝ),
          LipschitzWith S.boundaryExtensionConstant f ∧
          (∀ (x : ThreeSpace) (hx : x ∈ standardCapWindow D) (hc : x ∈ standardCapClosedCore),
            S.inclusion (S.witness.window ⟨x, hx⟩) =
              S.inclusion (S.witness.capChart ⟨x, hc⟩) ∧ φ x = f x) ∧
          (∀ (x : neckRetainedCollar S.delta)
            (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D),
            (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ capSeamOpen →
            S.inclusion (S.witness.window
              ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
                E.oldOutput (S.collarOldPoint hOld x) ∧
            φ ((standardCapL + x.val.2) • (x.val.1 : ThreeSpace)) =
              (min (riemannianEDistOf E.terminal.metric
                (E.oldTerminal (S.collarOldPoint hOld x)) p) (R : ℝ≥0∞)).toReal) ∧
          ∀ x₀ : standardCapWindow D, ‖x₀.val‖ ≤ standardCapL →
            ∃ (U : TopologicalSpace.Opens Q.Carrier) (Ψ : Q.Carrier → ℝ),
              S.window x₀ ∈ U ∧
              (∀ y ∈ U, ∀ z ∈ U,
                edist (Ψ y) (Ψ z) ≤ (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z) ∧
              (∀ x : standardCapWindow D, S.window x ∈ U → Ψ (S.window x) = φ x.val) ∧
              (U : Set Q.Carrier) ⊆
                S.window '' {x : standardCapWindow D | x.val ∈ Metric.ball x₀.val capSeamWidth} := by
  obtain ⟨Λ, _, hinverse⟩ := exists_uniform_local_window_inverse_on_closed_core.{u}
  refine ⟨capPhysicalScalarConstant Λ, ?_, ?_⟩
  · change (1 : ℝ) ≤ max 1 (Λ * (Real.pi / standardCapL +
      Real.sqrt 2 * capRadialDerivativeConstant))
    exact le_max_left _ _
  intro P Q a s E fixed D η m b S hOld hcoord hcanonical hη hD p R
  obtain ⟨f, φ, hf, hinside, hretained, hlocal⟩ :=
    S.exists_actual_local_scalar_glue hOld hcoord p R
  let K : ℝ≥0 := S.boundaryExtensionConstant + S.neck.annulusDerivativeConstant
  refine ⟨f, φ, hf, hinside, hretained, ?_⟩
  intro x₀ hx₀
  have hbuffer : ∃ r : ℝ, 0 < r ∧ r ≤ capSeamWidth ∧
      LipschitzOnWith K φ (Metric.ball x₀.val r) := by
    rcases lt_or_eq_of_le hx₀ with hstrict | hseam
    · let r : ℝ := min capSeamWidth ((standardCapL - ‖x₀.val‖) / 2)
      have hr : 0 < r := lt_min capSeamWidth_pos (by linarith)
      have hrwidth : r ≤ capSeamWidth := min_le_left _ _
      have hrgap : r ≤ (standardCapL - ‖x₀.val‖) / 2 := min_le_right _ _
      have hφ (x : ThreeSpace) (hx : x ∈ Metric.ball x₀.val r) : φ x = f x := by
        have hd := Metric.mem_ball.mp hx
        have hn := norm_le_norm_add_norm_sub' x x₀.val
        rw [← dist_eq_norm] at hn
        have hxnorm : ‖x‖ ≤ standardCapL := by linarith
        have hxwindow : x ∈ standardCapWindow D := by
          change ‖x‖ < D + 1
          linarith
        have hxcore : x ∈ standardCapClosedCore := by
          simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right] using hxnorm
        exact (hinside x hxwindow hxcore).2
      refine ⟨r, hr, hrwidth, ?_⟩
      intro x hx y hy
      rw [hφ x hx, hφ y hy]
      have hK : S.boundaryExtensionConstant ≤ K := le_add_of_nonneg_right zero_le
      exact (hf x y).trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hK) le_rfl)
    · exact ⟨capSeamWidth, capSeamWidth_pos, le_rfl, hlocal x₀.val hseam⟩
  obtain ⟨r, hr, hrwidth, hφ⟩ := hbuffer
  obtain ⟨U, χ, hcenter, hrepr, hpullback, hχ⟩ :=
    hinverse S hcanonical hη hD x₀ hx₀ r hr hrwidth
  have hfactor : (K : ℝ≥0∞) * ENNReal.ofReal (Λ * Real.sqrt S.neck.scale) ≤
      (capPhysicalScalarConstant Λ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := K), ← ENNReal.ofReal_mul K.coe_nonneg,
      scalar_inverse_constant_cancel S Λ]
    exact ENNReal.ofReal_le_coe.mpr (le_max_right _ _)
  have hcoords (y : Q.Carrier) (hy : y ∈ U) : χ y ∈ Metric.ball x₀.val r := by
    obtain ⟨x, hx, _, hball⟩ := hrepr y hy
    exact hx ▸ hball
  refine ⟨U, φ ∘ χ, hcenter, ?_, ?_, ?_⟩
  · intro y hy z hz
    calc
      edist ((φ ∘ χ) y) ((φ ∘ χ) z) ≤ (K : ℝ≥0∞) * edist (χ y) (χ z) :=
        hφ (hcoords y hy) (hcoords z hz)
      _ ≤ (K : ℝ≥0∞) * (ENNReal.ofReal (Λ * Real.sqrt S.neck.scale) *
          riemannianEDistOf E.outputMetric y z) := mul_le_mul' le_rfl (hχ y hy z hz)
      _ = ((K : ℝ≥0∞) * ENNReal.ofReal (Λ * Real.sqrt S.neck.scale)) *
          riemannianEDistOf E.outputMetric y z := (mul_assoc _ _ _).symm
      _ ≤ (capPhysicalScalarConstant Λ : ℝ≥0∞) *
          riemannianEDistOf E.outputMetric y z := mul_le_mul' hfactor le_rfl
  · intro x hx
    exact congrArg φ (hpullback x hx)
  · intro y hy
    obtain ⟨x, _, hxy, hball⟩ := hrepr y hy
    exact ⟨x, Metric.mem_ball.mpr ((Metric.mem_ball.mp hball).trans_le hrwidth), hxy⟩

/-- The original seam-centered conclusion uses the same selected scalar pair
from the closed-core producer; no second extension is chosen. -/
theorem exists_uniform_actual_local_physical_scalar_glue :
    ∃ C : ℝ≥0, 1 ≤ C ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m η b)
        (hOld : E.old = E.transition.trace.retainedCore),
        S.witness.HasRadialCoordinates → S.hasCanonicalWindow → η ≤ 1 / 2 →
        standardCapL + 1 ≤ D → ∀ (p : E.incoming.terminalRegularOpen) (R : ℝ≥0),
        ∃ (f φ : ThreeSpace → ℝ),
          LipschitzWith S.boundaryExtensionConstant f ∧
          (∀ (x : ThreeSpace) (hx : x ∈ standardCapWindow D) (hc : x ∈ standardCapClosedCore),
            S.inclusion (S.witness.window ⟨x, hx⟩) =
              S.inclusion (S.witness.capChart ⟨x, hc⟩) ∧ φ x = f x) ∧
          (∀ (x : neckRetainedCollar S.delta)
            (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D),
            (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ capSeamOpen →
            S.inclusion (S.witness.window
              ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
                E.oldOutput (S.collarOldPoint hOld x) ∧
            φ ((standardCapL + x.val.2) • (x.val.1 : ThreeSpace)) =
              (min (riemannianEDistOf E.terminal.metric
                (E.oldTerminal (S.collarOldPoint hOld x)) p) (R : ℝ≥0∞)).toReal) ∧
          ∀ x₀ : standardCapWindow D, ‖x₀.val‖ = standardCapL →
            ∃ (U : TopologicalSpace.Opens Q.Carrier) (Ψ : Q.Carrier → ℝ),
              S.window x₀ ∈ U ∧
              (∀ y ∈ U, ∀ z ∈ U,
                edist (Ψ y) (Ψ z) ≤ (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z) ∧
              (∀ x : standardCapWindow D, S.window x ∈ U → Ψ (S.window x) = φ x.val) ∧
              (U : Set Q.Carrier) ⊆
                S.window '' {x : standardCapWindow D | x.val ∈ Metric.ball x₀.val capSeamWidth} := by
  obtain ⟨C, hC, hmake⟩ := exists_uniform_actual_local_physical_scalar_glue_on_closed_core.{u}
  refine ⟨C, hC, ?_⟩
  intro P Q a s E fixed D η m b S hOld hcoord hcanonical hη hD p R
  obtain ⟨f, φ, hf, hinside, hretained, hlocal⟩ :=
    hmake S hOld hcoord hcanonical hη hD p R
  exact ⟨f, φ, hf, hinside, hretained, fun x₀ hx₀ => hlocal x₀ hx₀.le⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
