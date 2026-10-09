import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# O-CH11-NATIVE-SEP G4：`hSEP` chart-reach 的 window 内径向长度 M4（后缀 `_C11SP`，无 binder）

`window_tip_dist_le_C11SP`：canonical static cap window（`hasCanonicalWindow`，`ε ≤ 1/2`）中，
`‖x‖ < D` 的点到 tip 的 output 距离 `≤ √(3/2)/√q · ‖x‖`（`q = S.neck.scale`）。
证明：把 `S.window` 延拓成 `ThreeSpace → Q.Carrier`（窗外取常值），在凸集 `ball 0 D` 上用
`riemannian_edist_le_on_convex_source`；速度界 = `actual_window_quad_bounds`
（`q·g(dW v, dW v) ≤ (3/2)·std(v,v)`）
+ `StandardCap.metric_inner_le`（`std(v,v) ≤ ‖v‖²`）。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private actual_window_quad_bounds from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **M4（PROVED）**：window 内 `x → tip` 的 output 距离 `≤ √(3/2)/√q · ‖x‖`（`‖x‖ < D`）。 -/
theorem window_tip_dist_le_C11SP (S : E.PresentedStaticCap fixed D m ε b)
    (hcan : S.hasCanonicalWindow) (hε : ε ≤ 1 / 2) (x : standardCapWindow D) (hx : ‖x.val‖ < D)
    (hx0 : (0 : ThreeSpace) ∈ standardCapWindow D) :
    riemannianEDistOf E.outputMetric (S.window x) (S.window ⟨0, hx0⟩) ≤
      ENNReal.ofReal (Real.sqrt (3 / 2) / Real.sqrt S.neck.scale * ‖x.val‖) := by
  classical
  have hq : 0 < S.neck.scale := S.neck.scale_pos
  let f : ThreeSpace → Q.Carrier := fun p =>
    if h : p ∈ standardCapWindow D then S.window ⟨p, h⟩ else S.window x
  have hfval : ∀ y : standardCapWindow D, f y.val = S.window y := by
    intro y
    simp only [f, y.2, ↓reduceDIte]
  have hcomp : (fun y : standardCapWindow D => f y.val) = S.window := funext hfval
  have hfat : ∀ y : standardCapWindow D, ContMDiffAt ThreeModel ThreeModel ∞ f y.val := by
    intro y
    have h : ContMDiffAt ThreeModel ThreeModel ∞ (fun z : standardCapWindow D => f z.val) y := by
      rw [hcomp]
      exact S.window_smooth.contMDiff.contMDiffAt
    exact contMDiffAt_subtype_iff.mp h
  have hU : IsOpen (standardCapWindow D : Set ThreeSpace) := (standardCapWindow D).isOpen
  have hf : ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel 1 f (standardCapWindow D : Set ThreeSpace) :=
    fun p hp => ((hfat ⟨p, hp⟩).of_le (by simp)).contMDiffWithinAt
  have hSU : Metric.ball (0 : ThreeSpace) D ⊆ (standardCapWindow D : Set ThreeSpace) := by
    intro p hp
    change ‖p‖ < D + 1
    rw [Metric.mem_ball, dist_zero_right] at hp
    linarith
  let C : ℝ≥0 := ⟨Real.sqrt (3 / 2) / Real.sqrt S.neck.scale, by positivity⟩
  have hC : ∀ p ∈ Metric.ball (0 : ThreeSpace) D, ∀ v : ThreeSpace,
      Real.sqrt (E.outputMetric.inner (f p) (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel f p v)
        (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel f p v)) ≤ C * ‖v‖ := by
    intro p hp v
    have hpU := hSU hp
    let y : standardCapWindow D := ⟨p, hpU⟩
    have hyn : ‖y.val‖ < D := by
      change ‖p‖ < D
      rwa [Metric.mem_ball, dist_zero_right] at hp
    have hD : mfderiv ThreeModel ThreeModel S.window y =
        mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel f p := by
      rw [← hcomp]
      change mfderiv ThreeModel ThreeModel (f ∘ Subtype.val) y = _
      rw [mfderiv_comp y ((hfat y).mdifferentiableAt (by simp))
        ((contMDiff_subtype_val (I := ThreeModel) (U := standardCapWindow D) (n := ∞)).contMDiffAt
          |>.mdifferentiableAt (by simp)),
        DifferentialGeometry.mfderiv_subtype_val]
      rfl
    have hquad := (actual_window_quad_bounds S hcan hε y hyn v).2
    have hstd := StandardCap.metric_inner_le y.val v
    have hfp : f p = S.window y := hfval y
    rw [← hD, hfp]
    set X := E.outputMetric.inner (S.window y) (mfderiv ThreeModel ThreeModel S.window y v)
      (mfderiv ThreeModel ThreeModel S.window y v) with hXdef
    have hX : 0 ≤ X := metric_inner_self_nonneg E.outputMetric _ _
    have hXle : X ≤ (3 / 2) / S.neck.scale * ‖v‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hq]
      nlinarith
    calc Real.sqrt X ≤ Real.sqrt ((3 / 2) / S.neck.scale * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hXle
      _ = C * ‖v‖ := by
        change _ = Real.sqrt (3 / 2) / Real.sqrt S.neck.scale * ‖v‖
        rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ hq.le, Real.sqrt_sq (norm_nonneg v)]
  have hxS : x.val ∈ Metric.ball (0 : ThreeSpace) D := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hx
  have h0S : (0 : ThreeSpace) ∈ Metric.ball (0 : ThreeSpace) D := by
    rw [Metric.mem_ball, dist_self]
    exact (norm_nonneg x.val).trans_lt hx
  have hmain := riemannian_edist_le_on_convex_source E.outputMetric hU hf hSU
    (convex_ball (0 : ThreeSpace) D) hC hxS h0S
  rw [hfval x, show f 0 = S.window ⟨0, hx0⟩ from hfval ⟨0, hx0⟩] at hmain
  refine hmain.trans_eq ?_
  rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  rfl

end MetricCutCapEvent.PresentedStaticCap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
