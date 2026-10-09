import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction

set_option autoImplicit false

/-!
# S-CH11-REPROVE-B (G2)：`PresentedStaticCap` 的 canonical window 限制

按 reference 重证 astra `ST/PresentedStaticCapRestriction.lean`（W8 里编不过：`window_inner` 一步
`rw [restrictSubset_inner, …]` 的 pull-back 形找不到模式——`restrictOpenOfSubset` 的 `inner`
在 `V : TangentSpace x` 与 `TangentSpace (inclusion x)` 之间只 defeq，不 syntactic）。
这里把那一步改成 `refine (S.witness.window_inner (inclusion x) V W).trans ?_`（defeq 靠
elaborator 统一），其余逐字沿用。

* `weakenOrderAccuracy_C11RB`：降低 order、放宽 accuracy 保持 insertion data；
* `restrictCanonicalWindow_C11RB`：把真实 cap 的 window 限制到更小的 `D' ≤ D`（保持 carrier、
  metric 与几何映射）；
* `hasCanonicalWindow_restrictCanonicalWindow_C11RB`：窗口仍含 cap core
  （`transitionEnd < D' + 1`）时 canonical window 保持。
-/
noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
  {D ε ε' : ℝ} {m m' : ℕ}

/-- Lowering the asserted order and enlarging its error keeps the insertion data. -/
def weakenOrderAccuracy_C11RB (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (hm : m' ≤ m) (hε : ε ≤ ε') :
    CanonicalStaticInsertionWitness d A hA D m' ε' where
  data := w.data
  properties := { w.properties with
    window_close :=
      ((metricDerivENormSupOn_mono (Subset.rfl) hm _ _ _).trans_lt
        w.properties.window_close).trans_le (ENNReal.ofReal_le_ofReal hε) }

@[simp] theorem weakenOrderAccuracy_C11RB_data
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (hm : m' ≤ m) (hε : ε ≤ ε') :
    (w.weakenOrderAccuracy_C11RB hm hε).data = w.data := rfl

@[simp] theorem weakenOrderAccuracy_C11RB_windowMetric
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (hm : m' ≤ m) (hε : ε ≤ ε') :
    (w.weakenOrderAccuracy_C11RB hm hε).windowMetric = w.windowMetric := rfl

end DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D D' ε ε' : ℝ} {m m' : ℕ}
  {b : E.RetainedBoundaryIndex}

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem restricted_window_closeness_C11RB
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow)
    (hD' : 0 < D') (hD'D : D' ≤ D) (hm : m' ≤ m) (hε : ε ≤ ε') :
    metricDerivNormSupOn {x : standardCapWindow D' | ‖x.val‖ < D'} m'
      (S.witness.windowMetric.restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add hD'D (le_refl 1)) :
          standardCapWindow D' ≤ standardCapWindow D))
      (standardCapMetric.restrictOpen (standardCapWindow D'))
      (standardCapMetric.restrictOpen (standardCapWindow D')) < ε' := by
  obtain ⟨x₀, δ, k, d, w, _, hmetric, _⟩ := hS
  have heq : w.windowMetric = S.witness.windowMetric :=
    SmoothRiemannianMetric.ext_inner fun x v z =>
      (hmetric x v z).trans (S.window_inner x v z).symm
  have hclose := ((w.weakenOrderAccuracy_C11RB hm hε).restrictWindow hD' hD'D).window_closeness
  rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric,
    StandardCap.CanonicalStaticInsertionWitness.weakenOrderAccuracy_C11RB_windowMetric,
    heq] at hclose
  exact hclose

/-- Restrict an actual cap's window while retaining its carrier, metric and geometric maps. -/
def restrictCanonicalWindow_C11RB
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow)
    (hD' : 0 < D') (hD'D : D' ≤ D) (hm : m' ≤ m) (hε : ε ≤ ε') :
    E.PresentedStaticCap fixed D' m' ε' b := by
  let hsub : standardCapWindow D' ≤ standardCapWindow D :=
    fun _ hx => hx.trans_le (add_le_add hD'D (le_refl 1))
  let incl : C(standardCapWindow D', standardCapWindow D) :=
    ⟨TopologicalSpace.Opens.inclusion hsub,
      (contMDiff_inclusion (I := ThreeModel) (n := ∞) hsub).continuous⟩
  letI := S.witness.ballCharts
  letI := S.witness.ballSmooth
  letI := S.witness.retainedCharts
  letI := S.witness.retainedSmooth
  letI := S.witness.modelCoreCharts
  letI := S.witness.modelCoreSmooth
  letI := S.witness.quotientCharts
  letI := S.witness.quotientSmooth
  let witness : StaticCapWitness S.neck fixed D' m' ε' := {
    S.witness with
    radius_pos := hD'
    accuracy_pos := S.witness.accuracy_pos.trans_le hε
    window := S.witness.window.comp incl
    window_smooth := S.witness.window_smooth.comp
      (isSmoothEmbedding_opens_inclusion hsub) (by simp)
    window_tip := fun hx => S.witness.window_tip (hsub hx)
    windowMetric := S.witness.windowMetric.restrictOpenOfSubset hsub
    window_inner := by
      intro x V W
      change (S.witness.windowMetric.restrictOpenOfSubset hsub).inner x V W =
        S.neck.scale * S.witness.metric.inner
          (S.witness.window (TopologicalSpace.Opens.inclusion hsub x))
          (mfderiv ThreeModel ThreeModel
            ((S.witness.window : standardCapWindow D → S.witness.Output) ∘
              TopologicalSpace.Opens.inclusion hsub) x V)
          (mfderiv ThreeModel ThreeModel
            ((S.witness.window : standardCapWindow D → S.witness.Output) ∘
              TopologicalSpace.Opens.inclusion hsub) x W)
      refine (S.witness.window_inner (TopologicalSpace.Opens.inclusion hsub x) V W).trans ?_
      have hmd : MDifferentiableAt ThreeModel ThreeModel
          (S.witness.window : standardCapWindow D → S.witness.Output)
          (TopologicalSpace.Opens.inclusion hsub x) :=
        S.witness.window_smooth.contMDiff.mdifferentiableAt (by simp)
      have hmd' : MDifferentiableAt ThreeModel ThreeModel
          (TopologicalSpace.Opens.inclusion hsub) x :=
        (contMDiff_inclusion (I := ThreeModel) (n := ∞) hsub).contMDiffAt.mdifferentiableAt
          (by decide : (∞ : WithTop ℕ∞) ≠ 0)
      rw [mfderiv_comp_apply x (f := TopologicalSpace.Opens.inclusion hsub)
          (g := (S.witness.window : standardCapWindow D → S.witness.Output)) hmd hmd' V,
        mfderiv_comp_apply x (f := TopologicalSpace.Opens.inclusion hsub)
          (g := (S.witness.window : standardCapWindow D → S.witness.Output)) hmd hmd' W,
        mfderiv_opens_incl (I := ThreeModel) hsub x]
      rfl
    window_closeness := S.restricted_window_closeness_C11RB hS hD' hD'D hm hε
    window_deep := fun x hx hx' hc => S.witness.window_deep x hx (hsub hx') hc }
  exact { S with witness := witness }

variable (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow)
  (hD' : 0 < D') (hD'D : D' ≤ D) (hm : m' ≤ m) (hε : ε ≤ ε')

@[simp] theorem restrictCanonicalWindow_C11RB_delta :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).delta = S.delta := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_order :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).order = S.order := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_neck :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).neck = S.neck := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_Output :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.Output = S.witness.Output := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_metric :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.metric = S.witness.metric := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_inclusion :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).inclusion = S.inclusion := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_cap :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.cap = S.witness.cap := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_retained :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.retained = S.witness.retained := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_collapse :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.collapse = S.witness.collapse := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_tip :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.tip = S.witness.tip := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_capChart :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.capChart = S.witness.capChart := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_retainedPoint :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).retainedPoint = S.retainedPoint := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_window (x : standardCapWindow D') :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).window x =
      S.window ⟨x.val, x.property.trans_le (add_le_add hD'D (le_refl 1))⟩ := rfl

@[simp] theorem restrictCanonicalWindow_C11RB_windowMetric :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.windowMetric =
      S.witness.windowMetric.restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add hD'D (le_refl 1)) :
          standardCapWindow D' ≤ standardCapWindow D) := rfl

/-- Original cap coverage survives when the smaller window still contains the cap core. -/
theorem hasCanonicalWindow_restrictCanonicalWindow_C11RB
    (hcap : StandardCap.transitionEnd < D' + 1) :
    (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).hasCanonicalWindow := by
  have hSdata := hS
  obtain ⟨x₀, δ, k, d, w, hscale, hmetric, hcover⟩ := hSdata
  let w' := (w.weakenOrderAccuracy_C11RB hm hε).restrictWindow hD' hD'D
  have heq : w.windowMetric = S.witness.windowMetric :=
    SmoothRiemannianMetric.ext_inner fun x v z =>
      (hmetric x v z).trans (S.window_inner x v z).symm
  have heq' : w'.windowMetric =
      (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).witness.windowMetric := by
    rw [restrictCanonicalWindow_C11RB_windowMetric]
    dsimp only [w']
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric,
      StandardCap.CanonicalStaticInsertionWitness.weakenOrderAccuracy_C11RB_windowMetric, heq]
  refine ⟨x₀, δ, k, d, w', hscale, ?_, ?_⟩
  · intro x v z
    rw [heq']
    exact (S.restrictCanonicalWindow_C11RB hS hD' hD'D hm hε).window_inner x v z
  · intro z
    obtain ⟨x, hx, hpoint⟩ := hcover z
    let y : standardCapWindow D' := ⟨x.val, hx.trans_lt hcap⟩
    refine ⟨y, hx, ?_⟩
    change S.window
      ⟨x.val, (hx.trans_lt hcap).trans_le (add_le_add hD'D (le_refl 1))⟩ =
        S.inclusion (S.witness.cap z)
    exact hpoint

end MetricCutCapEvent.PresentedStaticCap
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
