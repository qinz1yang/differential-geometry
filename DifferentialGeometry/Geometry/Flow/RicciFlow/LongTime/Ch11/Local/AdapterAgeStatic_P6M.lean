import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeCaps_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows

/-!
# G3c（AD-age 收尾，part 1）：`PresentedStaticCap` 的抛物重标度（`_P6M`）

`MetricCutCapEvent.rescale μ`（time ↦ time/μ、metric ↦ μ⁻¹·g）把 incoming slab 换成
`E.incoming.rescale μ`，其 terminal open 与原来只是**命题相等**
（`IncomingSlab.rescale_terminalRegularOpen`），所以 `PresentedStaticCap` 的 neck / witness 不能
直接 cast（witness 沿 `▸` 后 `Output` 字段非定义等）。照树内
`History/CutoffRecordConcatenation` 的私有 `TerminalStaticPresentation`，本文件复写一份以
`(U, h)` 为指标的同构结构 `TerminalStaticPresentation_P6M`：
* `ofPresented` / `toPresented`（字段原样）、`rescale`（neck = G3a `NormalizedNeck.rescale_P6N`、
  witness = G3b `StaticCapWitness.rescale_P6N`、`inclusion_metric` 两侧同乘 `μ⁻¹`）、
  `castOpen`（沿 `U = V` 与度量 `HEq`，by `subst`/`cases`）；
* **`MetricCutCapEvent.PresentedStaticCap.rescale_P6M`** 与几何引理（`delta` 不变、
  `neck.scale ↦ μ · scale`、`sphereMark` / chart 值 / `window` 不变）；
* **`hasCanonicalWindow_rescale_P6M`**：`normalizedDatum.rescaled μ⁻¹` + 树内
  `CanonicalStaticInsertionWitness.rescale`（`StandardCap/StaticWitnessTransport`）；windowMetric
  不变（`rescale_windowMetric_inner_P6M`：`metricScalarAt (μ⁻¹ g) x₀ · μ⁻¹ out = R · out`）。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Window

open DifferentialGeometry.Topology.Manifold.Attachment in
private local instance quotientChartedSpace_P6M {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (StandardCap.InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace StandardCap.transitionEnd_pos hB

open DifferentialGeometry.Topology.Manifold.Attachment in
private local instance quotientIsManifold_P6M {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (StandardCap.InsertionQuotient hB) :=
  radialCapAttachment_isManifold StandardCap.transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

/-- 树内 `CanonicalStaticInsertionWitness.rescale c`（datum `d.rescaled c`）的标准帽窗口度量与原来
逐点相同：`metricScalarAt (c g) x₀ · (c · out) = R · out`（`rescaling_laws`：`windowMap` 不变、
`outMetric ↦ c · outMetric`）。 -/
theorem rescale_windowMetric_inner_P6M
    (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε) (c : ℝ) (hc : 0 < c)
    (hD : 0 < D) (x : standardCapWindow D) (v z : TangentSpace ThreeModel x) :
    (w.rescale c hc hD).windowMetric.inner x v z = w.windowMetric.inner x v z := by
  have hlaw := StandardCap.canonicalStaticInsertionWitness_rescaling_laws w c hc
    (w.rescale c hc hD)
  have hgeo := hlaw.1
  have hout := hlaw.2.1
  have hwin : (w.rescale c hc hD).window = w.window :=
    ContinuousMap.ext fun y => congrFun hgeo.window y
  rw [StandardCap.CanonicalStaticInsertionWitness.window_inner,
    StandardCap.CanonicalStaticInsertionWitness.window_inner, hout, hwin, scaleMetric_inner,
    metricScalarAt_scaleMetric, mul_mul_mul_comm, inv_mul_cancel₀ hc.ne', one_mul]

end Window

section Presentation

variable {P Q D₀ N₀ : OrientedThreeStage.{u}}

private local instance stageSecondCountable_P6M : SecondCountableTopology P.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier

private local instance opensLocallyCompact_P6M (U : TopologicalSpace.Opens P.Carrier) :
    LocallyCompactSpace U :=
  ChartedSpace.locallyCompactSpace ThreeSpace U

private local instance threeFinrank_P6M : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/- 以 terminal open `U` 与其上度量 `h` 为指标的 `PresentedStaticCap` 同构结构（照树内私有
`TerminalStaticPresentation`）；只去掉 incoming slab 的时间指标，几何字段原样。 -/
private structure TerminalStaticPresentation_P6M
    (X : SmoothCutCapTransition P Q D₀ N₀)
    (U : TopologicalSpace.Opens P.Carrier) (h : SmoothRiemannianMetric ThreeModel U)
    (g : Q.Metric) (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (ε : ℝ)
    (b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}) where
  delta : ℝ
  order : ℕ
  neck : NormalizedNeck h delta order
  witness : StaticCapWitness neck fixed D m ε
  inclusion : C(witness.Output, Q.Carrier)
  inclusion_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion
  inclusion_metric : ∀ x V W, witness.metric.inner x V W =
    g.inner (inclusion x) (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W)
  cap_eq : ∀ x : ThreeBall,
    X.trace.presentation (X.trace.capping.cap b.1 x) = Sum.inl (inclusion (witness.cap x))
  attaching_eq : (witness.attaching : Sphere 2 → Sphere 2) = X.trace.capping.attaching b.1
  retainedPoint : (x : neckRetainedCollar delta) →
    {p : X.trace.tubes.core // p ∈ X.trace.retainedCore}
  retained_point_eq : ∀ x : neckRetainedCollar delta, ∀ hx : x.1 ∈ neckBuffer delta,
    (retainedPoint x).1.1 = (neck.chart ⟨x.1, hx⟩).1
  retained_eq : ∀ x,
    X.trace.presentation (X.trace.capping.coreInclusion (retainedPoint x).1) =
      Sum.inl (inclusion (witness.retained x))

namespace TerminalStaticPresentation_P6M

variable {X : SmoothCutCapTransition P Q D₀ N₀} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
  {b : {b : X.trace.tubes.Boundary //
    ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}

private def ofPresented {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b) :
    TerminalStaticPresentation_P6M E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

private def toPresented {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {b : E.RetainedBoundaryIndex}
    (S : TerminalStaticPresentation_P6M E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b) :
    E.PresentedStaticCap fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

/-- `(U, h, g) ↦ (U, μ⁻¹ h, μ⁻¹ g)`：neck / witness 用 G3a / G3b 的重标度，其余原样。 -/
private def rescale {U : TopologicalSpace.Opens P.Carrier}
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) (μ : ℝ) (hμ : 0 < μ) :
    TerminalStaticPresentation_P6M X U (scaleMetric μ⁻¹ (inv_pos.mpr hμ) h)
      (scaleMetric μ⁻¹ (inv_pos.mpr hμ) g) fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck.rescale_P6N μ hμ
  witness := S.witness.rescale_P6N μ hμ
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := by
    intro x V W
    exact congrArg (fun z : ℝ => μ⁻¹ * z) (S.inclusion_metric x V W)
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

/-- 沿 terminal open 相等 `U = V` 与度量 `HEq h h'` 搬运（by `subst` / `cases`）。 -/
private def castOpen {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) :
    TerminalStaticPresentation_P6M X V h' g fixed D m ε b := by
  subst hUV
  obtain rfl := eq_of_heq hh
  exact S

private theorem castOpen_delta {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) :
    (S.castOpen hUV hh).delta = S.delta := by
  subst hUV
  obtain rfl := eq_of_heq hh
  rfl

private theorem castOpen_scale {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) :
    (S.castOpen hUV hh).neck.scale = S.neck.scale := by
  subst hUV
  obtain rfl := eq_of_heq hh
  rfl

private theorem castOpen_sphereMark {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) :
    (S.castOpen hUV hh).neck.sphereMark = S.neck.sphereMark := by
  subst hUV
  obtain rfl := eq_of_heq hh
  rfl

private theorem castOpen_chart_val {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b)
    (x : neckBuffer (S.castOpen hUV hh).delta) (hx : x.1 ∈ neckBuffer S.delta) :
    ((S.castOpen hUV hh).neck.chart x).1 = (S.neck.chart ⟨x.1, hx⟩).1 := by
  subst hUV
  obtain rfl := eq_of_heq hh
  rfl

private theorem castOpen_window {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) :
    (S.castOpen hUV hh).inclusion.comp (S.castOpen hUV hh).witness.window =
      S.inclusion.comp S.witness.window := by
  subst hUV
  obtain rfl := eq_of_heq hh
  rfl

/- `hasCanonicalWindow` 的 `(U, h)` 指标形（照树内私有 `TerminalStaticPresentation.Canonical`）。 -/
private def Canonical {U : TopologicalSpace.Opens P.Carrier}
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) : Prop :=
  ∃ (x₀ : U) (δ : ℝ) (k : ℕ) (d : normalizedDatum h x₀ δ k)
    (w : StandardCap.CanonicalStaticInsertionWitness
      d fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt h x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * g.inner ((S.inclusion.comp S.witness.window) x)
        (mfderiv ThreeModel ThreeModel (S.inclusion.comp S.witness.window) x v)
        (mfderiv ThreeModel ThreeModel (S.inclusion.comp S.witness.window) x z)) ∧
    ∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ StandardCap.transitionEnd ∧
      (S.inclusion.comp S.witness.window) x = S.inclusion (S.witness.cap z)

private theorem castOpen_canonical {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) (hS : S.Canonical) :
    (S.castOpen hUV hh).Canonical := by
  subst hUV
  obtain rfl := eq_of_heq hh
  exact hS

private theorem real_rescale_mul_P6M {μ : ℝ} (hμ : 0 < μ) (s Y : ℝ) :
    s * Y = μ * s * (μ⁻¹ * Y) := by
  field_simp

/-- 重标度保持 canonical window：datum `d.rescaled μ⁻¹`、witness `w.rescale μ⁻¹`。 -/
private theorem rescale_canonical {U : TopologicalSpace.Opens P.Carrier}
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    (S : TerminalStaticPresentation_P6M X U h g fixed D m ε b) (hS : S.Canonical)
    (μ : ℝ) (hμ : 0 < μ) : (S.rescale μ hμ).Canonical := by
  obtain ⟨x₀, δ, k, d, w, hscal, hwin, hcap⟩ := hS
  refine ⟨x₀, δ, k, d.rescaled μ⁻¹ (inv_pos.mpr hμ),
    w.rescale μ⁻¹ (inv_pos.mpr hμ) S.witness.radius_pos, ?_, ?_, hcap⟩
  · change metricScalarAt (scaleMetric μ⁻¹ (inv_pos.mpr hμ) h) x₀ = μ * S.neck.scale
    rw [metricScalarAt_scaleMetric, inv_inv, hscal]
  · intro x v z
    rw [rescale_windowMetric_inner_P6M, hwin x v z]
    exact real_rescale_mul_P6M hμ _ _

private theorem toPresented_canonical {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {b : E.RetainedBoundaryIndex}
    (S : TerminalStaticPresentation_P6M E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b) (hS : S.Canonical) :
    S.toPresented.hasCanonicalWindow := hS

private theorem ofPresented_canonical {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b)
    (hS : S.hasCanonicalWindow) : (ofPresented S).Canonical := hS

end TerminalStaticPresentation_P6M

namespace MetricCutCapEvent.PresentedStaticCap

variable {a s : ℝ} {E : MetricCutCapEvent P Q a s} {fixed : StaticCapScaffold} {D ε : ℝ}
  {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- **`_P6M`**：presented static cap 的抛物重标度（`E ↦ E.rescale μ`）：neck `scale ↦ μ · scale`、
witness 度量 × `μ⁻¹`、inclusion / cap / retained 数据原样，沿 terminal open 相等搬运。 -/
def rescale_P6M (S : E.PresentedStaticCap fixed D m ε b) (μ : ℝ) (hμ : 0 < μ) :
    (E.rescale μ hμ).PresentedStaticCap fixed D m ε b :=
  TerminalStaticPresentation_P6M.toPresented
    (((TerminalStaticPresentation_P6M.ofPresented S).rescale μ hμ).castOpen
      (E.incoming.rescale_terminalRegularOpen μ hμ).symm
      (E.terminal.rescale_metric_heq_P6N μ hμ).symm)

theorem rescale_P6M_delta (S : E.PresentedStaticCap fixed D m ε b) (μ : ℝ) (hμ : 0 < μ) :
    (S.rescale_P6M μ hμ).delta = S.delta :=
  TerminalStaticPresentation_P6M.castOpen_delta _ _ _

theorem rescale_P6M_scale (S : E.PresentedStaticCap fixed D m ε b) (μ : ℝ) (hμ : 0 < μ) :
    (S.rescale_P6M μ hμ).neck.scale = μ * S.neck.scale :=
  TerminalStaticPresentation_P6M.castOpen_scale _ _ _

theorem rescale_P6M_sphereMark (S : E.PresentedStaticCap fixed D m ε b) (μ : ℝ)
    (hμ : 0 < μ) : (S.rescale_P6M μ hμ).neck.sphereMark = S.neck.sphereMark :=
  TerminalStaticPresentation_P6M.castOpen_sphereMark _ _ _

theorem rescale_P6M_chart_val (S : E.PresentedStaticCap fixed D m ε b) (μ : ℝ) (hμ : 0 < μ)
    (x : neckBuffer (S.rescale_P6M μ hμ).delta) (hx : x.1 ∈ neckBuffer S.delta) :
    ((S.rescale_P6M μ hμ).neck.chart x).1 = (S.neck.chart ⟨x.1, hx⟩).1 :=
  TerminalStaticPresentation_P6M.castOpen_chart_val _ _ _ x hx

theorem rescale_P6M_window (S : E.PresentedStaticCap fixed D m ε b) (μ : ℝ) (hμ : 0 < μ) :
    (S.rescale_P6M μ hμ).window = S.window :=
  TerminalStaticPresentation_P6M.castOpen_window _ _ _

/-- **`_P6M`**：重标度保持 `hasCanonicalWindow`。 -/
theorem hasCanonicalWindow_rescale_P6M (S : E.PresentedStaticCap fixed D m ε b)
    (hS : S.hasCanonicalWindow) (μ : ℝ) (hμ : 0 < μ) :
    (S.rescale_P6M μ hμ).hasCanonicalWindow := by
  unfold rescale_P6M
  have h1 := TerminalStaticPresentation_P6M.ofPresented_canonical S hS
  have h2 := (TerminalStaticPresentation_P6M.ofPresented S).rescale_canonical h1 μ hμ
  have h3 := ((TerminalStaticPresentation_P6M.ofPresented S).rescale μ hμ).castOpen_canonical
    (E.incoming.rescale_terminalRegularOpen μ hμ).symm
    (E.terminal.rescale_metric_heq_P6N μ hμ).symm h2
  exact TerminalStaticPresentation_P6M.toPresented_canonical _ h3

end MetricCutCapEvent.PresentedStaticCap

end Presentation

/-- consumer：重标度 cap 仍有 canonical window，且 `neck.scale ↦ μ · scale`、`window` 不变。 -/
example {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow) (μ : ℝ) (hμ : 0 < μ) :
    (S.rescale_P6M μ hμ).hasCanonicalWindow ∧
      (S.rescale_P6M μ hμ).neck.scale = μ * S.neck.scale ∧
      (S.rescale_P6M μ hμ).window = S.window :=
  ⟨S.hasCanonicalWindow_rescale_P6M hS μ hμ, S.rescale_P6M_scale μ hμ, S.rescale_P6M_window μ hμ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
