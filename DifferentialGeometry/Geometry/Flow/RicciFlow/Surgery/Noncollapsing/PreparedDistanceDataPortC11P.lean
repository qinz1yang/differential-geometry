import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedNativeCertificateData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar

/-!
# S-CH11-FIX8 port of astra `PreparedDistanceData`（`PortC11P`）

来源：donor `PreparedDistanceData.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（1 个 error）。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `PreparedDistanceClassProvider.toNative` 的假设 `PreparedDistanceClassProvider …` 与结论
  `PreparedClassProviderWithNative (fun K => …)` 里的 universe 都不被约束，定理多出自由 universe
  参数，`@h P …` 报 universe 不匹配：两处都写 `.{u}`（同一个项）；
* 陈述里未引用的 binder `IL` 改成 `_IL`（alpha-重命名，同一命题；消 unused-variable warning）。

原路径 `PreparedDistanceData` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
def PreparedGeometricObservationExtensionWithDistance
    (Cdist : ℝ≥0)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B ε κ : ℝ)
    (p₀ : CutoffParameters) (δb ρb : ℝ) : Prop :=
    PreparedGeometricObservationExtensionWithNative
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist) P g B ε κ p₀ δb ρb

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedGeometricObservationExtensionWithDistance.toNative
    {Cdist : ℝ≥0} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {B ε κ : ℝ} {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtensionWithDistance Cdist P g B ε κ p₀ δb ρb) :
    PreparedGeometricObservationExtensionWithNative
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist) P g B ε κ p₀ δb ρb := by
  exact h

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedGeometricObservationExtensionWithDistance.forget
    {Cdist : ℝ≥0} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {B ε κ : ℝ} {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtensionWithDistance Cdist P g B ε κ p₀ δb ρb) :
    PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb := by
  exact PreparedGeometricObservationExtensionWithNative.forget h

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
def PreparedDistanceClassProvider
    (fixed : StaticCapScaffold) (recenter : ℝ) (Cdist : ℝ≥0) : Prop :=
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
      0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
    ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
      p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
      mcapRequest ≤ p₀.modelOrder ∧
      p₀.modelAccuracy ≤ 1 / 2 ∧ standardCapL + 1 ≤ p₀.modelRadius ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      (∀ (L : RetainedCoreHistory.{u}) (_IL : InitialIdentification P g L.toHistory)
        (pL : CutoffParameters)
        (R : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
        L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb R →
        L.NoncollapsedBefore κ ε L.horizon) ∧
      PreparedGeometricObservationExtensionWithDistance Cdist P g B ε κ p₀ δb ρb

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedDistanceClassProvider.toNative
    {Cdist : ℝ≥0} {fixed : StaticCapScaffold} {recenter : ℝ}
    (h : PreparedDistanceClassProvider.{u} fixed recenter Cdist) :
    PreparedClassProviderWithNative.{u}
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter := by
  intro P g B nativeProjectionx1
  have nativeProjectionh2 := @h P g B nativeProjectionx1
  obtain ⟨ε, κ, nativeProjectionh3⟩ := nativeProjectionh2
  refine ⟨ε, κ, ?_⟩
  obtain ⟨nativeProjectionfield4, nativeProjectionfield5, nativeProjectionfield6,
    nativeProjectionh7⟩ := nativeProjectionh3
  refine ⟨nativeProjectionfield4, nativeProjectionfield5, nativeProjectionfield6, ?_⟩
  intro δcap ρcap εcapRequest DcapRequest mcapRequest nativeProjectionx8 nativeProjectionx9
    nativeProjectionx10 nativeProjectionx11
  have nativeProjectionh12 := @nativeProjectionh7 δcap ρcap εcapRequest DcapRequest mcapRequest
    nativeProjectionx8 nativeProjectionx9 nativeProjectionx10 nativeProjectionx11
  obtain ⟨p₀, δb, ρb, nativeProjectionh13⟩ := nativeProjectionh12
  refine ⟨p₀, δb, ρb, ?_⟩
  obtain ⟨nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22, nativeProjectionh23⟩
    := nativeProjectionh13
  refine ⟨nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22, ?_⟩
  obtain ⟨nativeProjectionfield24, nativeProjectionfield25, nativeProjectionfield26,
    nativeProjectionh27⟩ := ((nativeProjectionh23.2).2)
  refine ⟨nativeProjectionfield24, nativeProjectionfield25, nativeProjectionfield26, ?_⟩
  exact nativeProjectionh27

end GC.GeneralFlow
