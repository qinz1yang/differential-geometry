import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialScalarUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceData

/-!
# S-CH11-FIX12 patched-at-path `PreparedClosedBirthClass`

来源：donor `PreparedClosedBirthClass.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）。patched-at-path：下游 `PreparedOverlapClosedBirth` 对它做
`open private … from` 原路径，故不做 PortC11P + shim（原路径文本 = 本文件）：
* 两处陈述里 `PreparedDistanceClassProvider fixed recenter Cdist` 的 universe 被自动成 `u_1`，而
  证明体全是 `.{u}`（"constant has level params [u, u_1] but expected [u_1]"）→ 陈述里写
  `PreparedDistanceClassProvider.{u}`；
* 陈述里只出现、证明不引用的 binder（`I` / `IV` / `IL`，共 11 处）加 `_` 前缀（unusedVariables；
  binder 名不改变陈述）；
* 两处孤立 `·`（单独一行后接 `exact`）合并成 `· exact …`（风格 linter）。
（初稿由 S-CH11-FIX11 在 overlay 探得，02:46 overlay exit 0；FIX12 接手落树。）
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow
universe u

/-- Prepare one exact class from the common scaffold and the paid combined
analytic provider. The original-metric zero-time bound precedes the horizon,
birth threshold, class quality, actual histories and fine requests. The class
retains its own extension callback and the combined physical control callback. -/
private theorem exists_prepared_closed_birth_class_before_quality_with_native_certificate_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedClassProviderWithNative certificate fixed recenter)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      Dstar ≤ p₀.modelRadius ∧ p₀.modelAccuracy ≤ εReserve ∧
      2 ≤ p₀.modelOrder ∧ 32 * Qall * ρb ^ 2 ≤ 1 ∧
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtensionWithNative certificate P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  obtain ⟨Qzero, hQzero, zeroBound⟩ := exists_scalar_lt_at_initial_metric P g
  refine ⟨Qzero, hQzero, zeroBound, ?_⟩
  intro B hB
  obtain ⟨εClass, κClass, hεClass, hεClass11, hκClass, prepare⟩ := prepareClass P g B hB
  obtain ⟨κ, hκ, enlarge⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκClass hεClass hε
  obtain ⟨qcan, qs, Qbirth, δAnal, ρAnal, εAnal, DAnal, mAnal,
    hqcan, hqs, hqsC, hQbirth, hδAnal, hρAnal, hεAnal, _hDAnal, control⟩ :=
    analytic P g B κ hB hκ
  have hQallPos : 0 < max Qbirth Qzero := hQzero.trans_le (le_max_right _ _)
  have hRoot : 0 < Real.sqrt (64 * max Qbirth Qzero) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) hQallPos)
  obtain ⟨p₀, δb, ρb, hfixed, hrc, hδb, hδAnalBound, hρb, hρRequest,
    haccRequest, hradRequest, hordRequest, hcap, hrec, classNC, extension⟩ :=
    prepare δAnal (min ρAnal (Real.sqrt (64 * max Qbirth Qzero))⁻¹)
      (min εAnal εReserve) (max DAnal Dstar) (max mAnal 2)
      hδAnal (lt_min hρAnal (inv_pos.mpr hRoot))
      (lt_min hεAnal hεReserve) (hDstar.trans_le (le_max_right _ _))
  have hρAnalBound : ρb ≤ ρAnal := hρRequest.trans (min_le_left _ _)
  have hρRoot : ρb ≤ (Real.sqrt (64 * max Qbirth Qzero))⁻¹ :=
    hρRequest.trans (min_le_right _ _)
  have hacc : p₀.modelAccuracy ≤ εAnal := haccRequest.trans (min_le_left _ _)
  have hrad : DAnal ≤ p₀.modelRadius := (le_max_left _ _).trans hradRequest
  have hord : mAnal ≤ p₀.modelOrder := (le_max_left _ _).trans hordRequest
  have hReserveRadius : Dstar ≤ p₀.modelRadius := (le_max_right _ _).trans hradRequest
  have hReserveAccuracy : p₀.modelAccuracy ≤ εReserve :=
    haccRequest.trans (min_le_right _ _)
  have hReserveOrder : 2 ≤ p₀.modelOrder := (le_max_right _ _).trans hordRequest
  have hReserveScale : 32 * max Qbirth Qzero * ρb ^ 2 ≤ 1 := by
    have hprod : ρb * Real.sqrt (64 * max Qbirth Qzero) ≤ 1 :=
      (le_div_iff₀ hRoot).mp (by simpa only [one_div] using hρRoot)
    have hprodSq : (ρb * Real.sqrt (64 * max Qbirth Qzero)) ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        pow_le_pow_left₀ (mul_nonneg hρb.le (Real.sqrt_nonneg _)) hprod 2
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hQallPos.le)] at hprodSq
    nlinarith only [hprodSq]
  refine ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, max Qbirth Qzero,
    hReserveRadius, hReserveAccuracy, hReserveOrder, hReserveScale,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, rfl, hQzero.trans_le (le_max_right _ _),
    hcap, hrec, extension, ?_⟩
  intro V IV pV records hVB hclass
  have hnc := enlarge V V.horizon (classNC V IV pV records hVB hclass)
  exact ⟨hnc, control p₀ δb ρb hacc hrad hord hδAnalBound hρAnalBound hrec
    V IV pV records hVB hclass hnc⟩

/-- Retain the original native API by projecting the same strengthened engine. -/
private theorem exists_prepared_closed_birth_class_before_quality_with_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedClassProviderWithNative certificate fixed recenter)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtensionWithNative certificate P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  obtain ⟨Qzero, hQzero, zeroBound, prepare⟩ :=
    exists_prepared_closed_birth_class_before_quality_with_native_certificate_with_reserve_quality
      1 1 one_pos one_pos certificate fixed recenter prepareClass
      ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε analytic P g
  refine ⟨Qzero, hQzero, zeroBound, ?_⟩
  intro B hB
  obtain ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall,
    _, _, _, _, hOld⟩ := prepare B hB
  exact ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall, hOld⟩

/-- Compatibility projection of the same generic native construction. -/
theorem exists_prepared_closed_birth_class_before_quality
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
      ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
      ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
        0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
      ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
        p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
        0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
        p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
        mcapRequest ≤ p₀.modelOrder ∧
        StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
        p₀.recenterConstant * δb ≤ 1 / 2 ∧
        (∀ (L : RetainedCoreHistory.{u}) (_IL : InitialIdentification P g L.toHistory)
          (pL : CutoffParameters)
          (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
          L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          L.NoncollapsedBefore κ ε L.horizon) ∧
        PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtension P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  have nativeResult :=
    @exists_prepared_closed_birth_class_before_quality_with_native_certificate.{u} (fun _ => True)
    fixed recenter (PreparedClassProviderWithNative.of_weak prepareClass) ε C1 C2 C1s C2s Cs τmin
    Cbirth Ctime Cgrad hε analytic P g
  obtain ⟨Qzero, nativeProjectionh1⟩ := nativeResult
  refine ⟨Qzero, ?_⟩
  obtain ⟨nativeProjectionfield2, nativeProjectionfield3, nativeProjectionh4⟩ := nativeProjectionh1
  refine ⟨nativeProjectionfield2, nativeProjectionfield3, ?_⟩
  intro B nativeProjectionx5
  have nativeProjectionh6 := @nativeProjectionh4 B nativeProjectionx5
  obtain ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall, nativeProjectionh7⟩ :=
    nativeProjectionh6
  refine ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall, ?_⟩
  obtain ⟨nativeProjectionfield8, nativeProjectionfield9, nativeProjectionfield10,
    nativeProjectionfield11, nativeProjectionfield12, nativeProjectionfield13,
    nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionh24⟩ := nativeProjectionh7
  refine ⟨nativeProjectionfield8, nativeProjectionfield9, nativeProjectionfield10,
    nativeProjectionfield11, nativeProjectionfield12, nativeProjectionfield13,
    nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, ?_⟩
  refine ⟨?_, ?_⟩
  · exact PreparedGeometricObservationExtensionWithNative.forget nativeProjectionh24.1
  · exact nativeProjectionh24.2

/-- The same native construction retaining the actual event distance certificate. -/
theorem exists_prepared_closed_birth_class_before_quality_with_distance_scalars
    (Cdist : ℝ≥0)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedDistanceClassProvider.{u} fixed recenter Cdist)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtensionWithDistance Cdist P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  exact @exists_prepared_closed_birth_class_before_quality_with_native_certificate.{u} (fun K => ∀ i
    : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter
    prepareClass.toNative ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε analytic P g

/-- Retain all four reserve bounds with the original distance certificate. -/
theorem exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (Cdist : ℝ≥0)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedDistanceClassProvider.{u} fixed recenter Cdist)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      Dstar ≤ p₀.modelRadius ∧ p₀.modelAccuracy ≤ εReserve ∧
      2 ≤ p₀.modelOrder ∧ 32 * Qall * ρb ^ 2 ≤ 1 ∧
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtensionWithDistance Cdist P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  exact @exists_prepared_closed_birth_class_before_quality_with_native_certificate_with_reserve_quality.{u}
    Dstar εReserve hDstar hεReserve (fun K => ∀ i : Fin K.eventCount,
      (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter
    prepareClass.toNative ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε analytic P g

end GC.GeneralFlow
