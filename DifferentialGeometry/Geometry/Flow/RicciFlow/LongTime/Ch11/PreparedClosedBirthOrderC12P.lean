import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedClosedBirthClass

/-!
# PreparedClosedBirthClass 的 `∀ mmod` 导出孪生（车道 C12-3，后缀 `_C12P`）

事实（`PreparedClosedBirthClass.lean:40–178` 私有引擎）：class preparer `prepare` 的 order 请求是任意
`ℕ`——原证明请求 `max (max mAnal mS) 2`，内部用 `mAnal ≤ modelOrder`（analytic 的 `mcap`）与
`mS ≤ modelOrder`（S16 uniform packet），导出时只留 `2 ≤ modelOrder`（`:401` 公开形）。
本文件是两层定理的孪生（新名字，原文件不动）：请求改成 `max (max mAnal mS) (max 2 mmod)`，
导出多一条 `mmod ≤ p₀.modelOrder`（`mmod` 由调用方在 `P g` 之前给定；`Dstar` 原本就任意）。
其余陈述、证明逐字。
* `exists_prepared_class_native_order_C12P`（私有引擎孪生，certificate 泛型）；
* `exists_prepared_class_distance_order_C12P`（`:401` 公开形孪生）。
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

/-- **私有引擎的 `∀ mmod` 孪生**：`2 ≤ p₀.modelOrder` 之后多 `mmod ≤ p₀.modelOrder`。 -/
theorem exists_prepared_class_native_order_C12P
    (Dstar εReserve : ℝ) (mmod : ℕ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedClassProviderWithNative certificate fixed recenter)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
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
      2 ≤ p₀.modelOrder ∧ mmod ≤ p₀.modelOrder ∧ 32 * Qall * ρb ^ 2 ≤ 1 ∧
      (∃ C1h C2h qh : ℝ, 1 ≤ C1h ∧ 1 ≤ C2h ∧ C1h ≤ strongC1_C11SC.{u} ε C1 ∧
        C2h ≤ strongC2_C11SC.{u} ε C2 Cgrad ∧ qs ≤ qh ∧
        ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
          (pV : CutoffParameters)
          (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
          V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          RecordHypFar_C12X (5 / 4) V records →
          V.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last V.eventCount) ∧
          ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
            V.StronglyCanonicalBeforeFull_C12X (Fin.last V.eventCount)
              ((V.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1h C2h qh
              V.horizon) ∧
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
  have hU := native_strongFull_uniform_radial_spec_C11SC.{u} hε hstr.2.2.2.2.2
  obtain ⟨qh, δS, ρS, εS, DS, mS, hqh, hδS, hρS, hεS, hDS, hX⟩ :=
    hU P g B hB C1 C2 C1s C2s qcan qs τmin Ctime Cgrad κ hstr.1 hstr.2.1 hstr.2.2.1
      hstr.2.2.2.1 hqcan hqs hstr.2.2.2.2.1 hκ
  have hQallPos : 0 < max Qbirth Qzero := hQzero.trans_le (le_max_right _ _)
  have hRoot : 0 < Real.sqrt (64 * max Qbirth Qzero) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) hQallPos)
  obtain ⟨p₀, δb, ρb, hfixed, hrc, hδb, hδAnalBound, hρb, hρRequest,
    haccRequest, hradRequest, hordRequest, hcap, hrec, classNC, extension⟩ :=
    prepare (min δAnal δS) (min (min ρAnal ρS) (Real.sqrt (64 * max Qbirth Qzero))⁻¹)
      (min (min εAnal εS) εReserve) (max (max DAnal DS) Dstar) (max (max mAnal mS) (max 2 mmod))
      (lt_min hδAnal hδS) (lt_min (lt_min hρAnal hρS) (inv_pos.mpr hRoot))
      (lt_min (lt_min hεAnal hεS) hεReserve) (hDstar.trans_le (le_max_right _ _))
  have hδAnalB : δb ≤ δAnal := hδAnalBound.trans (min_le_left _ _)
  have hδSB : δb ≤ δS := hδAnalBound.trans (min_le_right _ _)
  have hρAnalBound : ρb ≤ ρAnal :=
    hρRequest.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρSB : ρb ≤ ρS := hρRequest.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρRoot : ρb ≤ (Real.sqrt (64 * max Qbirth Qzero))⁻¹ :=
    hρRequest.trans (min_le_right _ _)
  have hacc : p₀.modelAccuracy ≤ εAnal :=
    haccRequest.trans ((min_le_left _ _).trans (min_le_left _ _))
  have haccS : p₀.modelAccuracy ≤ εS :=
    haccRequest.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrad : DAnal ≤ p₀.modelRadius :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hradRequest
  have hradS : DS ≤ p₀.modelRadius :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hradRequest
  have hord : mAnal ≤ p₀.modelOrder :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hordRequest
  have hordS : mS ≤ p₀.modelOrder :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hordRequest
  have hReserveRadius : Dstar ≤ p₀.modelRadius := (le_max_right _ _).trans hradRequest
  have hReserveAccuracy : p₀.modelAccuracy ≤ εReserve :=
    haccRequest.trans (min_le_right _ _)
  have hReserveOrder : 2 ≤ p₀.modelOrder :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hordRequest
  have hReqOrder : mmod ≤ p₀.modelOrder :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hordRequest
  have hReserveScale : 32 * max Qbirth Qzero * ρb ^ 2 ≤ 1 := by
    have hprod : ρb * Real.sqrt (64 * max Qbirth Qzero) ≤ 1 :=
      (le_div_iff₀ hRoot).mp (by simpa only [one_div] using hρRoot)
    have hprodSq : (ρb * Real.sqrt (64 * max Qbirth Qzero)) ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        pow_le_pow_left₀ (mul_nonneg hρb.le (Real.sqrt_nonneg _)) hprod 2
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hQallPos.le)] at hprodSq
    nlinarith only [hprodSq]
  refine ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, max Qbirth Qzero,
    hReserveRadius, hReserveAccuracy, hReserveOrder, hReqOrder, hReserveScale,
    ⟨strongC1_C11SC.{u} ε C1, strongC2_C11SC.{u} ε C2 Cgrad, qh,
      one_le_strongC1_C11SC hstr.1 ε, one_le_strongC2_C11SC hstr.2.1 ε Cgrad, le_rfl, le_rfl,
      hqh, ?_⟩,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, rfl, hQzero.trans_le (le_max_right _ _),
    hcap, hrec, extension, ?_⟩
  · intro V IV pV records hVB hclass hrecHyp
    have hnc := enlarge V V.horizon (classNC V IV pV records hVB hclass)
    exact hX p₀ δb ρb haccS hradS hordS hδSB hρSB hrec V IV pV records hVB hclass hrecHyp hnc
      (control p₀ δb ρb hacc hrad hord hδAnalB hρAnalBound hrec
        V IV pV records hVB hclass hnc).1
  · intro V IV pV records hVB hclass
    have hnc := enlarge V V.horizon (classNC V IV pV records hVB hclass)
    exact ⟨hnc, control p₀ δb ρb hacc hrad hord hδAnalB hρAnalBound hrec
      V IV pV records hVB hclass hnc⟩


/-- **`:401` 公开形的 `∀ mmod` 孪生**（distance-scalar certificate）：`2 ≤ p₀.modelOrder` 之后多
`mmod ≤ p₀.modelOrder`；`Dstar` 任意（原本就是）。 -/
theorem exists_prepared_class_distance_order_C12P
    (Dstar εReserve : ℝ) (mmod : ℕ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (Cdist : ℝ≥0)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedDistanceClassProvider.{u} fixed recenter Cdist)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
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
      2 ≤ p₀.modelOrder ∧ mmod ≤ p₀.modelOrder ∧ 32 * Qall * ρb ^ 2 ≤ 1 ∧
      (∃ C1h C2h qh : ℝ, 1 ≤ C1h ∧ 1 ≤ C2h ∧ C1h ≤ strongC1_C11SC.{u} ε C1 ∧
        C2h ≤ strongC2_C11SC.{u} ε C2 Cgrad ∧ qs ≤ qh ∧
        ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
          (pV : CutoffParameters)
          (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
          V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          RecordHypFar_C12X (5 / 4) V records →
          V.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last V.eventCount) ∧
          ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
            V.StronglyCanonicalBeforeFull_C12X (Fin.last V.eventCount)
              ((V.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1h C2h qh
              V.horizon) ∧
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
  exact @exists_prepared_class_native_order_C12P.{u}
    Dstar εReserve mmod hDstar hεReserve (fun K => ∀ i : Fin K.eventCount,
      (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter
    prepareClass.toNative ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε hstr analytic P g

end GC.GeneralFlow
