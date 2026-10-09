import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v z uSmoothJoin uPositiveStages uStageSmooth

private theorem exists_directed_local_joins_of_pullback_germ
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {Y : Type z} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    [IsManifold ThreeModel ∞ Y] [T2Space Y]
    {DX DY : RealTimeInterval}
    (A : SolutionOn (I := ThreeModel) (M := X) DX)
    (B : SolutionOn (I := ThreeModel) (M := Y) DY)
    (f : X → Y) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (T r : ℝ) (alpha : ℝ → X) (beta : ℝ → Y)
    (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel alpha r)
    (hcurve : f ∘ alpha =ᶠ[𝓝 r] beta)
    (hmetric : A.base.metric (T - r ^ 2) =
      localPullMetric (B.base.metric (T - r ^ 2)) f hf) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel X Y ∞,
      EqOn f F F.source ∧ alpha r ∈ F.source ∧ beta r ∈ F.symm.source ∧
      F (alpha r) = beta r ∧ F.symm (beta r) = alpha r ∧
      F ∘ alpha =ᶠ[𝓝 r] beta ∧ F.symm ∘ beta =ᶠ[𝓝 r] alpha ∧
      (∀ x ∈ F.source, ∀ V W : TangentSpace ThreeModel x,
        (A.base.metric (T - r ^ 2)).inner x V W =
          (B.base.metric (T - r ^ 2)).inner (F x)
            (mfderiv ThreeModel ThreeModel (F : X → Y) x V)
            (mfderiv ThreeModel ThreeModel (F : X → Y) x W)) ∧
      (∀ y ∈ F.symm.source, ∀ V W : TangentSpace ThreeModel y,
        (B.base.metric (T - r ^ 2)).inner y V W =
          (A.base.metric (T - r ^ 2)).inner (F.symm y)
            (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y V)
            (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y W)) ∧
      (mfderiv ThreeModel ThreeModel (F : X → Y) (alpha r)
        (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) = lVelocity (I := ThreeModel) beta r ∧
      (mfderiv ThreeModel ThreeModel (F.symm : Y → X) (beta r)
        (lVelocity (I := ThreeModel) beta r) : ThreeSpace) = lVelocity (I := ThreeModel) alpha r ∧
      A.scalar (T - r ^ 2) (alpha r) = B.scalar (T - r ^ 2) (beta r) ∧
      lRegularizedLagrangian A T alpha r = lRegularizedLagrangian B T beta r := by
  obtain ⟨F, hsource, hEq⟩ := hf (alpha r)
  have hstay : ∀ᶠ t in 𝓝 r, alpha t ∈ F.source :=
    halpha.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hsource)
  have hcenter : F ∘ alpha =ᶠ[𝓝 r] beta := by
    filter_upwards [hstay, hcurve] with t ht hct
    exact (hEq ht).symm.trans hct
  have hpoint : F (alpha r) = beta r := hcenter.self_of_nhds
  have htarget : beta r ∈ F.symm.source := hpoint ▸ F.map_source hsource
  have hpointInv : F.symm (beta r) = alpha r := by
    rw [← hpoint]
    exact F.left_inv hsource
  have hcenterInv : F.symm ∘ beta =ᶠ[𝓝 r] alpha := by
    filter_upwards [hstay, hcenter] with t ht hct
    change F.symm (beta t) = alpha t
    rw [← hct]
    exact F.left_inv ht
  have hderiv (x : X) (hx : x ∈ F.source) :
      (mfderiv ThreeModel ThreeModel f x : ThreeSpace →L[ℝ] ThreeSpace) =
        mfderiv ThreeModel ThreeModel (F : X → Y) x := by
    exact (Filter.eventuallyEq_of_mem (F.open_source.mem_nhds hx) hEq).mfderiv_eq
  have hforward (x : X) (hx : x ∈ F.source) (V W : TangentSpace ThreeModel x) :
      (A.base.metric (T - r ^ 2)).inner x V W =
        (B.base.metric (T - r ^ 2)).inner (F x)
          (mfderiv ThreeModel ThreeModel (F : X → Y) x V)
          (mfderiv ThreeModel ThreeModel (F : X → Y) x W) := by
    rw [hmetric, localPullMetric_inner, hderiv x hx]
    exact congrArg (fun y : Y => (B.base.metric (T - r ^ 2)).inner y
      (mfderiv ThreeModel ThreeModel (F : X → Y) x V)
      (mfderiv ThreeModel ThreeModel (F : X → Y) x W)) (hEq hx)
  have hinverse (y : Y) (hy : y ∈ F.symm.source) (V W : TangentSpace ThreeModel y) :
      (B.base.metric (T - r ^ 2)).inner y V W =
        (A.base.metric (T - r ^ 2)).inner (F.symm y)
          (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y V)
          (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y W) := by
    have hright : (F : X → Y) ∘ (F.symm : Y → X) =ᶠ[𝓝 y] id := by
      filter_upwards [F.symm.open_source.mem_nhds hy] with z hz
      exact F.right_inv hz
    have hcomp (Z : TangentSpace ThreeModel y) :
        mfderiv ThreeModel ThreeModel (F : X → Y) (F.symm y)
          (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y Z) = Z := by
      have hh := mfderiv_comp_apply y
        (F.mdifferentiableAt (by simp) (F.symm.map_source hy))
        (F.symm.mdifferentiableAt (by simp) hy) Z
      rw [hright.mfderiv_eq, mfderiv_id] at hh
      exact hh.symm
    have hm := hforward (F.symm y) (F.symm.map_source hy)
      (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y V)
      (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y W)
    rw [hcomp, hcomp] at hm
    exact (congrArg (fun z : Y => (B.base.metric (T - r ^ 2)).inner z V W)
      (F.right_inv hy)).symm.trans hm.symm
  have hvel : (mfderiv ThreeModel ThreeModel (F : X → Y) (alpha r)
      (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) = lVelocity (I := ThreeModel) beta r := by
    let one : TangentSpace 𝓘(ℝ, ℝ) r :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) r).symm (1 : ℝ)
    have hcomp := mfderiv_comp_apply r (F.mdifferentiableAt (by simp) hsource) halpha one
    have hmf := hcenter.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    have hm := congrArg
      (fun D : TangentSpace 𝓘(ℝ, ℝ) r →L[ℝ] TangentSpace ThreeModel ((F ∘ alpha) r) =>
        DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv
          (I := ThreeModel) ((F ∘ alpha) r) (D one)) hmf
    dsimp only [Function.comp_apply] at hm
    rw [hpoint] at hm
    have hvelEq : (lVelocity (I := ThreeModel) (F ∘ alpha) r : ThreeSpace) =
        lVelocity (I := ThreeModel) beta r := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        tangentSpaceCast] using! hm
    exact (show (mfderiv ThreeModel ThreeModel (F : X → Y) (alpha r)
      (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) =
        lVelocity (I := ThreeModel) (F ∘ alpha) r from by
      simpa only [lVelocity] using! hcomp.symm).trans hvelEq
  have hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel beta r :=
    ((F.mdifferentiableAt (by simp) hsource).comp r halpha).congr_of_eventuallyEq hcenter.symm
  have hvelInv : (mfderiv ThreeModel ThreeModel (F.symm : Y → X) (beta r)
      (lVelocity (I := ThreeModel) beta r) : ThreeSpace) = lVelocity (I := ThreeModel) alpha r := by
    let one : TangentSpace 𝓘(ℝ, ℝ) r :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) r).symm (1 : ℝ)
    have hcomp := mfderiv_comp_apply r (F.symm.mdifferentiableAt (by simp) htarget) hbeta one
    have hmf := hcenterInv.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    have hm := congrArg
      (fun D : TangentSpace 𝓘(ℝ, ℝ) r →L[ℝ] TangentSpace ThreeModel ((F.symm ∘ beta) r) =>
        DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv
          (I := ThreeModel) ((F.symm ∘ beta) r) (D one)) hmf
    dsimp only [Function.comp_apply] at hm
    rw [hpointInv] at hm
    have hvelEq : (lVelocity (I := ThreeModel) (F.symm ∘ beta) r : ThreeSpace) =
        lVelocity (I := ThreeModel) alpha r := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        tangentSpaceCast] using! hm
    exact (show (mfderiv ThreeModel ThreeModel (F.symm : Y → X) (beta r)
      (lVelocity (I := ThreeModel) beta r) : ThreeSpace) =
        lVelocity (I := ThreeModel) (F.symm ∘ beta) r from by
      simpa only [lVelocity] using! hcomp.symm).trans hvelEq
  have hscalar : A.scalar (T - r ^ 2) (alpha r) = B.scalar (T - r ^ 2) (beta r) := by
    change metricScalarAt (A.base.metric (T - r ^ 2)) (alpha r) =
      metricScalarAt (B.base.metric (T - r ^ 2)) (beta r)
    rw [hmetric, metricScalarAt_localPull]
    exact congrArg (metricScalarAt (B.base.metric (T - r ^ 2))) hcurve.self_of_nhds
  have hLag : lRegularizedLagrangian A T alpha r = lRegularizedLagrangian B T beta r := by
    calc
      lRegularizedLagrangian A T alpha r =
          lRegularizedLagrangian (B.localPullback f hf) T alpha r := by
        simp only [lRegularizedLagrangian, SolutionOn.scalar, SolutionFamily.scalar,
          SolutionOn.localPullback_metric, hmetric]
      _ = lRegularizedLagrangian B T (f ∘ alpha) r :=
        lRegularizedLagrangian_localPullback B f hf T halpha
      _ = lRegularizedLagrangian B T beta r := by
        simp only [lRegularizedLagrangian, lVelocity, hcurve.mfderiv_eq, hcurve.self_of_nhds]
        exact congrArg (fun y : Y =>
          (1 / 2 : ℝ) * (B.base.metric (T - r ^ 2)).inner y
            (lVelocity (I := ThreeModel) beta r) (lVelocity (I := ThreeModel) beta r) +
          2 * r ^ 2 * B.scalar (T - r ^ 2) (beta r)) hcurve.self_of_nhds
  exact ⟨F, hEq, hsource, htarget, hpoint, hpointInv, hcenter, hcenterInv,
    hforward, hinverse, hvel, hvelInv, hscalar, hLag⟩

private theorem survivor_pullback_at_strict_join_clocks
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {DS : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) DS)
    (oldMap : X → (H.stage i.castSucc).Carrier)
    (newMap : X → (H.stage i.succ).Carrier)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ oldMap)
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ newMap)
    (C D T c w d : ℝ) (hc : 0 ≤ c) (hcw : c < w) (hwd : w < d)
    (hwclock : T - w ^ 2 = H.time i.succ)
    (hcclock : T - c ^ 2 ∈ Ioo C D) (hdclock : T - d ^ 2 ∈ Ioo C D)
    (hOld : ∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) oldMap hold)
    (hNew : ∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) newMap hnew) :
    T - c ^ 2 ∈ Ioo (H.time i.succ) D ∧
      T - d ^ 2 ∈ Ioo C (H.time i.succ) ∧
      S.base.metric (T - c ^ 2) =
        localPullMetric (H.stageMetric i.succ (T - c ^ 2)) newMap hnew ∧
      S.base.metric (T - d ^ 2) =
        localPullMetric (H.stageMetric i.castSucc (T - d ^ 2)) oldMap hold := by
  have hw : 0 ≤ w := hc.trans hcw.le
  have hdc : H.time i.succ < T - c ^ 2 := by
    have hs := (sq_lt_sq₀ hc hw).mpr hcw
    linarith only [hs, hwclock]
  have hdd : T - d ^ 2 < H.time i.succ := by
    have hs := (sq_lt_sq₀ hw (hw.trans hwd.le)).mpr hwd
    linarith only [hs, hwclock]
  exact ⟨⟨hdc, hcclock.2⟩, ⟨hdclock.1, hdd⟩,
    hNew _ ⟨hdc.le, hcclock.2.le⟩, hOld _ ⟨hdclock.1.le, hdd⟩⟩

theorem exists_smooth_survivor_directed_joins
    (H : ObservedHistory.{uSmoothJoin}) (i : Fin H.eventCount)
    {C D T c d : ℝ} (hiT : H.time i.succ ≤ T) (hc : 0 ≤ c)
    (hcw : c < Real.sqrt (T - H.time i.succ))
    (hwd : Real.sqrt (T - H.time i.succ) < d)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (FC : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    {DS DN DO : RealTimeInterval}
    (SS : SolutionOn (I := ThreeModel) (M := W) DS)
    (SN : SolutionOn (I := ThreeModel) (M := (H.stage i.succ).Carrier) DN)
    (SO : SolutionOn (I := ThreeModel) (M := (H.stage i.castSucc).Carrier) DO)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => FC z.val))
    (hMN : ∀ t, SN.base.metric t = H.stageMetric i.succ t)
    (hMO : ∀ t, SO.base.metric t = H.stageMetric i.castSucc t)
    (hOld : ∀ t ∈ Ico C (H.time i.succ), SS.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hold)
    (hNew : ∀ t ∈ Icc (H.time i.succ) D, SS.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => FC z.val) hnew)
    (hclockc : T - c ^ 2 ∈ Ioo C D) (hclockd : T - d ^ 2 ∈ Ioo C D)
    (eta : ℝ → W) (alphaN gammaN : ℝ → (H.stage i.succ).Carrier)
    (alphaO gammaO : ℝ → (H.stage i.castSucc).Carrier)
    (hmdc : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel eta c)
    (hmdd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel eta d)
    (hGermN : ((fun z : W => FC z.val) ∘ eta) =ᶠ[𝓝 c] gammaN)
    (hGermO : ((fun z : W => z.val.val) ∘ eta) =ᶠ[𝓝 d] gammaO)
    (hOrdN : alphaN =ᶠ[𝓝 c] gammaN) (hOrdO : alphaO =ᶠ[𝓝 d] gammaO) :
    ∃ (Fn : PartialDiffeomorph ThreeModel ThreeModel W (H.stage i.succ).Carrier ∞)
      (Fo : PartialDiffeomorph ThreeModel ThreeModel W (H.stage i.castSucc).Carrier ∞),
      EqOn (fun z : W => FC z.val) Fn Fn.source ∧
      EqOn (fun z : W => z.val.val) Fo Fo.source ∧
      (alphaN c ∈ Fn.symm.source ∧
        (Fn.symm : _ → _) ∘ alphaN =ᶠ[𝓝 c] eta ∧
        (∀ y ∈ Fn.symm.source, ∀ V W : TangentSpace ThreeModel y,
          (SN.base.metric (T - c ^ 2)).inner y V W =
            (SS.base.metric (T - c ^ 2)).inner (Fn.symm y)
              (mfderiv ThreeModel ThreeModel (Fn.symm : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (Fn.symm : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (Fn.symm : _ → _) (alphaN c)
          (lVelocity (I := ThreeModel) alphaN c) : ThreeSpace) =
            lVelocity (I := ThreeModel) eta c ∧
        SN.scalar (T - c ^ 2) (alphaN c) = SS.scalar (T - c ^ 2) (eta c) ∧
        lRegularizedLagrangian SN T alphaN c = lRegularizedLagrangian SS T eta c) ∧
      (eta d ∈ Fo.source ∧
        (Fo : _ → _) ∘ eta =ᶠ[𝓝 d] alphaO ∧
        (∀ y ∈ Fo.source, ∀ V W : TangentSpace ThreeModel y,
          (SS.base.metric (T - d ^ 2)).inner y V W =
            (SO.base.metric (T - d ^ 2)).inner (Fo y)
              (mfderiv ThreeModel ThreeModel (Fo : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (Fo : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (Fo : _ → _) (eta d)
          (lVelocity (I := ThreeModel) eta d) : ThreeSpace) =
            lVelocity (I := ThreeModel) alphaO d ∧
        SS.scalar (T - d ^ 2) (eta d) = SO.scalar (T - d ^ 2) (alphaO d) ∧
        lRegularizedLagrangian SS T eta d = lRegularizedLagrangian SO T alphaO d) := by
  have hwclock : T - (Real.sqrt (T - H.time i.succ)) ^ 2 = H.time i.succ := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hiT)]
    ring
  have hclocks := H.survivor_pullback_at_strict_join_clocks i SS
    (fun z : W => z.val.val) (fun z : W => FC z.val) hold hnew
    C D T c (Real.sqrt (T - H.time i.succ)) d hc hcw hwd hwclock hclockc hclockd hOld hNew
  have hmN : SS.base.metric (T - c ^ 2) =
      localPullMetric (SN.base.metric (T - c ^ 2)) (fun z : W => FC z.val) hnew := by
    rw [hMN]
    exact hclocks.2.2.1
  have hmO : SS.base.metric (T - d ^ 2) =
      localPullMetric (SO.base.metric (T - d ^ 2)) (fun z : W => z.val.val) hold := by
    rw [hMO]
    exact hclocks.2.2.2
  obtain ⟨Fn, hEqN, _, hTarget, _, _, _, hInv, _, hInvMetric, _, hInvVel, hScalarN, hLagN⟩ :=
    exists_directed_local_joins_of_pullback_germ SS SN (fun z : W => FC z.val) hnew T c
      eta alphaN hmdc (hGermN.trans hOrdN.symm) hmN
  obtain ⟨Fo, hEqO, hSource, _, _, _, hForward, _, hMetric, _, hVel, _, hScalarO, hLagO⟩ :=
    exists_directed_local_joins_of_pullback_germ SS SO (fun z : W => z.val.val) hold T d
      eta alphaO hmdd (hGermO.trans hOrdO.symm) hmO
  exact ⟨Fn, Fo, hEqN, hEqO,
    ⟨hTarget, hInv, hInvMetric, hInvVel, hScalarN.symm, hLagN.symm⟩,
    ⟨hSource, hForward, hMetric, hVel, hScalarO, hLagO⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
