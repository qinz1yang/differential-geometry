import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingPinching

/-!
# L6-B 叶子窗口版：`TerminalPinching:19/45` 与 `HistorySurvivorIncomingPinching:68/113`（`_P6WA`）

P6WIN 接口约定：pinching 前提取窗口集 `Ico … ∩ Ici c`（`c` = 窗口起点），结论逐字。
* `TPin:19/45`：terminal limit 处用 `Ioo_mem_nhdsLT hcs` 取 `u → s⁻` 且 `c ≤ u`，故加 `hcs : c < s`；
* `HSIP:68`：`ht : t ∈ Icc c s`（原 `Icc (time first) s`），加 `hc : time first ≤ c`、`hcs : c < s`；
  old-stage 分支改用严格的 `activeStage_before_next`（`t ∈ Ico`），于是 `hpinch` 只在 `t ≥ c` 求值；
* `HSIP:113`：`hstart : time first ≤ s - θ / Q` 改 `hc : time first ≤ c`、`hstart : c ≤ s - θ / Q`、
  `hcs : c < s`。
consumer：`c = time first` 时的原形（全段 pinching `Ico` 经 `Ico ∩ Ici c ⊆ Ico`）推出，见文末 `example`。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s c : ℝ} {G : P.IncomingSlab a s}

namespace TerminalLimitMetric

/-- `TPin:19` 窗口版：pinching 取 `Ico a s ∩ Ici c`，加 `hcs : c < s`。 -/
theorem curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative_window_P6WA
    (L : G.TerminalLimitMetric) {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (hcs : c < s)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s ∩ Ici c) Phi)
    (x : G.terminalRegularOpen) :
    curvatureOperatorLowerBoundAt L.metric x (metricAlgebraicCurvatureTensorAt L.metric x)
      (Phi (metricScalarAt L.metric x)) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt L.metric x (by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace])
  apply (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
    basis horth).mpr
  apply le_of_tendsto_of_tendsto
    ((L.tendsto_leastCurvatureOperatorEigenvalueAt x).neg)
    ((hPhi.tendsto _).comp (L.tendsto_metricScalarAt x))
  have hp := (Perelman.phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    G.flow (Ico a s ∩ Ici c) Phi (by simp [ThreeSpace])).mp hpinch
  filter_upwards [Ioo_mem_nhdsLT G.lt, Ioo_mem_nhdsLT hcs] with t ht hct
  have htP := hp t ⟨⟨ht.1.le, ht.2⟩, hct.1.le⟩ x.val
  change -Phi (metricScalarAt (G.flow.base.metric t) x.val) ≤
    leastCurvatureOperatorEigenvalueAt (G.flow.base.metric t) x.val
      (metricAlgebraicCurvatureTensorAt (G.flow.base.metric t) x.val) at htP
  change -leastCurvatureOperatorEigenvalueAt (G.flow.base.metric t) x.val
    (metricAlgebraicCurvatureTensorAt (G.flow.base.metric t) x.val) ≤
      Phi (metricScalarAt (G.flow.base.metric t) x.val)
  linarith

/-- `TPin:45` 窗口版：`t ∈ Icc a s`、`c ≤ t`，pinching 取 `Ico a s ∩ Ici c`。 -/
theorem extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative_window_P6WA
    (L : G.TerminalLimitMetric) {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (hcs : c < s)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s ∩ Ici c) Phi)
    {t : ℝ} (ht : t ∈ Icc a s) (hct : c ≤ t) (x : G.terminalRegularOpen) :
    curvatureOperatorLowerBoundAt (L.extendedMetric t) x
      (metricAlgebraicCurvatureTensorAt (L.extendedMetric t) x)
      (Phi (metricScalarAt (L.extendedMetric t) x)) := by
  rcases lt_or_eq_of_le ht.2 with hts | rfl
  · rw [L.extendedMetric_before hts, ← DifferentialGeometry.localPullMetric_subtype_val,
      metricScalarAt_localPull, curvatureOperatorLowerBoundAt_localPullMetric_iff]
    exact hpinch t ⟨⟨ht.1, hts⟩, hct⟩ x.val
  · rw [L.extendedMetric_terminal]
    exact L.curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative_window_P6WA hPhi hcs hpinch x

end TerminalLimitMetric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

private theorem pinching_localPullMetric_window_P6WA
    {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric ThreeModel N) (f : M → N)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (Phi : ℝ → ℝ)
    (hpinch : ∀ x : N, curvatureOperatorLowerBoundAt g x
      (metricAlgebraicCurvatureTensorAt g x) (Phi (metricScalarAt g x))) :
    ∀ x : M, curvatureOperatorLowerBoundAt (localPullMetric g f hf) x
      (metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x)
      (Phi (metricScalarAt (localPullMetric g f hf) x)) := by
  intro x
  rw [metricScalarAt_localPull, curvatureOperatorLowerBoundAt_localPullMetric_iff]
  exact hpinch (f x)

private theorem pinching_restrictOpen_window_P6WA
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : TopologicalSpace.Opens M)
    (Phi : ℝ → ℝ)
    (hpinch : ∀ x : M, curvatureOperatorLowerBoundAt g x
      (metricAlgebraicCurvatureTensorAt g x) (Phi (metricScalarAt g x))) :
    ∀ x : U, curvatureOperatorLowerBoundAt (g.restrictOpen U) x
      (metricAlgebraicCurvatureTensorAt (g.restrictOpen U) x)
      (Phi (metricScalarAt (g.restrictOpen U) x)) := by
  rw [← DifferentialGeometry.localPullMetric_subtype_val]
  exact pinching_localPullMetric_window_P6WA g Subtype.val _ Phi hpinch

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s c : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  (K : Set G.terminalRegularOpen)
  (gflow : ℝ → SmoothRiemannianMetric ThreeModel
    (H.backwardSurvivorIncomingFootprint first last hle G K))
  (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
    ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K))
  (hlast : ∀ t ∈ Icc (H.time last) s,
    gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
      (H.backwardSurvivorIncomingFootprint first last hle G K))
  {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
  (hc : H.time first ≤ c) (hcs : c < s)
  (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
    Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici c) Phi)
  (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s ∩ Ici c) Phi)

include hslabs hlast hPhi hc hcs hpinch hpinchFinal in
/-- `HSIP:68` 窗口版。 -/
theorem curvatureOperatorLowerBoundAt_backwardSurvivorIncomingFootprint_window_P6WA
    {t : ℝ} (ht : t ∈ Icc c s) :
    ∀ x : H.backwardSurvivorIncomingFootprint first last hle G K,
      curvatureOperatorLowerBoundAt (gflow t) x (metricAlgebraicCurvatureTensorAt (gflow t) x)
        (Phi (metricScalarAt (gflow t) x)) := by
  by_cases hlasttime : H.time last ≤ t
  · rw [hlast t ⟨hlasttime, ht.2⟩]
    apply pinching_restrictOpen_window_P6WA
    unfold backwardSurvivorIncomingMetric
    apply pinching_localPullMetric_window_P6WA
    exact L.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative_window_P6WA
      hPhi hcs hpinchFinal ⟨hlasttime, ht.2⟩ ht.1
  · have hti : t < H.time last := lt_of_not_ge hlasttime
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans (hc.trans ht.1), hti.le.trans (H.time_le_horizon_at last)⟩
    let k := H.activeStage tH
    have hk : k < last := by
      apply H.time_strictMono.lt_iff_lt.mp
      exact (H.activeStage_time_le tH).trans_lt hti
    have hkfirst : first ≤ k := H.le_activeStage tH first (hc.trans ht.1)
    let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
    have hf : first ≤ j.castSucc := hkfirst
    have hl : j.succ ≤ last := hk
    have htj : t ∈ Ico (H.time j.castSucc) (H.time j.succ) :=
      ⟨H.activeStage_time_le tH,
        H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)⟩
    rw [hslabs j hf hl t (Ico_subset_Icc_self htj)]
    apply pinching_restrictOpen_window_P6WA
    apply pinching_restrictOpen_window_P6WA
    unfold backwardSurvivorSlabMetric
    apply pinching_localPullMetric_window_P6WA
    let Lj := (H.event j).terminal
    exact Lj.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative_window_P6WA
      hPhi (ht.1.trans_lt htj.2) (hpinch j hf hl) (Ico_subset_Icc_self htj) ht.1

private local instance :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let _ : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let _ : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

include hslabs hlast hPhi hc hcs hpinch hpinchFinal in
/-- `HSIP:113` 窗口版。 -/
theorem phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback_window_P6WA
    {E J M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace J] {I : ModelWithCorners ℝ E J} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace J M] [IsManifold I ∞ M] [T2Space M]
    {Q θ : ℝ} (hQ : 0 < Q) (hstart : c ≤ s - θ / Q)
    (f : M → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hf : IsLocalDiffeomorph I ThreeModel ∞ f)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hmetric : ∀ v ∈ Icc (-θ) 0,
      S.base.metric v = localPullMetric (scaleMetric Q hQ (gflow (s + v / Q))) f hf) :
    Perelman.PhiAlmostNonnegative S (Icc (-θ) 0) (Perelman.rescalePinchingFunction Q Phi) := by
  let U : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D :=
    { base.metric := fun v => scaleMetric Q hQ (gflow (s + v / Q)) }
  have hU : Perelman.PhiAlmostNonnegative U (Icc (-θ) 0)
      (Perelman.rescalePinchingFunction Q Phi) := by
    intro v hv x
    have hlo : -(θ / Q) ≤ v / Q := by
      simpa only [neg_div] using div_le_div_of_nonneg_right hv.1 hQ.le
    have hhi : v / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.2 hQ.le
    have ht : s + v / Q ∈ Icc c s := by constructor <;> linarith
    have hp := H.curvatureOperatorLowerBoundAt_backwardSurvivorIncomingFootprint_window_P6WA
      first last hle G L K gflow hslabs hlast hPhi hc hcs hpinch hpinchFinal ht x
    change curvatureOperatorLowerBoundAt (scaleMetric Q hQ (gflow (s + v / Q))) x
      (metricAlgebraicCurvatureTensorAt (scaleMetric Q hQ (gflow (s + v / Q))) x)
      (Perelman.rescalePinchingFunction Q Phi
        (metricScalarAt (scaleMetric Q hQ (gflow (s + v / Q))) x))
    rw [curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      Perelman.rescalePinchingFunction]
    simpa only [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] using hp
  have hp := hU.localPullback f hf
  intro v hv x
  change curvatureOperatorLowerBoundAt (S.base.metric v) x
    (metricAlgebraicCurvatureTensorAt (S.base.metric v) x)
    (Perelman.rescalePinchingFunction Q Phi (metricScalarAt (S.base.metric v) x))
  rw [hmetric v hv]
  exact hp v hv x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u in
/-- consumer：原 `HSIP:68`（`ht : t ∈ Icc (time first) s`、pinching 取 `Ico`）
由窗口版（`c = time first`）推出。 -/
example : type_of%
    @ObservedHistory.curvatureOperatorLowerBoundAt_backwardSurvivorIncomingFootprint.{u} := by
  intro H first last hle s G L K gflow hslabs hlast Phi hPhi hpinch hpinchFinal t ht
  exact H.curvatureOperatorLowerBoundAt_backwardSurvivorIncomingFootprint_window_P6WA
    first last hle G L K gflow hslabs hlast hPhi le_rfl
    ((H.time_strictMono.monotone hle).trans_lt G.lt)
    (fun j hf hl t ht x => hpinch j hf hl t ht.1 x) (fun t ht x => hpinchFinal t ht.1 x) ht

universe u in
open ObservedHistory in
/-- consumer：原 `HSIP:113`。 -/
example : type_of%
    @phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback.{u} := by
  intro H first last hle s G L K gflow hslabs hlast Phi hPhi hpinch hpinchFinal E J M _ _ _ _ I
    _ _ _ _ _ Q θ hQ hstart f hf D S hmetric
  exact
    H.phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback_window_P6WA
      first last hle G L K gflow hslabs hlast hPhi le_rfl
      ((H.time_strictMono.monotone hle).trans_lt G.lt)
      (fun j hf hl t ht x => hpinch j hf hl t ht.1 x) (fun t ht x => hpinchFinal t ht.1 x)
      hQ hstart f hf S hmetric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
