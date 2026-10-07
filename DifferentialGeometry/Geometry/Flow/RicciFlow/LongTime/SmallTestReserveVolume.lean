import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformReserveBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WholeCanonicalComponentSeedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StageBallVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume

/-!
# S-CH11-FIX9 patched-at-path of astra `SmallTestReserveVolume`

来源：donor `SmallTestReserveVolume.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（6 error）。本文件只有 elaboration 层面修补（no statement /
definition / proof idea altered；不加 `set_option`）：
* `hzero`：`simpa only [hz] using L.prepared.zero_bound …`（`hz : activeStage t = 0` 要改写依赖类型的
  index `(K.stage (activeStage t)).Carrier`，simp 进不了）→ 对 index 做一般引理
  `∀ j, j = 0 → …`，`subst` 后 `exact`；
* `hsource`：`simpa only [hmetric t] using hSpatial …` 同类（metric 出现在 `SpatialCanonicalWitness` 的
  类型里）→ 先 `rw [← hmetric t]`（motive 型良）再 `exact`；
* 2 处 `X.terminal_curvature_bound z hz`：本树 `isParabolicallyRmControlledBall.
  terminal_curvature_bound` 的 `H` 是显式参数（树内其它调用都写 `h.terminal_curvature_bound H x hx`）
  → 补 `H`；
* `round` 情形：`cases hAlt : V.alternative` 已经把目标里的 `V.alternative` 换掉，
  `rw [hAlt]` 找不到模式 → 直接 `trivial`；
* 主定理陈述里 16 个只在 `intro` 里引用的 binder 名（`hTower hshift hoffset hshift_nonneg
  hmodelRadius hmodelAccuracy hmodelOrder hclassScale hfit hclock htop hback hseed hseedVolume hx
  hreserve`）→ 加 `_` 前缀（unusedVariables；binder 名不改变陈述）。

下游 `SmallTestLargeReserveVolume` 有 `open private seed_scalar_le_three_div_sq from` 本路径，
故直接在原路径修补（不另建 PortC11P / shim）。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u

open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq
  overlap_spatialWitness_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

/-- Extract the spatial witness from the same prepared class at its own threshold,
including the actual birth metric and its original marked time-zero exclusion. -/
private theorem PreparedSpatialStepRetention.exists_spatialWitness_at_own_threshold
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (t : Icc (0 : ℝ) W.oldNative.horizon)
    (htop : (t : ℝ) < W.oldNative.horizon)
    (y : (W.oldNative.toHistory.stageAt t).Carrier)
    (hR : L.prepared.Qall < metricScalarAt
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage t) t) y) :
    ∃ V : SpatialCanonicalWitness
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage t) t)
      C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) y,
      V.capTubeHasNeckChart C.epsilon := by
  let K := W.oldNative
  obtain ⟨_hnc, hEst, hBirth⟩ := L.prepared.control K W.oldNativeInitial
    W.oldNativeParameters W.oldNativeRecords W.oldNative_horizon.le W.oldNative_class
  have hBirthAll : L.prepared.Qbirth ≤ L.prepared.Qall := by
    rw [L.prepared.Qall_eq]
    exact le_max_left _ _
  have hZeroAll : L.prepared.Qzero ≤ L.prepared.Qall := by
    rw [L.prepared.Qall_eq]
    exact le_max_right _ _
  have hqsBirth : L.prepared.qs ≤ L.prepared.Qbirth :=
    (le_max_right L.prepared.qcan L.prepared.qs).trans
      ((le_max_right 1 (max L.prepared.qcan L.prepared.qs)).trans L.prepared.Qbirth_ge)
  by_cases hbirth : K.time (K.toHistory.activeStage t) = (t : ℝ)
  · have hmetricBirth : K.toHistory.stageMetric (K.toHistory.activeStage t) t =
        K.initialMetric (K.toHistory.activeStage t) := by
      rw [← hbirth]
      exact K.toHistory.stageMetric_initial _
    have hxBirth : L.prepared.Qall <
        metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y := by
      rw [← hmetricBirth]
      exact hR
    by_cases hz : K.toHistory.activeStage t = 0
    · have hzero : ∀ z : (K.stage (K.toHistory.activeStage t)).Carrier,
          metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) z < L.prepared.Qzero := by
        have key : ∀ j : Fin (K.eventCount + 1), j = 0 →
            ∀ z : (K.stage j).Carrier,
              metricScalarAt (K.initialMetric j) z < L.prepared.Qzero := by
          intro j hj
          subst hj
          exact L.prepared.zero_bound K.toHistory W.oldNativeInitial
        exact key _ hz
      exact (not_lt_of_ge (hZeroAll.trans_lt hxBirth).le (hzero y)).elim
    · obtain ⟨V, hV⟩ := hBirth t htop hbirth hz y (hBirthAll.trans_lt hxBirth)
      rw [hmetricBirth]
      exact ⟨V.enlargeConstants (le_max_right _ _) (le_max_right _ _),
        hV.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩
  · have hstrict : K.time (K.toHistory.activeStage t) < (t : ℝ) :=
      lt_of_le_of_ne (K.toHistory.activeStage_time_le t) hbirth
    obtain ⟨s, G, hts, _hsK, _hinit, hmetric, _hD, _hG, _hCan, hSpatial⟩ :=
      hEst.exists_outgoingSlab_of_lt_horizon t htop
    have hhigh : L.prepared.qs < G.flow.scalar t y := by
      change L.prepared.qs < metricScalarAt (G.flow.base.metric t) y
      rw [hmetric t]
      exact hqsBirth.trans_lt (hBirthAll.trans_lt hR)
    have hsource : ∃ V : SpatialCanonicalWitness
        (K.toHistory.stageMetric (K.toHistory.activeStage t) t) C.epsilon C.C1s C.C2s y,
        V.capTubeHasNeckChart C.epsilon := by
      rw [← hmetric t]
      exact hSpatial y t ⟨hstrict, hts⟩ hhigh
    obtain ⟨V, hV⟩ := hsource
    exact ⟨V.enlargeConstants (le_max_left _ _) (le_max_left _ _),
      hV.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩

/-- The stronger normalization in the actual analytic seed gives the coefficient
three at its original endpoint and original metric. -/
private theorem seed_scalar_le_three_div_sq
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {r : ℝ}
    (hseed : GC.LongTime.hasSmallParabolicCurvature H t p r) :
    metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ 3 / r ^ 2 := by
  obtain ⟨hr, a, hat, _ha, htrace⟩ := hseed
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨A, hA⟩ := htrace p hp
  have hbound := hA.1 t hat le_rfl
  have he : A.point (H.activeStage t) (H.activeStage_mono hat)
      (H.activeStage_mono le_rfl) = p := A.endpoint_eq
  rw [he] at hbound
  let N := normSq0S (H.stageMetric (H.activeStage t) t) p 4
    (metricRm04At (H.stageMetric (H.activeStage t) t) p)
  have hN : 0 ≤ N := normSq0S_nonneg _ _ _ _
  change (Real.sqrt 3 * r) ^ 4 * N ≤ 1 at hbound
  have hfour : (Real.sqrt (3 : ℝ) * r) ^ 4 = 9 * r ^ 4 := by
    calc
      (Real.sqrt (3 : ℝ) * r) ^ 4 = (Real.sqrt (3 : ℝ) ^ 2) ^ 2 * r ^ 4 := by ring
      _ = 9 * r ^ 4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  rw [hfour] at hbound
  have hsquare : (3 * r ^ 2 * Real.sqrt N) ^ 2 ≤ 1 := by
    calc
      (3 * r ^ 2 * Real.sqrt N) ^ 2 = 9 * r ^ 4 * N := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hN]
        ring
      _ ≤ 1 := hbound
  have hnorm : 3 * r ^ 2 * Real.sqrt N ≤ 1 := by
    have hnonneg : 0 ≤ 3 * r ^ 2 * Real.sqrt N := by positivity
    nlinarith only [hsquare, hnonneg]
  have hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ 9 * Real.sqrt N := by
    have h := (le_abs_self (metricScalarAt (H.stageMetric (H.activeStage t) t) p)).trans
      (scalar_abs_le_rm (H.stageMetric (H.activeStage t) t) p)
    change metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt N at h
    norm_num [ThreeSpace] at h
    exact h
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  have hmul := mul_le_mul_of_nonneg_right hscalar (sq_nonneg r)
  nlinarith only [hmul, hnorm]

/-- An existing small test in the original observation either has uniform volume
or enlarges to the pre-fine reserve on that same flow and at that same point. -/
theorem exists_test_volume_or_reserve_in_same_observation_of_retained_class_quality
    (Dstar : ℝ) (hDstar : StandardCap.transitionEnd < Dstar) :
    ∃ εcap cBG : ℝ, 0 < εcap ∧ 0 < cBG ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (C : ClosedBirthConstants),
    ∃ cMax : ℝ, 0 < cMax ∧
    ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
    ∀ {pBase : CutoffParameters}
      (S : PreparedSpatialChain pBase C P g)
      (F : GC.Interface.RawSurgery P g) (_hTower : F.tower = S.tower)
      (j : ℕ) {εcut Dcut : ℝ} {mcut : ℕ}
      (W : PreparedSpatialStepRetention (S.state j) (S.state (j + 1))
        (S.accuracy j) (1 / ((j : ℝ) + 2)) εcut Dcut mcut)
      (_hshift : (S.state (j + 1)).shift =
        (S.state j).history.time (Fin.last (S.state j).history.eventCount))
      (_hoffset : (S.state (j + 1)).offset = (S.state j).history.eventCount)
      (_hshift_nonneg : 0 ≤ (S.state j).shift)
      (_hmodelRadius : Dstar ≤ (S.state j).prepared.parameters.modelRadius)
      (_hmodelAccuracy : (S.state j).prepared.parameters.modelAccuracy ≤ εcap)
      (_hmodelOrder : 2 ≤ (S.state j).prepared.parameters.modelOrder)
      (_hclassScale : 32 * (S.state j).prepared.Qall *
        (S.state j).prepared.radiusBound ^ 2 ≤ 1)
      (_hfit : (S.state j).radius * Real.sqrt (S.state j).prepared.Qall ≤ 100 * cMax)
      (U : ℝ) (hU : 0 ≤ U)
      (T : Icc (0 : ℝ) (F.observation.observe U hU).horizon)
      (τ : Icc (0 : ℝ) W.oldNative.horizon)
      (_hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift)
      (_htop : (τ : ℝ) < W.oldNative.horizon)
      (_hback : ((S.state j).radius / 100) ^ 2 ≤ (τ : ℝ))
      (p x : ((F.observation.observe U hU).stageAt T).Carrier)
      (r : ℝ)
      (_hseed : GC.LongTime.hasSmallParabolicCurvature (F.observation.observe U hU) T p r)
      (_hseedVolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel ((F.observation.observe U hU).stageAt T).Carrier
          ((F.observation.observe U hU).stageMetric
            ((F.observation.observe U hU).activeStage T) T)
          (riemannianBallOf ((F.observation.observe U hU).stageMetric
            ((F.observation.observe U hU).activeStage T) T) p r))
      (_hx : x ∈ riemannianBallOf ((F.observation.observe U hU).stageMetric
        ((F.observation.observe U hU).activeStage T) T) p (A * r))
      (_hreserve : (S.state j).radius / 100 < r),
    ∀ ρ : ℝ, ρ < r →
      (F.observation.observe U hU).isParabolicallyRmControlledBall T x ρ →
      ENNReal.ofReal (κ * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel ((F.observation.observe U hU).stageAt T).Carrier
          ((F.observation.observe U hU).stageMetric
            ((F.observation.observe U hU).activeStage T) T)
          (riemannianBallOf ((F.observation.observe U hU).stageMetric
            ((F.observation.observe U hU).activeStage T) T) x ρ) ∨
      ∃ ρ' : ℝ, (S.state j).radius / 100 ≤ ρ' ∧ ρ' < r ∧ ρ ≤ ρ' ∧
        (F.observation.observe U hU).isParabolicallyRmControlledBall T x ρ' ∧
        ENNReal.ofReal (cBG * (ρ / ρ') ^ 3) *
            riemannianVolumeMeasure ThreeModel ((F.observation.observe U hU).stageAt T).Carrier
              ((F.observation.observe U hU).stageMetric
                ((F.observation.observe U hU).activeStage T) T)
              (riemannianBallOf ((F.observation.observe U hU).stageMetric
                ((F.observation.observe U hU).activeStage T) T) x ρ') ≤
          riemannianVolumeMeasure ThreeModel ((F.observation.observe U hU).stageAt T).Carrier
            ((F.observation.observe U hU).stageMetric
              ((F.observation.observe U hU).activeStage T) T)
            (riemannianBallOf ((F.observation.observe U hU).stageMetric
              ((F.observation.observe U hU).activeStage T) T) x ρ) := by
  classical
  obtain ⟨εcap, hεcap, reserve⟩ :=
    exists_same_native_reserve_ball_control_of_retained_class_quality.{u} Dstar hDstar
  obtain ⟨cBG, hcBG, hBG⟩ := exists_riemannianVolumeMeasure_ball_ge_of_rm_le.{u}
  refine ⟨εcap, cBG, hεcap, hcBG, ?_⟩
  intro P g C
  obtain ⟨_phi, _hphi, cMax, hcMax, hreserve⟩ := reserve P g C
  refine ⟨cMax, hcMax, ?_⟩
  intro A hA
  let C1bar := max C.C1s C.Cbirth
  let C2bar := max C.C2s (max C.Cbirth (C.Cgrad : ℝ))
  obtain ⟨κcan, hκcan, hcanonicalVolume⟩ :=
    exists_ball_volume_of_spatialCanonicalWitness.{u} C.epsilon C1bar C2bar
  obtain ⟨κwhole, hκwhole, hwholeVolume⟩ :=
    exists_ball_volume_lower_of_whole_canonical_component_and_seed.{u}
      C.epsilon C1bar C2bar A hA
  refine ⟨min κcan κwhole, lt_min hκcan hκwhole, ?_⟩
  intro pBase S F hTower j εcut Dcut mcut W hshift hoffset hshift_nonneg
    hmodelRadius hmodelAccuracy hmodelOrder hclassScale hfit U hU T τ hclock htop hback
    p x r hseed hseedVolume hx hsmallReserve ρ hρr htest
  let H := F.observation.observe U hU
  let gT := H.stageMetric (H.activeStage T) T
  let b := (S.state j).radius / 100
  have hr : 0 < r := hseed.1
  have hρ : 0 < ρ := htest.1
  have ratio (ρ' : ℝ) (hρρ' : ρ ≤ ρ')
      (hball : H.isParabolicallyRmControlledBall T x ρ') :
      ENNReal.ofReal (cBG * (ρ / ρ') ^ 3) *
          riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier gT
            (riemannianBallOf gT x ρ') ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier gT
          (riemannianBallOf gT x ρ) :=
    hBG gT x hρ hρρ' (fun z hz => hball.terminal_curvature_bound H z hz)
  by_cases hlargeTest : b ≤ ρ
  · exact Or.inr ⟨ρ, hlargeTest, hρr, le_rfl, htest, ratio ρ le_rfl htest⟩
  have hρb : ρ ≤ b := (lt_of_not_ge hlargeTest).le
  obtain ⟨hstage, hmetric, transport⟩ := S.native_query_transport_to_observation
    F hTower j W hshift hoffset U hU T τ hclock
  let y := overlapCastPoint hstage x
  have hpoint : HEq x y := (overlapCastPoint_heq hstage x).symm
  have hscalar := overlap_scalar_eq hstage hmetric hpoint
  by_cases hlow : metricScalarAt gT x ≤ (S.state j).prepared.Qall
  · have hlowNative : metricScalarAt
        (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) y ≤
          (S.state j).prepared.Qall := by
      rw [← hscalar]
      exact hlow
    have hnative := hreserve W (S.successor j) hshift hoffset hshift_nonneg
      hmodelRadius hmodelAccuracy hmodelOrder hclassScale hfit τ htop y hlowNative hback
    have hball : H.isParabolicallyRmControlledBall T x b :=
      transport x y hpoint b hnative
    exact Or.inr ⟨b, le_rfl, hsmallReserve, hρb, hball, ratio b hρb hball⟩
  · have hhighNative : (S.state j).prepared.Qall < metricScalarAt
        (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) y := by
      rw [← hscalar]
      exact lt_of_not_ge hlow
    obtain ⟨Vnative, hVnative⟩ := W.exists_spatialWitness_at_own_threshold τ htop y hhighNative
    obtain ⟨V, hV, _hVeq⟩ := overlap_spatialWitness_transport
      hstage.symm hmetric.symm hpoint.symm Vnative hVnative
    by_cases hreq : V.alternative.requiresVolume
    · have hcenter : ρ ^ 4 * normSq0S gT x 4 (metricRm04At gT x) ≤ 1 :=
        htest.terminal_curvature_bound H x (by
          change riemannianEDistOf gT x x < ENNReal.ofReal ρ
          rw [riemannianEDistOf_self]
          exact ENNReal.ofReal_pos.mpr hρ)
      refine Or.inl (le_trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_left κcan κwhole) (pow_nonneg hρ.le 3))) ?_)
      exact hcanonicalVolume V hV hreq ρ hρ hcenter
    · have hwhole : V.alternative.isWholeComponent := by
        cases hAlt : V.alternative with
        | neck _data => exact (hreq (by rw [hAlt]; trivial)).elim
        | cap _data _deep => exact (hreq (by rw [hAlt]; trivial)).elim
        | positive _whole _data _sec => exact (hreq (by rw [hAlt]; trivial)).elim
        | round _whole _data => trivial
      refine Or.inl (le_trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_right κcan κwhole) (pow_nonneg hρ.le 3))) ?_)
      exact hwholeVolume gT p x r ρ hr hρ hρr.le hx
        (seed_scalar_le_three_div_sq H T p hseed) hseedVolume V hwhole

end GC.GeneralFlow
