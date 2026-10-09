import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SmallTestReserveVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FirstCurvatureContactVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformPinching

/-!
# S-CH11-FIX9 port of astra `SmallTestLargeReserveVolume`（`PortC11P`）

来源：donor `SmallTestLargeReserveVolume.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* 2 处 `W.exists_spatialWitness_at_own_threshold …`：`open private … from SmallTestReserveVolume` 只开放
  全名，点记号找不到 private 声明 → 写全名 `PreparedSpatialStepRetention.
  exists_spatialWitness_at_own_threshold W …`；
* `htest.terminal_curvature_bound x (by …)`：本树 `terminal_curvature_bound` 的 `H` 是显式参数 → 补 `H`；
* `round` 情形：`cases hAlt : V.alternative` 已把目标里的 `V.alternative` 换掉，`rw [hAlt]` 找不到
  模式 → 直接 `trivial`；
* heartbeat：整条主定理（~300 行）是一个声明，共用 200000 heartbeat 预算（`norm_eq` 的陈述处 isDefEq
  超时，整体 whnf 超时）→ 把主定理里两个与上下文无关的局部引理 `norm_eq` / `closed_ball_iff`
  逐字抽成顶层 `private theorem`（`closed_ball_iff` 的 `r` 变成隐式参数），主定理调用处不变；
  不加 `set_option`；
* 主定理陈述里 11 个只在 `intro` 里引用的 binder 名（`hTower hshift hoffset hshift_nonneg hfit hclock
  htop hseed hseedVolume hx hreserve`）→ 加 `_` 前缀（unusedVariables；binder 名不改变陈述）。

原路径 `SmallTestLargeReserveVolume` 是只 import 本文件的 re-export shim。
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
open private PreparedSpatialStepRetention.exists_spatialWitness_at_own_threshold
  seed_scalar_le_three_div_sq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SmallTestReserveVolume

private theorem norm_eq {P₀ P₁ : OrientedThreeStage.{u}} (hP : P₀ = P₁)
    {g₀ : P₀.Metric} {g₁ : P₁.Metric} (hg : HEq g₀ g₁)
    {z₀ : P₀.Carrier} {z₁ : P₁.Carrier} (hz : HEq z₀ z₁) :
    normSq0S g₀ z₀ 4 (metricRm04At g₀ z₀) =
      normSq0S g₁ z₁ 4 (metricRm04At g₁ z₁) := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hz
  rfl

private theorem closed_ball_iff {P₀ P₁ : OrientedThreeStage.{u}} {r : ℝ} (hP : P₀ = P₁)
    {g₀ : P₀.Metric} {g₁ : P₁.Metric} (hg : HEq g₀ g₁)
    {x₀ z₀ : P₀.Carrier} {x₁ z₁ : P₁.Carrier}
    (hx' : HEq x₀ x₁) (hz : HEq z₀ z₁) :
    z₀ ∈ riemannianClosedBallOf g₀ x₀ r ↔ z₁ ∈ riemannianClosedBallOf g₁ x₁ r := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hx'
  cases eq_of_heq hz
  rfl

/-- An existing test below the seed scale has uniform volume when the same
pre-fine reserve is at least that scale. The low-center case uses the actual
spatial gradient and pinching at the query, including surgery births. -/
theorem exists_test_volume_in_same_observation_of_large_reserve
    (P : OrientedThreeStage.{u}) (g : P.Metric) (C : ClosedBirthConstants) :
    ∃ cSpatial : ℝ, 0 < cSpatial ∧
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
      (_hfit : (S.state j).radius * Real.sqrt (S.state j).prepared.Qall ≤ 100 * cSpatial)
      (U : ℝ) (hU : 0 ≤ U)
      (T : Icc (0 : ℝ) (F.observation.observe U hU).horizon)
      (τ : Icc (0 : ℝ) W.oldNative.horizon)
      (_hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift)
      (_htop : (τ : ℝ) < W.oldNative.horizon)
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
      (_hreserve : r ≤ (S.state j).radius / 100),
    ∀ ρ : ℝ, ρ < r →
      (F.observation.observe U hU).isParabolicallyRmControlledBall T x ρ →
      ENNReal.ofReal (κ * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel ((F.observation.observe U hU).stageAt T).Carrier
          ((F.observation.observe U hU).stageMetric
            ((F.observation.observe U hU).activeStage T) T)
          (riemannianBallOf ((F.observation.observe U hU).stageMetric
            ((F.observation.observe U hU).activeStage T) T) x ρ) := by
  classical
  obtain ⟨phi, hphi, hpinch⟩ := exists_uniform_pinching_for_same_full_native_steps P g
  let Kphi : ℝ := 4 * Real.sqrt 3 * (1 + phi 1 + phi 0)
  have hKphi : 0 < Kphi := by
    have h1 := hphi.pos 1
    have h0 := hphi.pos 0
    dsimp only [Kphi]
    positivity
  let cSpatial : ℝ := min 1 (min (1 / (4 * ((C.Cgrad : ℝ) + 1)))
    (1 / (8 * (Kphi + 1))))
  have hc : 0 < cSpatial := by dsimp only [cSpatial]; positivity
  have hcOne : cSpatial ≤ 1 := min_le_left _ _
  have hcGrad : cSpatial ≤ 1 / (4 * ((C.Cgrad : ℝ) + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcPhi : cSpatial ≤ 1 / (8 * (Kphi + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hGradCap : (C.Cgrad : ℝ) * cSpatial ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * ((C.Cgrad : ℝ) + 1))).mp hcGrad
    nlinarith only [h, hc.le]
  have hcSq : cSpatial ^ 2 ≤ cSpatial := by nlinarith only [hc.le, hcOne]
  have hPhiCap : Kphi * cSpatial ^ 2 ≤ 1 / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (Kphi + 1))).mp hcPhi
    have hKc : Kphi * cSpatial ≤ 1 / 8 := by nlinarith only [h, hc.le]
    exact (mul_le_mul_of_nonneg_left hcSq hKphi.le).trans hKc
  refine ⟨cSpatial, hc, ?_⟩
  intro A hA
  let C1bar := max C.C1s C.Cbirth
  let C2bar := max C.C2s (max C.Cbirth (C.Cgrad : ℝ))
  obtain ⟨κlow, hκlow, hlowVolume⟩ :=
    exists_ball_volume_lower_of_seed_and_canonical_first_contacts.{u}
      C.epsilon C1bar C2bar A hA
  obtain ⟨κcan, hκcan, hcanonicalVolume⟩ :=
    exists_ball_volume_of_spatialCanonicalWitness.{u} C.epsilon C1bar C2bar
  obtain ⟨κwhole, hκwhole, hwholeVolume⟩ :=
    exists_ball_volume_lower_of_whole_canonical_component_and_seed.{u}
      C.epsilon C1bar C2bar A hA
  refine ⟨min κlow (min κcan κwhole), lt_min hκlow (lt_min hκcan hκwhole), ?_⟩
  intro pBase S F hTower j εcut Dcut mcut W hshift hoffset hshift_nonneg hfit
    U hU T τ hclock htop p x r hseed hseedVolume hx hreserve ρ hρr htest
  let H := F.observation.observe U hU
  let gT := H.stageMetric (H.activeStage T) T
  let N := W.oldNative
  let gN := N.toHistory.stageMetric (N.toHistory.activeStage τ) τ
  let M : ℝ := (S.state j).prepared.Qall
  have hr : 0 < r := hseed.1
  have hρ : 0 < ρ := htest.1
  have hseedScalar : metricScalarAt gT p ≤ 3 / r ^ 2 :=
    seed_scalar_le_three_div_sq H T p hseed
  have decrease {κ' : ℝ} (hκ' : min κlow (min κcan κwhole) ≤ κ')
      (hvol : ENNReal.ofReal (κ' * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier gT
          (riemannianBallOf gT x ρ)) :
      ENNReal.ofReal (min κlow (min κcan κwhole) * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier gT
          (riemannianBallOf gT x ρ) :=
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hκ' (pow_nonneg hρ.le 3))).trans hvol
  obtain ⟨hstage, hmetric, _⟩ := S.native_query_transport_to_observation
    F hTower j W hshift hoffset U hU T τ hclock
  let y := overlapCastPoint hstage x
  have hpoint : HEq x y := (overlapCastPoint_heq hstage x).symm
  have hscalar := overlap_scalar_eq hstage hmetric hpoint
  by_cases hlow : metricScalarAt gT x ≤ M
  · have hM : 1 ≤ M := by
      apply le_trans ((le_max_left 1 (max (S.state j).prepared.qcan
        (S.state j).prepared.qs)).trans (S.state j).prepared.Qbirth_ge)
      change (S.state j).prepared.Qbirth ≤ (S.state j).prepared.Qall
      rw [(S.state j).prepared.Qall_eq]
      exact le_max_left _ _
    have hMpos : 0 < M := zero_lt_one.trans_le hM
    have hfitr : r * Real.sqrt M ≤ cSpatial := by
      have hsmall := mul_le_mul_of_nonneg_right hreserve (Real.sqrt_nonneg M)
      change (S.state j).radius * Real.sqrt M ≤ 100 * cSpatial at hfit
      nlinarith only [hsmall, hfit]
    have hMr : M * r ^ 2 ≤ cSpatial ^ 2 := by
      calc
        M * r ^ 2 = (r * Real.sqrt M) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hMpos.le]
          ring
        _ ≤ cSpatial ^ 2 := pow_le_pow_left₀ (by positivity) hfitr 2
    have hgradScale : (C.Cgrad : ℝ) * r * Real.sqrt M ≤ 1 / 4 := by
      calc
        (C.Cgrad : ℝ) * r * Real.sqrt M = C.Cgrad * (r * Real.sqrt M) := by ring
        _ ≤ C.Cgrad * cSpatial := mul_le_mul_of_nonneg_left hfitr C.Cgrad.coe_nonneg
        _ ≤ 1 / 4 := hGradCap
    have hpinchN := hpinch W (S.successor j) hshift hoffset hshift_nonneg
    have hlast : N.toHistory.activeStage τ = Fin.last N.eventCount →
        ∃ h : N.time (Fin.last N.eventCount) < N.horizon,
          Perelman.PhiAlmostNonnegative (N.finalSlab h).flow
            (Icc (N.time (Fin.last N.eventCount)) N.horizon) phi := by
      intro hlast
      have hstart : N.time (Fin.last N.eventCount) ≤ (τ : ℝ) := by
        simpa only [hlast] using N.toHistory.activeStage_time_le τ
      have hfinal := hstart.trans_lt htop
      exact ⟨hfinal, hpinchN.2 hfinal⟩
    have hRm (z : (N.toHistory.stageAt τ).Carrier) :
        Real.sqrt (normSq0S gN z 4 (metricRm04At gN z)) ≤
          Kphi * max (metricScalarAt gN z) 1 :=
      N.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinchN.1 τ hlast z
    obtain ⟨_, _, _, _, hpointGrad⟩ := W.own_threshold_native_certificates τ htop
    obtain ⟨s, G, _, _, _, hG, _, _, _, _⟩ :=
      W.oldNative_estimates.exists_outgoingSlab_of_lt_horizon τ htop
    have hgradNow : ∀ z, M < G.flow.scalar τ z → ∀ v : TangentSpace I3 z,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow τ z v| ≤
          C.Cgrad * G.flow.scalar τ z * Real.sqrt (G.flow.scalar τ z) *
            Real.sqrt ((G.flow.base.metric τ).inner z v v) := by
      intro z hz
      have hz' : M < metricScalarAt gN z := by
        change M < metricScalarAt (G.flow.base.metric τ) z at hz
        rwa [hG τ] at hz
      change ∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (G.flow.base.metric τ)) z v)| ≤
          C.Cgrad * metricScalarAt (G.flow.base.metric τ) z *
            Real.sqrt (metricScalarAt (G.flow.base.metric τ) z) *
            Real.sqrt ((G.flow.base.metric τ).inner z v v)
      rw [hG τ]
      exact (hpointGrad z hz').2
    have hlowN : metricScalarAt gN y ≤ M := by
      rw [← hscalar]
      exact hlow
    have hmax : max (G.flow.scalar τ y) M = M := by
      apply max_eq_right
      change metricScalarAt (G.flow.base.metric τ) y ≤ M
      rw [hG τ]
      exact hlowN
    have hmaxPos : 0 < max (G.flow.scalar τ y) M := by
      rw [hmax]
      exact hMpos
    have hgradMax : (C.Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar τ y) M) ≤ 1 / 4 := by
      rw [hmax]
      exact hgradScale
    have hspace : ∀ z ∈ riemannianClosedBallOf gN y r, metricScalarAt gN z ≤ 4 * M := by
      intro z hz
      have hzG : z ∈ riemannianClosedBallOf (G.flow.base.metric τ) y r := by
        rw [hG τ]
        exact hz
      have h := G.scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos
        hgradNow hmaxPos hgradMax hzG
      rw [hmax] at h
      change metricScalarAt (G.flow.base.metric τ) z ≤ 4 * M at h
      rwa [hG τ] at h
    have hnearN : ∀ z ∈ riemannianClosedBallOf gN y r,
        r ^ 4 * normSq0S gN z 4 (metricRm04At gN z) ≤ (1 : ℝ) / 4 := by
      intro z hz
      have hmaxBound : max (metricScalarAt gN z) 1 ≤ 4 * M :=
        max_le (hspace z hz) (by linarith only [hM])
      have hsqrt : Real.sqrt (normSq0S gN z 4 (metricRm04At gN z)) ≤ 4 * Kphi * M := by
        calc
          _ ≤ Kphi * max (metricScalarAt gN z) 1 := hRm z
          _ ≤ Kphi * (4 * M) := mul_le_mul_of_nonneg_left hmaxBound hKphi.le
          _ = 4 * Kphi * M := by ring
      have hscaled : r ^ 2 * Real.sqrt (normSq0S gN z 4 (metricRm04At gN z)) ≤ 1 / 2 := by
        calc
          _ ≤ r ^ 2 * (4 * Kphi * M) := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg r)
          _ = 4 * (Kphi * (M * r ^ 2)) := by ring
          _ ≤ 4 * (Kphi * cSpatial ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMr hKphi.le) (by norm_num)
          _ ≤ 1 / 2 := by linarith only [hPhiCap]
      calc
        _ = (r ^ 2 * Real.sqrt (normSq0S gN z 4 (metricRm04At gN z))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (normSq0S_nonneg _ _ _ _)]
          ring
        _ ≤ ((1 : ℝ) / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hscaled 2
        _ = 1 / 4 := by norm_num
    have hcontactN (z : (N.toHistory.stageAt τ).Carrier)
        (hz : r ^ 4 * normSq0S gN z 4 (metricRm04At gN z) = 1) :
        ∃ V : SpatialCanonicalWitness gN C.epsilon C1bar C2bar z,
          V.capTubeHasNeckChart C.epsilon := by
      have hhigh : M < metricScalarAt gN z := by
        by_contra hnot
        have hle : metricScalarAt gN z ≤ M := le_of_not_gt hnot
        have hmaxBound : max (metricScalarAt gN z) 1 ≤ M := max_le hle hM
        have hsqrt := (hRm z).trans (mul_le_mul_of_nonneg_left hmaxBound hKphi.le)
        have hscaled : r ^ 2 * Real.sqrt (normSq0S gN z 4 (metricRm04At gN z)) ≤ 1 / 8 := by
          calc
            _ ≤ r ^ 2 * (Kphi * M) := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg r)
            _ = Kphi * (M * r ^ 2) := by ring
            _ ≤ Kphi * cSpatial ^ 2 := mul_le_mul_of_nonneg_left hMr hKphi.le
            _ ≤ 1 / 8 := hPhiCap
        have hsq : (r ^ 2 * Real.sqrt (normSq0S gN z 4 (metricRm04At gN z))) ^ 2 = 1 := by
          calc
            _ = r ^ 4 * normSq0S gN z 4 (metricRm04At gN z) := by
              rw [mul_pow, Real.sq_sqrt (normSq0S_nonneg _ _ _ _)]
              ring
            _ = 1 := hz
        have hup := pow_le_pow_left₀ (by positivity :
          0 ≤ r ^ 2 * Real.sqrt (normSq0S gN z 4 (metricRm04At gN z))) hscaled 2
        rw [hsq] at hup
        norm_num at hup
      exact PreparedSpatialStepRetention.exists_spatialWitness_at_own_threshold W τ htop z hhigh
    have hnear : ∀ z ∈ riemannianClosedBallOf gT x r,
        r ^ 4 * normSq0S gT z 4 (metricRm04At gT z) ≤ (1 : ℝ) / 4 := by
      intro z hz
      let zN := overlapCastPoint hstage z
      have hzN : HEq z zN := (overlapCastPoint_heq hstage z).symm
      have hmem := (closed_ball_iff hstage hmetric hpoint hzN).mp hz
      rw [norm_eq hstage hmetric hzN]
      exact hnearN zN hmem
    have hcontact (z : (H.stageAt T).Carrier)
        (hz : r ^ 4 * normSq0S gT z 4 (metricRm04At gT z) = 1) :
        ∃ V : SpatialCanonicalWitness gT C.epsilon C1bar C2bar z,
          V.capTubeHasNeckChart C.epsilon := by
      let zN := overlapCastPoint hstage z
      have hzN : HEq z zN := (overlapCastPoint_heq hstage z).symm
      have heq : r ^ 4 * normSq0S gN zN 4 (metricRm04At gN zN) = 1 := by
        rw [← norm_eq hstage hmetric hzN]
        exact hz
      obtain ⟨V, hV⟩ := hcontactN zN heq
      obtain ⟨V', hV', _⟩ := overlap_spatialWitness_transport
        hstage.symm hmetric.symm hzN.symm V hV
      exact ⟨V', hV'⟩
    exact decrease (min_le_left _ _)
      (hlowVolume gT p x r ρ hr hρ hρr.le hx hseedScalar hseedVolume hnear hcontact)
  · have hhighNative : M < metricScalarAt gN y := by
      rw [← hscalar]
      exact lt_of_not_ge hlow
    obtain ⟨Vnative, hVnative⟩ :=
      PreparedSpatialStepRetention.exists_spatialWitness_at_own_threshold W τ htop y hhighNative
    obtain ⟨V, hV, _⟩ := overlap_spatialWitness_transport
      hstage.symm hmetric.symm hpoint.symm Vnative hVnative
    by_cases hreq : V.alternative.requiresVolume
    · have hcenter : ρ ^ 4 * normSq0S gT x 4 (metricRm04At gT x) ≤ 1 :=
        htest.terminal_curvature_bound H x (by
          change riemannianEDistOf gT x x < ENNReal.ofReal ρ
          rw [riemannianEDistOf_self]
          exact ENNReal.ofReal_pos.mpr hρ)
      exact decrease ((min_le_right _ _).trans (min_le_left _ _))
        (hcanonicalVolume V hV hreq ρ hρ hcenter)
    · have hwhole : V.alternative.isWholeComponent := by
        cases hAlt : V.alternative with
        | neck _data => exact (hreq (by rw [hAlt]; trivial)).elim
        | cap _data _deep => exact (hreq (by rw [hAlt]; trivial)).elim
        | positive _whole _data _sec => exact (hreq (by rw [hAlt]; trivial)).elim
        | round _whole _data => trivial
      exact decrease ((min_le_right _ _).trans (min_le_right _ _))
        (hwholeVolume gT p x r ρ hr hρ hρr.le hx hseedScalar hseedVolume V hwhole)

end GC.GeneralFlow
