import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeSurgeryDistC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardNeckedRayCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TriangularMappedJetsCXSP

/-!
# SPINE-A1 G6：native (N-bdd) 的 Λ 穿线——G46 → G48 → G55 → G60 与 G42 → G43 → G44 → G53 → G64

SPINE-B 分工（23:3x）：native 有界 ratio 子情形 `ρ < nr(τ) ≤ Λ ρ` 下，guard 链里 `nr ≤ r` 只经 G21
（record-scale 分离）被消费，SPINE-B 已给 Λ 版，G5 已给 time window 的 Λ 孪生。本文件把 guard 链
其余各叶（只把 `nr ≤ r` 往下传）逐字复制成 Λ 孪生：生成器 `build-logs/scratch/O-CH11-SPINE-A1/gen/`
（`twin.py` + `mk_x1.py`），只做三类断言计数过的替换：
* 陈述：`∀ Afac, 1 < Afac →` / `∀ A, 0 < A →` 之后插 `∀ Λ : ℝ, 1 ≤ Λ →`；guard 行
  `q.neckRadius _ ≤ r _` ↦ `q.neckRadius _ ≤ Λ * r _`；
* 证明：intro / 上游调用处补 `Λ hΛ`（只对被孪生的上游；G56 / G58 等无 guard 叶不动）；
* 名字：`foo_CXSP` ↦ `foo_bdd_C11SP`（含 private helper），上游引用随之改名。
`Λ = 1` 时各叶陈述退回原 guard 叶。不消费 hw / κ'' / Budget / SCRS⁺；不经 RegularSlice。
-/

set_option autoImplicit false

noncomputable section

universe u

section P6TimeBoundedBallCXSP

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

/-- 原 seed footprint 中的 terminal 球标量界，生产精确同球的 bounded-Rm traced region。 -/
theorem exists_prepared_time_bounded_ball_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 m0 : ℝ, 4 ≤ H0 ∧ 1 / 2 ≤ m0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ β0 : ℝ, 0 < β0 ∧
        ∀ m : ℝ, m0 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let Km := 2 * Real.sqrt 3 * ((2 * m) / 2 + max (2 * m) (2 * Real.exp 4))
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (y : (H.stageAt t).Carrier) (Rad dCenter : ℝ), 0 < Rad → 0 ≤ dCenter →
          dCenter + Rad / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let U := riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rad / Real.sqrt Q)
        (∀ x ∈ U, metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q) →
        H.isTracedRegion t y (Rad / Real.sqrt Q) ((β0 / (m + 1)) / Q) (Km * Q) := by
  obtain ⟨ε₀, hε₀, hpoint⟩ := exists_prepared_time_trace_window_of_ratio_C11SP P g
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨params, records, _hmodelR, _hmodelO, _hmodelA, _hparams, _hcan, _hOld,
    _hdecay, _hrecent⟩ := exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  obtain ⟨KG, TG, _hKG, _hTG, hGood⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans hA)
  obtain ⟨H0, hH0, hpointA⟩ := hpoint S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  have hHpos : 0 < H0 := by linarith only [hH0]
  let m0 : ℝ := max (1 / 2) (1 + 10000 * KG / H0)
  refine ⟨H0, m0, hH0, le_max_left _ _, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, βold, _hlam0, hβold, hpointM⟩ := hpointA d0 Δ γ hd0 hΔ hγ hbuffer
  let β0 : ℝ := min βold (min (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
  have hβ0 : 0 < β0 := by dsimp [β0]; positivity
  have hβoldle : β0 ≤ βold := min_le_left _ _
  have hβH : β0 ≤ H0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβtime : (Ctime : ℝ) * β0 ≤ 1 / 4 := by
    have h := (min_le_right βold _).trans
      (min_le_right (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * ((Ctime : ℝ) + 1))).mp h
    nlinarith only [hmul, hβ0]
  refine ⟨β0, hβ0, ?_⟩
  intro m hm0
  have hm : 1 / 2 ≤ m := (le_max_left _ _).trans hm0
  have hmp : 0 < m := by linarith only [hm]
  have hden : 0 < m + 1 := by linarith only [hm]
  have hGoodCoef : 10000 * KG ≤ H0 * m := by
    have h := (le_max_right (1 / 2) (1 + 10000 * KG / H0)).trans hm0
    have hratio : 10000 * KG / H0 ≤ m := by linarith only [h]
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  obtain ⟨TS, hTS, hpointN⟩ := hpointM m hm
  refine ⟨max (2 * TG) TS, hTS.trans_le (le_max_right _ _), ?_⟩
  intro n H t p r Q Km ht htime hsmall hvol hguard y Rad dCenter hRad hdCenter hfit hcenter
    U hscalar
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos hr))
  have hM : 0 < m * Q := mul_pos hmp hQ
  have hsmallCopy := hsmall
  obtain ⟨_hr, aSeed, haT, hclock, hseed⟩ := hsmallCopy
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨seedTrace, _hcontrolled⟩ := hseed p hp
  have hdist (x : (H.stageAt t).Carrier) (hx : x ∈ U) :
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) := by
    have hx' : riemannianEDistOf (H.stageMetric (H.activeStage t) t) y x <
        ENNReal.ofReal (Rad / Real.sqrt Q) := hx
    exact seed_closedBall_distance_CXSP (H.stageMetric (H.activeStage t) t)
      hHpos hr hRad.le hdCenter hfit hcenter x hx'.le
  have hpointX (x : (H.stageAt t).Carrier) (hx : x ∈ U) :=
    hpointN n t p r ((le_max_right _ _).trans ht) htime hsmall hvol hguard
      aSeed haT hclock seedTrace x (hscalar x hx) (hdist x hx)
  let β : ℝ := β0 / (m + 1)
  let ell : ℝ := (lam0 / (m + 1)) / Real.sqrt Q
  have hβ : 0 < β := div_pos hβ0 hden
  have hβle : β ≤ βold / (m + 1) := div_le_div_of_nonneg_right hβoldle hden.le
  have hβH' : β ≤ H0 / 4 :=
    (div_le_self hβ0.le (by linarith only [hm] : 1 ≤ m + 1)).trans hβH
  have htau : 0 < β / Q := div_pos hβ hQ
  have htauR : β / Q ≤ r ^ 2 / 4 := calc
    β / Q ≤ (H0 / 4) / Q := div_le_div_of_nonneg_right hβH' hQ.le
    _ = r ^ 2 / 4 := by dsimp only [Q]; field_simp [hHpos.ne', hr.ne']
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - β / Q,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r], (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have haa : aSeed ≤ a := by
    change (aSeed : ℝ) ≤ (t : ℝ) - β / Q
    rw [hclock]
    nlinarith only [htauR, sq_nonneg r]
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - β / Q
    nlinarith only [htauR, sq_nonneg r]
  have haClock : (a : ℝ) = (t : ℝ) - β / Q := rfl
  have hQa : 1 ≤ Q * (a : ℝ) := by
    have hra : r ^ 2 ≤ (a : ℝ) := by
      rw [haClock]
      nlinarith only [htime, htauR, sq_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left hra hQ.le
    have hQr : Q * r ^ 2 = H0 := by dsimp only [Q]; field_simp [hr.ne']
    rw [hQr] at hmul
    linarith only [hmul, hH0]
  have hbudget : Ctime * (m * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    have heq : (m + 1) * β = β0 := mul_div_cancel₀ _ hden.ne'
    have hmb : m * β ≤ β0 := by nlinarith only [heq, hβ]
    have htb := (mul_le_mul_of_nonneg_left hmb Ctime.coe_nonneg).trans hβtime
    have hc : Ctime * (m * Q) * ((t : ℝ) - a) = Ctime * (m * β) := by
      rw [haClock, sub_sub_cancel]
      field_simp [hQ.ne']
    rw [hc]
    linarith only [htb]
  have hGoodThreshold : (10000 * KG) * (r ^ 2)⁻¹ ≤ m * Q := by
    have hmul := mul_le_mul_of_nonneg_right hGoodCoef (inv_nonneg.mpr (sq_nonneg r))
    dsimp only [Q]
    nlinarith only [hmul]
  refine ⟨div_pos hRad (Real.sqrt_pos.mpr hQ), htau, a, hat, rfl, ?_⟩
  intro x hx
  obtain ⟨ax, _haxSeed, _haxt, hxClock, _hxDepth, Bold, hBold⟩ := hpointX x hx
  have haxa : ax ≤ a := by
    change (ax : ℝ) ≤ (t : ℝ) - β / Q
    rw [hxClock]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hβle hQ.le) _
  let B := Bold.restrictFirst (H.activeStage_mono haxa) (H.activeStage_mono hat)
  let AA := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
  have hdistance (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      AA.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
      AA.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        AA.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) :=
    hBold v (haxa.trans hav) hvt
  have hcontrol := B.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v hav hvt hage htop hRv => by
      have hfoot : B.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt) ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haa.trans hav))
            (H.activeStage_mono hvt)) (Afac * r) :=
        (hdistance v hav hvt).1.trans_le (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (by linarith only [hbuffer, hγ] : d0 + Δ ≤ Afac) hr.le))
      have hGoodV := hGood n t p r ((le_max_left _ _).trans ht)
        htime hsmall hvol aSeed haT hclock seedTrace v (haa.trans hav) hvt
        (hhalf.trans (show (a : ℝ) ≤ v from hav)) _ hfoot
        (hGoodThreshold.trans_lt hRv).le
      exact hGoodV.2 hage htop) (hscalar x hx) hbudget
  refine ⟨B, ?_⟩
  exact B.isRmBoundedBy_of_scalar_and_HI_CXSP ha₀.le hQ (by positivity) hQa
    (fun v z => hHI F n (records n) v z)
    (fun v hav hvt => by simpa only [mul_assoc] using hcontrol v hav hvt)

end GC.LongTime.Ch11

end P6TimeBoundedBallCXSP

section P6TimeScalarEscapeCXSP

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem escape_scaled_ball_eq_bdd_C11SP
    {P : OrientedThreeStage.{u}} (g : P.Metric) (x : P.Carrier)
    {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    riemannianBallOf (scaleMetric Q hQ g) x R =
      riemannianBallOf g x (R / Real.sqrt Q) := by
  have h := riemannianBallOf_scaleMetric Q hQ g x (R / Real.sqrt Q)
  rwa [mul_div_cancel₀ R (Real.sqrt_pos.mpr hQ).ne'] at h

private theorem escape_primary_radius_bdd_C11SP {chi Q : ℝ}
    (hchi : 0 < chi) (hQ : 0 < Q) (R : ℝ) :
    (R / Real.sqrt chi) / Real.sqrt Q = R / Real.sqrt (chi * Q) := by
  rw [Real.sqrt_mul hchi.le]
  field_simp [(Real.sqrt_pos.mpr hchi).ne', (Real.sqrt_pos.mpr hQ).ne']

private theorem escape_primary_traced_region_bdd_C11SP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon} {x : (H.stageAt t).Carrier}
    {chi Q R beta K : ℝ} (hchi : 0 < chi) (hQ : 0 < Q)
    (h : H.isTracedRegion t x ((R / Real.sqrt chi) / Real.sqrt Q)
      (beta / Q) (K * Q)) :
    H.isTracedRegion t x (R / Real.sqrt (chi * Q))
      ((chi * beta) / (chi * Q)) ((K / chi) * (chi * Q)) := by
  have hr := escape_primary_radius_bdd_C11SP hchi hQ R
  have ht : (chi * beta) / (chi * Q) = beta / Q := by
    field_simp [hchi.ne', hQ.ne']
  have hk : (K / chi) * (chi * Q) = K * Q := by
    field_simp [hchi.ne']
  rw [ht, hk, ← hr]
  exact h

/-- TimeCore 与实际 prepared chain 在原 stage carrier 生产 scalar-escape pointed limit
的完整数据；辅助常数先于 sequence 及其 primary-scale multiplier 选取。 -/
theorem exists_prepared_time_scalar_escape_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ (Haux m0 Kb Tb : ℝ) (hHaux : 4 ≤ Haux),
        1 / 2 ≤ m0 ∧ 0 < Kb ∧ 0 < Tb ∧
        ∀ d0 Δ gamma : ℝ, 0 ≤ d0 → 0 < Δ → 0 < gamma → d0 + Δ + gamma ≤ Afac →
        ∀ chi : ℝ, ∀ hchi : 1 ≤ chi,
          max Kb (4 * max C2 1) ≤ chi * Haux →
        ∀ Rad dAnchor : ℝ, 0 ≤ dAnchor →
          dAnchor + Rad / Real.sqrt (chi * Haux) ≤ d0 →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (time : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p anchor : ∀ i, ((H i).stageAt (time i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (time i : ℝ)) →
        ∀ hsmall : ∀ i, hasSmallParabolicCurvature (H i) (time i) (p i) (r i),
          (∀ i, ENNReal.ofReal (Afac⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (time i)) (time i)) (p i) (r i)) →
          (∀ i, q.neckRadius (time i) ≤ Λ * r i) →
          Tendsto (fun i => (time i : ℝ)) atTop atTop →
        let stage : ℕ → OrientedThreeStage.{u} := fun i => (H i).stageAt (time i)
        let metric : ∀ i, (stage i).Metric :=
          fun i => (H i).stageMetric ((H i).activeStage (time i)) (time i)
        let Qbase : ℕ → ℝ := fun i => chi * (Haux * (r i ^ 2)⁻¹)
        let hQbase : ∀ i, 0 < Qbase i := fun i =>
          mul_pos (zero_lt_one.trans_le hchi)
            (mul_pos (by linarith only [hHaux]) (inv_pos.mpr (sq_pos_of_pos (hsmall i).1)))
        let Xall : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := (stage i).Carrier
                basepoint := anchor i
                metric := scaleMetric (Qbase i) (hQbase i) (metric i) } };
          (∀ i, metricScalarAt (metric i) (anchor i) = Qbase i) →
          (∀ i, riemannianEDistOf (metric i) (p i) (anchor i) ≤
            ENNReal.ofReal (dAnchor * r i)) →
          (∃ R : ℝ, 0 < R ∧ R + 2 ≤ Rad ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
            ∀ z : (stage i).Carrier,
              riemannianEDistOf (Xall.obj i).metric (anchor i) z < ENNReal.ofReal R →
              metricScalarAt (metric i) z / Qbase i ≤ B) →
        ∃ rho : ℝ, 0 < rho ∧ rho + 2 ≤ Rad ∧
          ∃ ind : ℕ → ℕ, StrictMono ind ∧ ∃ z : ∀ i, (stage (ind i)).Carrier,
          let X := Xall.subseq ind
          ∃ f : ℕ → ℕ, StrictMono f ∧
            ∃ rad : ℕ → ℝ, (∀ n, 0 < rad n ∧ rad n < rho) ∧ Tendsto rad atTop (𝓝 rho) ∧
            ∃ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
              (maps : PointedRiemannianConvergenceMaps X.connectedComponent Pl f),
              let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
              let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
              let maps' := maps.liftTargetOpen U hp
              ∃ M : MetricConvergenceData maps',
                metricScalarAt Pl.metric Pl.basepoint = 1 ∧
                (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData maps' n) ∧
                (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
                (∀ R : ℝ, 0 ≤ R → R < rho →
                  IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
                (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint
                  (rad n) ⊆ maps'.target n) ∧
                (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ y ∈ maps'.source n,
                  ∀ v : TangentSpace ThreeModel y,
                    (1 - eta) * Pl.metric.inner y v v ≤
                      (X.obj (f n)).metric.inner (maps'.map n y)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v) ∧
                    (X.obj (f n)).metric.inner (maps'.map n y)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v) ≤
                      (1 + eta) * Pl.metric.inner y v v) ∧
                (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint
                  (z (f n)) ≠ ⊤) ∧
                Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric
                  (X.obj (f n)).basepoint (z (f n))).toReal) atTop (𝓝 rho) ∧
                Tendsto (fun n => metricScalarAt (metric (ind (f n))) (z (f n)) /
                  Qbase (ind (f n))) atTop atTop := by
  obtain ⟨ε₀, hε₀, hbounded⟩ := exists_prepared_time_bounded_ball_bdd_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨Kb, Tb, hKb, hTb, hcanonical⟩ := hb Afac (zero_lt_one.trans hA)
  obtain ⟨Haux, m0, hHaux, hm0, hboundedA⟩ :=
    hbounded S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  refine ⟨Haux, m0, Kb, Tb, hHaux, hm0, hKb, hTb, ?_⟩
  intro d0 Δ gamma hd0 hΔ hgamma hbuffer
  obtain ⟨β0, hβ0, hboundedM⟩ := hboundedA d0 Δ gamma hd0 hΔ hgamma hbuffer
  intro chi hchi hscale Rad dAnchor hdAnchor hfit idx H time p anchor r htime hsmall hvol
    hguard htlim stage metric Qbase hQbase Xall hanchorR hanchorDist hfailure
  have hchip : 0 < chi := zero_lt_one.trans_le hchi
  have hHpos : 0 < Haux := by linarith only [hHaux]
  have hHbase : 0 < chi * Haux := mul_pos hchip hHpos
  have hr (i : ℕ) : 0 < r i := (hsmall i).1
  obtain ⟨Rbad, hRbad, hRbadRad, hfail⟩ := hfailure
  have hRad : 0 < Rad := by linarith only [hRbad, hRbadRad]
  have hcenterA : dAnchor < Afac := by
    have hterm : 0 < Rad / Real.sqrt (chi * Haux) :=
      div_pos hRad (Real.sqrt_pos.mpr hHbase)
    linarith only [hfit, hbuffer, hΔ, hgamma, hterm]
  have hanchorBall (i : ℕ) : anchor i ∈ riemannianBallOf (metric i) (p i) (Afac * r i) := by
    apply (hanchorDist i).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (zero_lt_one.trans hA) (hr i))).mpr
    exact mul_lt_mul_of_pos_right hcenterA (hr i)
  have hhigh (i : ℕ) : max Kb (4 * max C2 1) * (r i ^ 2)⁻¹ ≤
      metricScalarAt (metric i) (anchor i) := by
    have hmul := mul_le_mul_of_nonneg_right hscale (inv_nonneg.mpr (sq_nonneg (r i)))
    rw [hanchorR i]
    dsimp only [Qbase]
    nlinarith only [hmul]
  have hbase : ∀ᶠ i in atTop,
      ∃ W : SpatialCanonicalWitness (metric i) ε C1 C2 (anchor i),
        W.capTubeHasNeckChart ε ∧ ∃ y ∈ connectedComponent (anchor i),
          C2 * metricScalarAt (metric i) y < metricScalarAt (metric i) (anchor i) := by
    filter_upwards [htlim.eventually_ge_atTop Tb] with i hi
    obtain ⟨W, hchart, hpcomp, hgap⟩ := exists_seed_volume_base_CXSP
      (hsmall i) (hanchorBall i) (hhigh i)
      (fun y hy hyR =>
        (hcanonical (idx i) (time i) (p i) (r i) hi (htime i) (hsmall i)
          (hvol i) y hy hyR).1)
    exact ⟨W, hchart, p i, hpcomp, hgap⟩
  let distN (i : ℕ) (z : (stage i).Carrier) : ℝ≥0∞ :=
    riemannianEDistOf (Xall.obj i).metric (anchor i) z
  let scalarN (i : ℕ) (z : (stage i).Carrier) : ℝ := metricScalarAt (metric i) z / Qbase i
  have hunit : ∃ B : ℝ, ∀ᶠ i in atTop, ∀ z : (stage i).Carrier,
      distN i z < ENNReal.ofReal (1 : ℝ) → scalarN i z ≤ B := by
    refine ⟨C2, hbase.mono ?_⟩
    intro i hi z hz
    obtain ⟨W, _hchart, _hgap⟩ := hi
    have hzBall : z ∈ riemannianBallOf (scaleMetric (Qbase i) (hQbase i) (metric i))
        (anchor i) 1 := hz
    rw [escape_scaled_ball_eq_bdd_C11SP (metric i) (anchor i) (hQbase i) 1] at hzBall
    have hradius : 1 / Real.sqrt (Qbase i) ≤ W.radius := by
      simpa only [hanchorR i, one_div] using W.radius_lower
    have hbz := (W.scalar_bounds z
      (W.ball_inside (riemannianBallOf_mono _ _ hradius hzBall))).2
    apply (div_le_iff₀ (hQbase i)).mpr
    simpa only [hanchorR i] using hbz
  obtain ⟨rho, ind, hOneRho, hind, hinner, z, hfinite, hdist, hescape⟩ :=
    Analysis.exists_subsequence_radius_escape distN scalarN (by norm_num : (0 : ℝ) < 1)
      hunit ⟨Rbad, hRbad, hfail⟩
  have hrho : 0 < rho := zero_lt_one.trans_le hOneRho
  have hrhoBad : rho ≤ Rbad := by
    by_contra hnot
    obtain ⟨B, hB⟩ := hinner Rbad (lt_of_not_ge hnot)
    exact hfail ⟨B, hB⟩
  have hrhoRad : rho + 2 ≤ Rad := by linarith only [hrhoBad, hRbadRad]
  have hjets : ∀ R : ℝ, 0 < R → R < rho → ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
      ∀ᶠ i in atTop, HasLocalCurvDerivBound (Xall.obj i) (Xall.obj i).basepoint R k J := by
    intro R hR hRrho k
    let Rwide : ℝ := (R + rho) / 2
    have hRRwide : R < Rwide := by dsimp only [Rwide]; linarith only [hRrho]
    have hRwide : 0 < Rwide := hR.trans hRRwide
    have hRwiderho : Rwide < rho := by dsimp only [Rwide]; linarith only [hRrho]
    obtain ⟨B, hB⟩ := hinner Rwide hRwiderho
    let m : ℝ := max m0 (max 1 (B * chi))
    have hmm0 : m0 ≤ m := le_max_left _ _
    have hm1 : 1 ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    have hmp : 0 < m := zero_lt_one.trans_le hm1
    have hBm : B * chi ≤ m := (le_max_right _ _).trans (le_max_right _ _)
    have hden : 0 < m + 1 := by linarith only [hm1]
    let RadAux : ℝ := Rwide / Real.sqrt chi
    have hRadAux : 0 < RadAux := div_pos hRwide (Real.sqrt_pos.mpr hchip)
    have hfitAux : dAnchor + RadAux / Real.sqrt Haux ≤ d0 := by
      have hfitR : Rwide / Real.sqrt (chi * Haux) ≤ Rad / Real.sqrt (chi * Haux) :=
        div_le_div_of_nonneg_right (by linarith only [hRwiderho, hrhoRad])
          (Real.sqrt_nonneg _)
      have heq : RadAux / Real.sqrt Haux = Rwide / Real.sqrt (chi * Haux) :=
        escape_primary_radius_bdd_C11SP hchip hHpos Rwide
      rw [heq]
      linarith only [hfitR, hfit]
    let Km : ℝ := 2 * Real.sqrt 3 * ((2 * m) / 2 + max (2 * m) (2 * Real.exp 4))
    have hKm : 0 < Km := by dsimp only [Km]; positivity
    let theta : ℝ := chi * (β0 / (m + 1))
    let Kprim : ℝ := Km / chi
    have htheta : 0 < theta := mul_pos hchip (div_pos hβ0 hden)
    have hKprim : 0 < Kprim := div_pos hKm hchip
    obtain ⟨Tm, _hTm, hboundedN⟩ := hboundedM m hmm0
    obtain ⟨J, hJ, hinnerJets⟩ := exists_inner_jets_of_traced_region_CXSP
      R Rwide theta Kprim hR.le hRRwide htheta hKprim
    refine ⟨J k, zero_le_one.trans (hJ k), ?_⟩
    filter_upwards [hB, htlim.eventually_ge_atTop Tm] with i hi hti
    let Qaux : ℝ := Haux * (r i ^ 2)⁻¹
    have hQaux : 0 < Qaux := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos (hr i)))
    have hprimary : Qbase i = chi * Qaux := rfl
    have hradius : RadAux / Real.sqrt Qaux = Rwide / Real.sqrt (Qbase i) :=
      escape_primary_radius_bdd_C11SP hchip hQaux Rwide
    have hterminal : ∀ w ∈ riemannianBallOf (metric i) (anchor i)
        (RadAux / Real.sqrt Qaux), metricScalarAt (metric i) w ≤ m * Qaux := by
      intro w hw
      have hwN : w ∈ riemannianBallOf (scaleMetric (Qbase i) (hQbase i) (metric i))
          (anchor i) Rwide := by
        rw [escape_scaled_ball_eq_bdd_C11SP (metric i) (anchor i) (hQbase i) Rwide, ← hradius]
        exact hw
      have hR : metricScalarAt (metric i) w ≤ B * Qbase i :=
        (div_le_iff₀ (hQbase i)).mp (hi w hwN)
      refine hR.trans ?_
      rw [hprimary]
      calc B * (chi * Qaux) = (B * chi) * Qaux := by ring
           _ ≤ m * Qaux := mul_le_mul_of_nonneg_right hBm hQaux.le
    have htr : (H i).isTracedRegion (time i) (anchor i) (RadAux / Real.sqrt Qaux)
        ((β0 / (m + 1)) / Qaux) (Km * Qaux) :=
      hboundedN (idx i) (time i) (p i) (r i) hti (htime i) (hsmall i) (hvol i)
        (hguard i) (anchor i) RadAux dAnchor hRadAux hdAnchor hfitAux (hanchorDist i) hterminal
    have htrPrimary : (H i).isTracedRegion (time i) (anchor i)
        (Rwide / Real.sqrt (Qbase i)) (theta / Qbase i) (Kprim * Qbase i) :=
      escape_primary_traced_region_bdd_C11SP hchip hQaux htr
    intro w hw
    exact hinnerJets (H i) (time i) (anchor i) (Qbase i) (hQbase i) htrPrimary k w hw
  have hconv := exists_stage_pointed_convergence_of_jets_CXSP
    (fun i => stage (ind i)) (fun i => metric (ind i)) (fun i => Qbase (ind i))
    (fun i => hQbase (ind i)) (fun i => anchor (ind i)) ε C1 C2 hrho
    (hind.tendsto_atTop.eventually hbase) (fun R hR hRrho k => by
      obtain ⟨J, hJ, hbnd⟩ := hjets R hR hRrho k
      exact ⟨J, hJ, hind.tendsto_atTop.eventually hbnd⟩)
  obtain ⟨f, hf, rad, hrad, hradlim, Pl, maps, M, hcanonicalDomain, hradial, hcompact,
    hcapture, hmetric⟩ := hconv
  have hscalarOne : metricScalarAt Pl.metric Pl.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M
      hcanonicalDomain (by
        intro n
        change metricScalarAt (scaleMetric (Qbase (ind (f n))) (hQbase (ind (f n)))
          (metric (ind (f n)))) (anchor (ind (f n))) = 1
        rw [metricScalarAt_scaleMetric, hanchorR (ind (f n)),
          inv_mul_cancel₀ (hQbase (ind (f n))).ne'])
  refine ⟨rho, hrho, hrhoRad, ind, hind, z, ?_⟩
  exact ⟨f, hf, rad, hrad, hradlim, Pl, maps, M, hscalarOne, hcanonicalDomain,
    hradial, hcompact, hcapture, hmetric, fun n => hfinite (f n),
    hdist.comp hf.tendsto_atTop, hescape.comp hf.tendsto_atTop⟩

end GC.LongTime.Ch11

end P6TimeScalarEscapeCXSP

section P6GuardScalarEscapeCXSP

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem guard_scaleMetric_congr_bdd_C11SP
    {P : OrientedThreeStage.{u}} (g : P.Metric) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hcd : c = d) :
    scaleMetric c hc g = scaleMetric d hd g := by
  subst d
  rfl

/-- 原 scalar 坏序列的 guard 分支直接产生完整 first-level pointed escape；所有尺度常数
先于该序列选取，anchor、fit、scalar failure 和几何紧性供给均在证明内完成。 -/
theorem exists_guard_scalar_escape_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ A : ℝ, 0 < A → ∀ Λ : ℝ, 1 ≤ Λ → ∃ Hbase : ℝ, 4 ≤ Hbase ∧
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, q.neckRadius (t i) ≤ Λ * r i) →
      ∃ N : ℕ,
        let φ : ℕ → ℕ := fun i => i + N
        StrictMono φ ∧ ∃ anchor : ∀ i, ((H (φ i)).stageAt (t (φ i))).Carrier,
        let stage : ℕ → OrientedThreeStage.{u} := fun i => (H (φ i)).stageAt (t (φ i))
        let metric : ∀ i, (stage i).Metric :=
          fun i => (H (φ i)).stageMetric ((H (φ i)).activeStage (t (φ i))) (t (φ i))
        ∃ (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
        (∀ i, Q i = Hbase * (r (φ i) ^ 2)⁻¹) ∧
        let Xall : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := (stage i).Carrier
                basepoint := anchor i
                metric := scaleMetric (Q i) (hQ i) (metric i) } };
        (∀ i, metricScalarAt (metric i) (anchor i) = Q i) ∧
        (∀ i, riemannianEDistOf (metric i) (p (φ i)) (anchor i) ≤
          ENNReal.ofReal (A * r (φ i))) ∧
        (∀ i, ∃ (L : ℝ) (γ : ℝ → (stage i).Carrier) (s : ℝ),
          0 ≤ L ∧ L < A * r (φ i) ∧ γ 0 = p (φ i) ∧ γ L = x (φ i) ∧
          ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
          (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
            riemannianEDistOf (metric i) (γ a) (γ b) = ENNReal.ofReal |a - b|) ∧
          s ∈ Ioo (0 : ℝ) L ∧ γ s = anchor i ∧
          (∀ v ∈ Icc (0 : ℝ) (L - s),
            γ (s + v) ∈ riemannianBallOf (metric i) (p (φ i)) (A * r (φ i)) ∧
              Q i ≤ metricScalarAt (metric i) (γ (s + v)))) ∧
        (∀ i, riemannianEDistOf (Xall.obj i).metric (anchor i) (x (φ i)) <
          ENNReal.ofReal (A * Real.sqrt Hbase)) ∧
        Tendsto (fun i => metricScalarAt (metric i) (x (φ i)) / Q i) atTop atTop ∧
        ∃ rho : ℝ, 0 < rho ∧ rho + 2 ≤ A * Real.sqrt Hbase + 3 ∧
          ∃ ind : ℕ → ℕ, StrictMono ind ∧ ∃ z : ∀ i, (stage (ind i)).Carrier,
          let X := Xall.subseq ind
          ∃ f : ℕ → ℕ, StrictMono f ∧
            ∃ rad : ℕ → ℝ, (∀ n, 0 < rad n ∧ rad n < rho) ∧ Tendsto rad atTop (𝓝 rho) ∧
            ∃ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
              (maps : PointedRiemannianConvergenceMaps X.connectedComponent Pl f),
              let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
              let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
              let maps' := maps.liftTargetOpen U hp
              ∃ M : MetricConvergenceData maps',
                metricScalarAt Pl.metric Pl.basepoint = 1 ∧
                (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData maps' n) ∧
                (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
                (∀ R : ℝ, 0 ≤ R → R < rho →
                  IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
                (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint
                  (rad n) ⊆ maps'.target n) ∧
                (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ y ∈ maps'.source n,
                  ∀ v : TangentSpace ThreeModel y,
                    (1 - eta) * Pl.metric.inner y v v ≤
                      (X.obj (f n)).metric.inner (maps'.map n y)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v) ∧
                    (X.obj (f n)).metric.inner (maps'.map n y)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v)
                        (mfderiv ThreeModel ThreeModel (maps'.map n) y v) ≤
                      (1 + eta) * Pl.metric.inner y v v) ∧
                (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint
                  (z (f n)) ≠ ⊤) ∧
                Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric
                  (X.obj (f n)).basepoint (z (f n))).toReal) atTop (𝓝 rho) ∧
                Tendsto (fun n => metricScalarAt (metric (ind (f n))) (z (f n)) /
                  Q (ind (f n))) atTop atTop := by
  obtain ⟨ε₀, hε₀, hescape⟩ := exists_prepared_time_scalar_escape_bdd_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb A hA Λ hΛ
  let Awork : ℝ := 4 * A + 4
  have hAwork : 1 < Awork := by dsimp only [Awork]; linarith only [hA]
  have hAAwork : A ≤ Awork := by dsimp only [Awork]; linarith only [hA]
  obtain ⟨Haux, _m0, Kb, _Tb, hHaux, _hm0, _hKb, _hTb, hrun⟩ :=
    hescape S F q hTower hdiag hacc hrad hord hb Awork hAwork Λ hΛ
  have hHauxPos : 0 < Haux := by linarith only [hHaux]
  let chi : ℝ := max 1 (max Kb (4 * max C2 1) / Haux)
  have hchi : 1 ≤ chi := le_max_left _ _
  have hscale : max Kb (4 * max C2 1) ≤ chi * Haux :=
    (div_le_iff₀ hHauxPos).mp (le_max_right _ _)
  let Hbase : ℝ := chi * Haux
  have hHbase : 4 ≤ Hbase := hHaux.trans (by
    dsimp only [Hbase]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hchi hHauxPos.le)
  have hHbasePos : 0 < Hbase := by linarith only [hHbase]
  let Rad : ℝ := A * Real.sqrt Hbase + 3
  have hsqrt : 2 ≤ Real.sqrt Hbase := by
    nlinarith only [Real.sq_sqrt hHbasePos.le, Real.sqrt_nonneg Hbase, hHbase]
  have hradDiv : Rad / Real.sqrt Hbase ≤ A + 2 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hHbasePos)).mpr
    dsimp only [Rad]
    nlinarith only [hsqrt]
  have hfit : A + Rad / Real.sqrt (chi * Haux) ≤ 2 * A + 2 := by
    change A + Rad / Real.sqrt Hbase ≤ 2 * A + 2
    linarith only [hradDiv]
  have hbuffer : (2 * A + 2) + 1 + 1 ≤ Awork := by
    dsimp only [Awork]
    linarith only [hA]
  have hrunFixed := hrun (2 * A + 2) 1 1 (by positivity) zero_lt_one zero_lt_one
    hbuffer chi hchi hscale Rad A hA.le hfit
  refine ⟨Hbase, hHbase, ?_⟩
  intro idx H t p x r htime hsmall hvol hx htlim hbad hguard
  obtain ⟨N, hanchors⟩ := exists_scalar_anchor_sequence_CXSP H t p x r hA hHbase hsmall hx hbad
  refine ⟨N, ?_⟩
  intro φ
  obtain ⟨hφ, anchor, hanchorR, hanchorDist, hgeom, hnorm, _hratio, hbadQ, hfailure⟩ := hanchors
  refine ⟨hφ, anchor, ?_⟩
  intro stage metric
  let Q : ℕ → ℝ := fun i => chi * (Haux * (r (φ i) ^ 2)⁻¹)
  have hQ (i : ℕ) : 0 < Q i :=
    mul_pos (zero_lt_one.trans_le hchi)
      (mul_pos hHauxPos (inv_pos.mpr (sq_pos_of_pos (hsmall (φ i)).1)))
  have hscaleSeed (i : ℕ) : Q i = Hbase * (r (φ i) ^ 2)⁻¹ :=
    (mul_assoc chi Haux ((r (φ i) ^ 2)⁻¹)).symm
  refine ⟨Q, hQ, hscaleSeed, ?_⟩
  intro Xall
  let Qseed : ℕ → ℝ := fun i => Hbase * (r (φ i) ^ 2)⁻¹
  have hQseed (i : ℕ) : 0 < Qseed i :=
    mul_pos hHbasePos (inv_pos.mpr (sq_pos_of_pos (hsmall (φ i)).1))
  have hmetricSeed (i : ℕ) : scaleMetric (Q i) (hQ i) (metric i) =
      scaleMetric (Qseed i) (hQseed i) (metric i) :=
    guard_scaleMetric_congr_bdd_C11SP (metric i) (hQ i) (hQseed i) (hscaleSeed i)
  have hanchorPrimary (i : ℕ) : metricScalarAt (metric i) (anchor i) = Q i :=
    (hanchorR i).trans (hscaleSeed i).symm
  have hnormPrimary (i : ℕ) :
      riemannianEDistOf (Xall.obj i).metric (anchor i) (x (φ i)) <
        ENNReal.ofReal (A * Real.sqrt Hbase) := by
    change riemannianEDistOf (scaleMetric (Q i) (hQ i) (metric i)) _ _ < _
    rw [hmetricSeed i]
    exact hnorm i
  have hbadPrimary : Tendsto (fun i => metricScalarAt (metric i) (x (φ i)) / Q i)
      atTop atTop := by
    have heq : (fun i => metricScalarAt (metric i) (x (φ i)) / Q i) =
        fun i => metricScalarAt (metric i) (x (φ i)) / Qseed i := by
      funext i
      rw [hscaleSeed i]
    rw [heq]
    exact hbadQ
  refine ⟨hanchorPrimary, hanchorDist, ?_, hnormPrimary, hbadPrimary, ?_⟩
  · intro i
    obtain ⟨L, γ, s, hL, hlen, hstart, hend, hsmooth, _hcomp, hdist, hs, hbase,
      _hlast, hclosed, _hopen, _hdistend, _hshort⟩ := hgeom i
    refine ⟨L, γ, s, hL, hlen, hstart, hend, hsmooth, hdist, hs, hbase, ?_⟩
    intro v hv
    obtain ⟨hfoot, hscalar⟩ := hclosed v hv
    refine ⟨hfoot, ?_⟩
    rw [hscaleSeed i]
    exact hscalar
  · have hvolWork (i : ℕ) : ENNReal.ofReal (Awork⁻¹ * r i ^ 3) ≤
        ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i) :=
      seed_volume_of_parameter_le_CXSP (hsmall i) hA hAAwork (hvol i)
    have hfailurePrimary : ∃ R : ℝ, 0 < R ∧ R + 2 ≤ Rad ∧
        ¬ ∃ B : ℝ, ∀ᶠ i in atTop, ∀ z : (stage i).Carrier,
          riemannianEDistOf (Xall.obj i).metric (anchor i) z < ENNReal.ofReal R →
            metricScalarAt (metric i) z / Q i ≤ B := by
      obtain ⟨R, hR, hRad, hfail⟩ := hfailure
      refine ⟨R, hR, hRad, ?_⟩
      rintro ⟨B, hB⟩
      apply hfail
      refine ⟨B, ?_⟩
      filter_upwards [hB] with i hi z hz
      have hzPrimary : riemannianEDistOf (Xall.obj i).metric (anchor i) z <
          ENNReal.ofReal R := by
        change riemannianEDistOf (scaleMetric (Q i) (hQ i) (metric i)) _ _ < _
        rwa [hmetricSeed i]
      simpa only [hscaleSeed i] using hi z hzPrimary
    have hout := hrunFixed (idx ∘ φ) (fun i => t (φ i)) (fun i => p (φ i)) anchor
      (r ∘ φ) (fun i => htime (φ i)) (fun i => hsmall (φ i))
      (fun i => hvolWork (φ i)) (fun i => hguard (φ i))
      (htlim.comp hφ.tendsto_atTop) hanchorPrimary hanchorDist hfailurePrimary
    exact hout

end GC.LongTime.Ch11

end P6GuardScalarEscapeCXSP

section P6GuardNeckedRayCXSP

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 从原坏序列直接生产原归一化极限中的非负曲率、有限缺端 ray 与末端 spatial necks。 -/
theorem exists_guard_necked_missing_ray_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ε ≤ coneAccuracy →
      ∀ A : ℝ, 0 < A → ∀ Λ : ℝ, 1 ≤ Λ → ∃ Hbase : ℝ, 4 ≤ Hbase ∧
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, q.neckRadius (t i) ≤ Λ * r i) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      ∃ (rho : ℝ) (hrho : 0 < rho), rho + 2 ≤ A * Real.sqrt Hbase + 3 ∧
        ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
        let _ : EMetricSpace Pl.M := Pl.emetricSpace
        ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
          metricScalarAt Pl.metric Pl.basepoint = 1 ∧
          (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
            algebraicCurvatureOperatorNonnegativeCone) ∧
          (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
          (∀ R : ℝ, 0 ≤ R → R < rho →
            IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
          Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
          Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
            (cocompact Pl.M) ∧
          (∀ y : Pl.M, ¬ Tendsto ray
            (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
          Tendsto (fun v => metricScalarAt Pl.metric (ray v))
            (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
          ∀ᶠ v : Ico (0 : ℝ) rho in
              comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
            Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v)) := by
  obtain ⟨ε₀, hε₀, hguardEscape⟩ := exists_guard_scalar_escape_bdd_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb hε A hA Λ hΛ
  obtain ⟨Hbase, hHbase, hproduce⟩ :=
    hguardEscape S F q hTower hdiag hacc hrad hord hb A hA Λ hΛ
  have hHb : 0 < Hbase := by linarith only [hHbase]
  refine ⟨Hbase, hHbase, ?_⟩
  intro idx H t p x r htime hsmall hvol hx htlim hbad hguard hratio
  obtain ⟨N, hrest⟩ := hproduce idx t p x r htime hsmall hvol hx htlim hbad hguard
  let φ : ℕ → ℕ := fun i => i + N
  obtain ⟨hφ, anchor, Q, hQ, hscale, hanchorR, hanchorDist, _hOldSegments,
    _hOldDistance, _hOldBlow, rho, hrho, hrhoBound, ind, hind, z,
    f, hf, rad, hrad, hradlim, Pl, maps, M, hbaseR, hcanonical,
    hradial, hcompact, htarget, hmetric, hfinite, hdist, hhigh⟩ := hrest
  let stage := fun i => (H (φ (ind i))).stageAt (t (φ (ind i)))
  let metric := fun i => (H (φ (ind i))).stageMetric
    ((H (φ (ind i))).activeStage (t (φ (ind i)))) (t (φ (ind i)))
  let idx' : ℕ → ℕ := fun i => idx (φ (ind i))
  let t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).horizon :=
    fun i => t (φ (ind i))
  let p' : ∀ i, (stage i).Carrier := fun i => p (φ (ind i))
  let anchor' : ∀ i, (stage i).Carrier := fun i => anchor (ind i)
  let r' : ℕ → ℝ := fun i => r (φ (ind i))
  let Q' : ℕ → ℝ := fun i => Q (ind i)
  have hQ' (i : ℕ) : 0 < Q' i := hQ (ind i)
  let U := fun i => connectedComponentOpen (I := ThreeModel) (anchor' i)
  let hp := fun i => (mem_connectedComponent : anchor' i ∈ U i)
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun i =>
        { M := (stage i).Carrier
          basepoint := anchor' i
          metric := scaleMetric (Q' i) (hQ' i) (metric i) } }
  let maps0 := maps.liftTargetOpen (S := X) U hp
  have hscaleDiv (i : ℕ) : Q' i = Hbase / r' i ^ 2 := by
    simpa only [div_eq_mul_inv] using hscale (ind i)
  have hscaleMul (i : ℕ) : Q' i * r' i ^ 2 = Hbase :=
    (eq_div_iff (pow_ne_zero 2 (hsmall (φ (ind i))).1.ne')).mp (hscaleDiv i)
  have htime' (i : ℕ) : 2 * r' i ^ 2 < (t' i : ℝ) := htime (φ (ind i))
  have hsmall' (i : ℕ) : hasSmallParabolicCurvature
      (F.tower.history (idx' i)).toHistory (t' i) (p' i) (r' i) := hsmall (φ (ind i))
  have ht' (i : ℕ) : 0 < (t' i : ℝ) :=
    (mul_nonneg (by norm_num) (sq_nonneg (r' i))).trans_lt (htime' i)
  have hmono : StrictMono (fun i => φ (ind i)) := hφ.comp hind
  have htlim' : Tendsto (fun i => (t' i : ℝ)) atTop atTop := htlim.comp hmono.tendsto_atTop
  have hratio' : Tendsto (fun i => r' i / Real.sqrt (t' i : ℝ)) atTop (𝓝 0) :=
    hratio.comp hmono.tendsto_atTop
  have hnonnegative := curvatureOperator_nonnegative_of_prepared_stage_limit_CXSP
    S F hTower Hbase hHb idx' t' anchor' r' Q' ht' (fun i => (hsmall' i).1)
    hQ' hscaleDiv hratio' f hf Pl maps0 M hcanonical
  let Awork : ℝ := 4 * A + 4
  have hAwork : 0 < Awork := by dsimp only [Awork]; positivity
  have hAAwork : A ≤ Awork := by dsimp only [Awork]; linarith only [hA]
  have hvol' (i : ℕ) : ENNReal.ofReal (Awork⁻¹ * r' i ^ 3) ≤
      ballVolume (metric i) (p' i) (r' i) :=
    seed_volume_of_parameter_le_CXSP (hsmall' i) hA hAAwork (hvol (φ (ind i)))
  have hsqrt : 2 ≤ Real.sqrt Hbase := by
    nlinarith only [Real.sq_sqrt hHb.le, Real.sqrt_nonneg Hbase, hHbase]
  have hrhoDiv : (rho + 1) / Real.sqrt Hbase ≤ A + 1 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hHb)).mpr
    nlinarith only [hrhoBound, hsqrt]
  have hfit : A + (rho + 1) / Real.sqrt Hbase < Awork := by
    dsimp only [Awork]
    linarith only [hrhoDiv, hA]
  have hlower (eta : ℝ) (heta : 0 < eta) : ∀ᶠ n in atTop, ∀ y ∈ maps0.source n,
      ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * Pl.metric.inner y v v ≤
          (scaleMetric (Q' (f n)) (hQ' (f n)) (metric (f n))).inner (maps0.map n y)
            (mfderiv ThreeModel ThreeModel (maps0.map n) y v)
            (mfderiv ThreeModel ThreeModel (maps0.map n) y v) := by
    filter_upwards [hmetric eta heta] with n hn y hy v
    exact (hn y hy v).1
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  obtain ⟨ell, γ, _hellEq, helllim, hends, hmin, hsegment,
    ψ, ray, hψ, hray, hrayBase, hconv, _hstay, hscalar, hrayEscape, hmissing, hblow⟩ :=
    exists_stage_escape_scalar_ray_CXSP hb Awork hAwork idx' t' p' anchor' r'
      htime' hsmall' hvol' htlim' Hbase hHb Q' hQ' hscaleMul A hA.le
      (fun i => hanchorDist (ind i)) rho hrho hfit f hf Pl maps0 M hcanonical
      rad (fun n => (hrad n).1) hradlim htarget hlower hcompact hradial
      (fun n => z (f n)) hfinite hdist hhigh
  let maps1 := maps0.compSubseq ψ hψ
  have hcanonical1 (n : ℕ) : (M.compSubseq ψ hψ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps1 n := by
    change (M.domain (ψ n)).compSubseq ψ hψ n = _
    rw [hcanonical (ψ n)]
    rfl
  have hhighSegment : Tendsto (fun n =>
      metricScalarAt (metric (f n)) (γ n (ell n)) / Q' (f n)) atTop atTop := by
    convert hhigh using 1
    funext n
    rw [(hends n).2.1]
  have hnecks := eventually_stage_ray_necks_of_timeCore_CXSP hb hε
    Awork hAwork idx' t' p' anchor' r' htime' hsmall' hvol' htlim'
    Hbase hHb Q' hQ' hscaleMul (fun i => hanchorR (ind i)) rho hrho
    (f ∘ ψ) (hf.comp hψ) Pl maps1 (M.compSubseq ψ hψ) hcanonical1 hcompact
    (ell ∘ ψ) (fun n => γ (ψ n)) (helllim.comp hψ.tendsto_atTop)
    (fun n => (hends (ψ n)).1) (fun n => hmin (ψ n))
    (hψ.tendsto_atTop.eventually hsegment) (hhighSegment.comp hψ.tendsto_atTop) ray
    (fun v => (hconv {v} isCompact_singleton).tendsto_at (mem_singleton v)) hscalar hblow
  exact ⟨rho, hrho, hrhoBound, Pl, ray, hbaseR, hnonnegative, hradial, hcompact,
    hray, hrayBase, hrayEscape, hmissing, hblow, hnecks.2⟩

end GC.LongTime.Ch11

end P6GuardNeckedRayCXSP

section P6TimeSecondaryBallCXSP

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11
/-- TimeCore 与实际 chain 在精确 secondary 开球上生产共同 a、全部 traces，
以及独立于 L 的 secondary depth。 -/
theorem exists_prepared_time_secondary_ball_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ C : ℝ, 1 ≤ C → 2 * C2 ≤ C →
        ∃ θ : ℝ, 0 < θ ∧ θ = β0 / (2 * (C + 1)) ∧
        ∀ L : ℝ, L0 ≤ L → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (C * L + 1)) / Real.sqrt Q
        let β := β0 / (C * L + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (y : (H.stageAt t).Carrier) (dCenter : ℝ), 0 ≤ dCenter →
          dCenter + 1 / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let Rn := metricScalarAt (H.stageMetric (H.activeStage t) t) y
        Q * (L - 1) < Rn → Rn < Q * (L + 1) →
        let U := riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Real.sqrt Rn)⁻¹
        ∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) ∧ 1 ≤ Q * (a : ℝ) ∧
          H.time (H.activeStage a) < (t : ℝ) - θ / Rn ∧
          ∀ x ∈ U, ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) ∧
              metricScalarAt (H.stageMetric (H.activeStage v) v)
                (B.point (H.activeStage v) (H.activeStage_mono hav)
                  (H.activeStage_mono hvt)) ≤ 2 * ((C * L) * Q) := by
  obtain ⟨ε₀, hε₀, hpoint⟩ := exists_prepared_time_trace_window_of_ratio_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨Kcan, Tcan, _hKcan, hTcan, hcanonical⟩ := hb Afac (zero_lt_one.trans hA)
  obtain ⟨KG, TG, _hKG, _hTG, hGood⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans hA)
  obtain ⟨H0, hH0, hpointA⟩ := hpoint S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  have hHpos : 0 < H0 := by linarith
  let L0 : ℝ := max (max 3 (1 + Kcan / H0)) (1 + 10000 * KG / H0)
  have hL03 : 3 ≤ L0 := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨H0, L0, hH0, hL03, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, βold, hlam0, hβold, hpointM⟩ := hpointA d0 Δ γ hd0 hΔ hγ hbuffer
  let β0 : ℝ := min βold (min (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
  have hβ0 : 0 < β0 := by dsimp [β0]; positivity
  have hβoldle : β0 ≤ βold := min_le_left _ _
  have hβH : β0 ≤ H0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβtime : (Ctime : ℝ) * β0 ≤ 1 / 4 := by
    have h := (min_le_right βold _).trans
      (min_le_right (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * ((Ctime : ℝ) + 1))).mp h
    nlinarith only [hmul, hβ0]
  refine ⟨lam0, β0, hlam0, hβ0, ?_⟩
  intro C hC hC2
  let θ : ℝ := β0 / (2 * (C + 1))
  have hθpos : 0 < θ := div_pos hβ0 (by linarith)
  refine ⟨θ, hθpos, rfl, ?_⟩
  intro L hL
  have hL3 : 3 ≤ L := hL03.trans hL
  have hmL : L ≤ C * L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ L)
  have hm : 1 / 2 ≤ C * L := by linarith
  have hden : 0 < C * L + 1 := by linarith
  have hthreshold : Kcan ≤ H0 * (L - 1) := by
    have h := (le_max_right 3 (1 + Kcan / H0)).trans
      ((le_max_left _ _).trans hL)
    have hratio : Kcan / H0 ≤ L - 1 := by linarith
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  have hGoodCoef : 10000 * KG ≤ H0 * (C * L) := by
    have h := (le_max_right (max 3 (1 + Kcan / H0)) _).trans hL
    have hratio : 10000 * KG / H0 ≤ C * L := by linarith
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  obtain ⟨TS, _hTS, hpointN⟩ := hpointM (C * L) hm
  refine ⟨max (max Tcan (2 * TG)) TS,
    hTcan.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro n H t p r Q ell β ht htime hsmall hvol hguard aSeed haT hclock seedTrace
    y dCenter hdCenter hfit hcenter Rn hlower hupper U
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos hr))
  have hM : 0 < (C * L) * Q := mul_pos (by linarith) hQ
  have hradH : 0 < 1 / Real.sqrt H0 := one_div_pos.mpr (Real.sqrt_pos.mpr hHpos)
  have hcenterA : dCenter < Afac := by linarith only [hfit, hbuffer, hradH, hΔ, hγ]
  have hyA : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (Afac * r) := by
    apply hcenter.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (zero_lt_one.trans hA) hr)).mpr
    exact mul_lt_mul_of_pos_right hcenterA hr
  have hR : Kcan * (r ^ 2)⁻¹ ≤ Rn := by
    have hmul := mul_le_mul_of_nonneg_right hthreshold (inv_nonneg.mpr (sq_nonneg r))
    have hle : Kcan * (r ^ 2)⁻¹ ≤ Q * (L - 1) := by
      dsimp only [Q]
      nlinarith only [hmul]
    exact hle.trans hlower.le
  obtain ⟨W, _hchart⟩ := (hcanonical n t p r
    ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
    htime hsmall hvol y hyA hR).1
  have hyU : y ∈ U := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) y y < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos))
  have hscalar := (secondary_unit_ball_scalar_CXSP W hC hC2 hL3 hQ hupper).2
  have hdist := secondary_unit_ball_distance_CXSP
    (H.stageMetric (H.activeStage t) t) hHpos hr hL3 hlower hdCenter hfit hcenter
  have hpointX (x : (H.stageAt t).Carrier) (hx : x ∈ U) :=
    hpointN n t p r ((le_max_right _ _).trans ht) htime hsmall hvol hguard
      aSeed haT hclock seedTrace x (hscalar x hx) (hdist x hx)
  obtain ⟨aold, haoldSeed, _haoldt, haoldClock, _holdDepth, _hcenterTrace⟩ := hpointX y hyU
  have hβ : 0 < β := div_pos hβ0 hden
  have hβle : β ≤ βold / (C * L + 1) := div_le_div_of_nonneg_right hβoldle hden.le
  have hβH' : β ≤ H0 / 4 :=
    (div_le_self hβ0.le (by linarith : 1 ≤ C * L + 1)).trans hβH
  have htau : 0 < β / Q := div_pos hβ hQ
  have htauR : β / Q ≤ r ^ 2 / 4 := calc
    β / Q ≤ (H0 / 4) / Q := div_le_div_of_nonneg_right hβH' hQ.le
    _ = r ^ 2 / 4 := by dsimp only [Q]; field_simp [hHpos.ne', hr.ne']
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - β / Q,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r], (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have hclocks (a' : Icc (0 : ℝ) H.horizon)
      (ha' : (a' : ℝ) = (t : ℝ) - (βold / (C * L + 1)) / Q) : a' ≤ a := by
    change (a' : ℝ) ≤ (t : ℝ) - β / Q
    rw [ha']
    exact sub_le_sub_left (div_le_div_of_nonneg_right hβle hQ.le) _
  have haa : aSeed ≤ a := haoldSeed.trans (hclocks aold haoldClock)
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - β / Q
    nlinarith only [htauR, sq_nonneg r]
  have haClock : (a : ℝ) = (t : ℝ) - β / Q := rfl
  have hdepth : Q * ((t : ℝ) - a) = β := by
    change Q * ((t : ℝ) - ((t : ℝ) - β / Q)) = β
    rw [sub_sub_cancel, mul_div_cancel₀ _ hQ.ne']
  have hQa : 1 ≤ Q * (a : ℝ) := by
    have hra : r ^ 2 ≤ (a : ℝ) := by
      rw [haClock]
      nlinarith only [htime, htauR, sq_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left hra hQ.le
    have hQr : Q * r ^ 2 = H0 := by dsimp only [Q]; field_simp [hr.ne']
    rw [hQr] at hmul
    linarith only [hmul, hH0]
  have hratio : L - 1 < Rn / Q := by
    apply (lt_div_iff₀ hQ).mpr
    simpa only [mul_comm] using hlower
  have hθdepth : θ / Rn < β / Q :=
    (secondary_depth_lt_uniform_window_CXSP hC hL3 hQ hratio hβ0).2
  have hstart : H.time (H.activeStage a) ≤ (t : ℝ) - β / Q :=
    (H.activeStage_time_le a).trans_eq haClock
  have hbudget : Ctime * ((C * L) * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    have heq : (C * L + 1) * β = β0 := mul_div_cancel₀ _ hden.ne'
    have hmb : C * L * β ≤ β0 := by nlinarith only [heq, hβ]
    have htb := (mul_le_mul_of_nonneg_left hmb Ctime.coe_nonneg).trans hβtime
    have hc : Ctime * ((C * L) * Q) * ((t : ℝ) - a) = Ctime * (C * L * β) := by
      rw [haClock, sub_sub_cancel]
      field_simp [hQ.ne']
    rw [hc]
    linarith only [htb]
  have hGoodThreshold : (10000 * KG) * (r ^ 2)⁻¹ ≤ (C * L) * Q := by
    have hmul := mul_le_mul_of_nonneg_right hGoodCoef (inv_nonneg.mpr (sq_nonneg r))
    dsimp only [Q]
    nlinarith only [hmul]
  refine ⟨a, haa, hat, haClock, hdepth, hhalf, hQa,
    hstart.trans_lt (sub_lt_sub_left hθdepth t), ?_⟩
  intro x hx
  obtain ⟨ax, _haxSeed, _haxt, hxClock, _hxDepth, Bold, hBold⟩ := hpointX x hx
  have haxa : ax ≤ a := hclocks ax hxClock
  let B := Bold.restrictFirst (H.activeStage_mono haxa) (H.activeStage_mono hat)
  let AA := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
  have hdistance (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      AA.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
      AA.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        AA.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) :=
    hBold v (haxa.trans hav) hvt
  have hcontrol := B.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v hav hvt hage htop hRv => by
      have hfoot : B.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt) ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haa.trans hav))
            (H.activeStage_mono hvt)) (Afac * r) :=
        (hdistance v hav hvt).1.trans_le (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (by linarith : d0 + Δ ≤ Afac) hr.le))
      have hGoodV := hGood n t p r
        ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
        htime hsmall hvol aSeed haT hclock seedTrace v (haa.trans hav) hvt
        (hhalf.trans (show (a : ℝ) ≤ v from hav)) _ hfoot
        (hGoodThreshold.trans_lt hRv).le
      exact hGoodV.2 hage htop) (hscalar x hx) hbudget
  exact ⟨B, fun v hav hvt =>
    ⟨(hdistance v hav hvt).1, (hdistance v hav hvt).2, hcontrol v hav hvt⟩⟩

end GC.LongTime.Ch11

end P6TimeSecondaryBallCXSP

section P6TimeTracedRegionCXSP

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

/-- 原 history 上的实际有界曲率 traced region；不是目标 Good/Dt 的 conditional wrapper。 -/
theorem exists_prepared_time_traced_region_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, 0 < θ ∧ 0 < K0 ∧
        ∀ L : ℝ, L0 ≤ L → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (y : (H.stageAt t).Carrier) (dCenter : ℝ), 0 ≤ dCenter →
          dCenter + 1 / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let Rn := metricScalarAt (H.stageMetric (H.activeStage t) t) y
        Q * (L - 1) < Rn → Rn < Q * (L + 1) →
        H.isTracedRegion t y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) := by
  obtain ⟨ε₀, hε₀, hsecondary⟩ := exists_prepared_time_secondary_ball_bdd_C11SP P g
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨params, records, _hmodelR, _hmodelO, _hmodelA, _hparams, _hcan, _hOld,
    _hdecay, _hrecent⟩ := exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  obtain ⟨H0, L0, hH0, hL0, hsecondaryA⟩ :=
    hsecondary S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, β0, _hlam0, hβ0, hsecondaryC⟩ :=
    hsecondaryA d0 Δ γ hd0 hΔ hγ hbuffer
  let C : ℝ := max 1 (2 * C2)
  have hC : 1 ≤ C := le_max_left _ _
  have hC2 : 2 * C2 ≤ C := le_max_right _ _
  obtain ⟨θ, hθ, hθeq, hsecondaryL⟩ := hsecondaryC C hC hC2
  let K0 : ℝ := 2 * Real.sqrt 3 * ((4 * C) / 2 + max (4 * C) (2 * Real.exp 4))
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  refine ⟨θ, K0, hθ, hK0, ?_⟩
  intro L hL
  obtain ⟨T₀, hT₀, hsecondaryN⟩ := hsecondaryL L hL
  refine ⟨T₀, hT₀, ?_⟩
  intro n H t p r Q ht htime hsmall hvol hguard y dCenter hdCenter hfit hcenter
    Rn hlower hupper
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos (by linarith) (inv_pos.mpr (sq_pos_of_pos hr))
  have hL3 : 3 ≤ L := hL0.trans hL
  have hRn : 0 < Rn := (mul_pos hQ (by linarith)).trans hlower
  have hQR : Q ≤ Rn := by nlinarith
  have hsmallCopy := hsmall
  obtain ⟨_hr, aSeed, haT, hclock, hseed⟩ := hsmallCopy
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨seedTrace, _hcontrolled⟩ := hseed p hp
  obtain ⟨a, haa, hat, haClock, _hdepth, _hhalf, hQa, _hstart, htraces⟩ :=
    hsecondaryN n t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace
      y dCenter hdCenter hfit hcenter hlower hupper
  have hratio : L - 1 < Rn / Q := by
    apply (lt_div_iff₀ hQ).mpr
    simpa only [mul_comm] using hlower
  have hdepth : θ / Rn < (β0 / (C * L + 1)) / Q := by
    rw [hθeq]
    exact (secondary_depth_lt_uniform_window_CXSP hC hL3 hQ hratio hβ0).2
  have habound : (a : ℝ) ≤ (t : ℝ) - θ / Rn := by
    rw [haClock]
    exact (sub_lt_sub_left hdepth _).le
  have hbt : (t : ℝ) - θ / Rn ≤ (t : ℝ) := sub_le_self _ (div_pos hθ hRn).le
  let b : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - θ / Rn,
    a.2.1.trans habound, hbt.trans t.2.2⟩
  have hab : a ≤ b := habound
  have hbt' : b ≤ t := hbt
  have hRnb : 1 ≤ Rn * (b : ℝ) :=
    hQa.trans ((mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ b from hab) hQ.le).trans
      (mul_le_mul_of_nonneg_right hQR b.2.1))
  have hscalarCompare : 2 * ((C * L) * Q) ≤ (4 * C) * Rn := by
    have hLQ : L * Q ≤ 2 * Rn := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hLQ (by positivity : 0 ≤ 2 * C)
    nlinarith only [hmul]
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr hRn), div_pos hθ hRn, b, hbt', rfl, ?_⟩
  intro x hx
  obtain ⟨B, hB⟩ := htraces x hx
  let B' := B.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt')
  refine ⟨B', ?_⟩
  exact B'.isRmBoundedBy_of_scalar_and_HI_CXSP ha₀.le hRn (by positivity) hRnb
    (fun v z => hHI F n (records n) v z)
    (fun v hbv hvt => ((hB v (hab.trans hbv) hvt).2.2).trans hscalarCompare)

end GC.LongTime.Ch11

end P6TimeTracedRegionCXSP

section P6TracedSecondaryJetsCXSP

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

/-- 原 history 的 traced unit ball 给物理半球及其 normalized metric 的统一 jets。 -/
theorem exists_secondary_jets_of_traced_region_bdd_C11SP
    (θ K0 : ℝ) (hθ : 0 < θ) (hK0 : 0 < K0) :
    ∃ J : ℕ → ℝ, (∀ m, 1 ≤ J m) ∧
      ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
        (y : (H.stageAt t).Carrier) (Rn : ℝ) (hRn : 0 < Rn),
        H.isTracedRegion t y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) →
        ∀ m : ℕ, ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y
          (1 / (2 * Real.sqrt Rn)),
          curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
              J m * Real.sqrt Rn ^ (m + 2) ∧
            curvDerivNorm m
              (scaleMetric Rn hRn (H.stageMetric (H.activeStage t) t)) z ≤ J m := by
  let D : ℕ → ℝ := fun m =>
    shiLocalUniformBound 3 m ((K0 / 4) * (4 * θ) / 2)
        (Real.sqrt (K0 / 4) /
          (8 * Real.exp ((3 : ℝ) ^ 2 * ((K0 / 4) * (4 * θ) / 2)))) *
      (K0 / 4) / Real.sqrt ((4 * θ) / 2) ^ m
  let J : ℕ → ℝ := fun m => max 1 (D m * 2 ^ (m + 2))
  refine ⟨J, fun m => le_max_left _ _, ?_⟩
  intro H t y Rn hRn htraced m z hz
  have hsqrt : 0 < Real.sqrt Rn := Real.sqrt_pos.mpr hRn
  let s := 1 / (2 * Real.sqrt Rn)
  have hs : 0 < s := by dsimp only [s]; positivity
  have hs2 : s ^ 2 = 1 / (4 * Rn) := by
    dsimp only [s]
    rw [div_pow, mul_pow, Real.sq_sqrt hRn.le]
    norm_num
  have hradius : 2 * s = (Real.sqrt Rn)⁻¹ := by
    dsimp only [s]
    field_simp [hsqrt.ne']
  have hdepth : (4 * θ) * s ^ 2 = θ / Rn := by
    rw [hs2]
    field_simp [hRn.ne']
  have hcurvature : (K0 / 4) / s ^ 2 = K0 * Rn := by
    rw [hs2]
    field_simp [hRn.ne']
  have htr : H.isTracedRegion t y (2 * s) ((4 * θ) * s ^ 2)
      ((K0 / 4) / s ^ 2) := by
    rwa [hradius, hdepth, hcurvature]
  have hb := FILL910.A11b_shi_whole_ball_of_isTracedRegion H t y
    (by positivity : 0 < 4 * θ) hs (by positivity : 0 < K0 / 4) htr m z hz
  change curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
    D m / s ^ (m + 2) at hb
  have hrescale : D m / s ^ (m + 2) =
      (D m * 2 ^ (m + 2)) * Real.sqrt Rn ^ (m + 2) := by
    dsimp only [s]
    rw [one_div, inv_pow, div_inv_eq_mul, mul_pow]
    ring
  rw [hrescale] at hb
  have hphysical : curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
      J m * Real.sqrt Rn ^ (m + 2) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg hsqrt.le _))
  refine ⟨hphysical, ?_⟩
  rw [curvDerivNorm_scaleMetric]
  apply (div_le_iff₀ (mul_pos hRn (pow_pos hsqrt m))).mpr
  calc
    curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
        J m * Real.sqrt Rn ^ (m + 2) := hphysical
    _ = J m * (Rn * Real.sqrt Rn ^ m) := by
      rw [pow_add, Real.sq_sqrt hRn.le]
      ring

/-- 从新 TimeCore 与实际 chain 直接生产 normalized secondary jets；J 先于 L。 -/
theorem exists_prepared_time_secondary_jets_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, ∃ J : ℕ → ℝ, 0 < θ ∧ 0 < K0 ∧ (∀ m, 1 ≤ J m) ∧
        ∀ L : ℝ, L0 ≤ L → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (y : (H.stageAt t).Carrier) (dCenter : ℝ), 0 ≤ dCenter →
          dCenter + 1 / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let Rn := metricScalarAt (H.stageMetric (H.activeStage t) t) y
        Q * (L - 1) < Rn → Rn < Q * (L + 1) →
        H.isTracedRegion t y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) ∧
          ∀ (hRn : 0 < Rn) (m : ℕ),
          ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y
            (1 / (2 * Real.sqrt Rn)),
            curvDerivNorm m
              (scaleMetric Rn hRn (H.stageMetric (H.activeStage t) t)) z ≤ J m := by
  obtain ⟨ε₀, hε₀, htraced⟩ := exists_prepared_time_traced_region_bdd_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨H0, L0, hH0, hL0, htracedA⟩ :=
    htraced S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨θ, K0, hθ, hK0, htracedL⟩ := htracedA d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨J, hJpos, hJ⟩ := exists_secondary_jets_of_traced_region_bdd_C11SP θ K0 hθ hK0
  refine ⟨θ, K0, J, hθ, hK0, hJpos, ?_⟩
  intro L hL
  obtain ⟨T₀, hT₀, htracedN⟩ := htracedL L hL
  refine ⟨T₀, hT₀, ?_⟩
  intro n H t p r Q ht htime hsmall hvol hguard y dCenter hdCenter hfit hcenter
    Rn hlower hupper
  have htr := htracedN n t p r ht htime hsmall hvol hguard
    y dCenter hdCenter hfit hcenter hlower hupper
  exact ⟨htr, fun hRn m z hz => (hJ H t y Rn hRn htr m z hz).2⟩

end GC.LongTime.Ch11

end P6TracedSecondaryJetsCXSP

section P6TimeMappedJetsCXSP

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 固定高 level 的 limit 点产生原 history 的 traced region 与 normalized jets。 -/
theorem exists_prepared_time_mapped_jets_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, ∃ J : ℕ → ℝ, 0 < θ ∧ 0 < K0 ∧ (∀ m, 1 ≤ J m) ∧
        ∀ χ : ℝ, 0 < χ → ∀ rho dAnchor : ℝ, 0 < rho → 0 ≤ dAnchor →
          dAnchor + rho / Real.sqrt (χ * H0) + 1 / Real.sqrt H0 ≤ d0 →
        ∀ idx : ℕ → ℕ,
        let H := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 0 < r i) → Tendsto (fun i => (t i : ℝ)) atTop atTop →
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (Afac⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, q.neckRadius (t i) ≤ Λ * r i) →
        ∀ anchor : ∀ i, ((H i).stageAt (t i)).Carrier,
          (∀ i, riemannianEDistOf ((H i).stageMetric ((H i).activeStage (t i)) (t i))
            (p i) (anchor i) ≤ ENNReal.ofReal (dAnchor * r i)) →
        ∀ (Qbase : ℕ → ℝ) (hQbase : ∀ i, 0 < Qbase i),
          (∀ i, Qbase i = (χ * H0) * (r i ^ 2)⁻¹) →
        let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := ((H i).stageAt (t i)).Carrier
                basepoint := anchor i
                metric := scaleMetric (Qbase i) (hQbase i)
                  ((H i).stageMetric ((H i).activeStage (t i)) (t i)) } }
        ∀ (f : ℕ → ℕ), StrictMono f →
        ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (Phi : PointedRiemannianConvergenceMaps X Pl f) (M : MetricConvergenceData Phi),
          (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) →
        ∀ z : Pl.M,
          riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho →
          L0 ≤ χ * metricScalarAt Pl.metric z →
        ∀ᶠ n in atTop,
          let Hn := H (f n)
          let tn := t (f n)
          let y := Phi.map n z
          let Rn := metricScalarAt (Hn.stageMetric (Hn.activeStage tn) tn) y
          0 < Rn ∧ Hn.isTracedRegion tn y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) ∧
            ∀ (hRn : 0 < Rn) (m : ℕ),
            ∀ w ∈ riemannianBallOf (Hn.stageMetric (Hn.activeStage tn) tn) y
              (1 / (2 * Real.sqrt Rn)),
              curvDerivNorm m
                (scaleMetric Rn hRn (Hn.stageMetric (Hn.activeStage tn) tn)) w ≤ J m := by
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_prepared_time_secondary_jets_bdd_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨H0, L0, hH0, hL0, hmainA⟩ :=
    hmain S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨θ, K0, J, hθ, hK0, hJ, hmainL⟩ := hmainA d0 Δ γ hd0 hΔ hγ hbuffer
  refine ⟨θ, K0, J, hθ, hK0, hJ, ?_⟩
  intro χ hχ rho dAnchor hrho hdAnchor hfit idx H t p r hr htendsto htime hsmall
    hvol hguard anchor hanchor Qbase hQbase hscale X f hf Pl Phi M hcanonical z hz hlevel
  have hHpos : 0 < H0 := by linarith only [hH0]
  let Ps := fun i => (H i).stageAt (t i)
  let gs : ∀ i, (Ps i).Metric :=
    fun i => (H i).stageMetric ((H i).activeStage (t i)) (t i)
  let L : ℝ := χ * metricScalarAt Pl.metric z
  have hL : L0 ≤ L := hlevel
  have hL3 : 3 ≤ L := hL0.trans hL
  obtain ⟨T₀, _hT₀, hmainN⟩ := hmainL L hL
  have hdist := eventually_stage_pointed_seed_distance_CXSP
    (P := Ps) (g := gs) (Qbase := Qbase) (hQbase := hQbase)
    (anchor := anchor) (f := f) (Pl := Pl) (F := Phi)
    (M := M) (hcanonical := hcanonical) (p := p) (r := r) (hr := hr)
    (Hbase := χ * H0) (dAnchor := dAnchor) (rho := rho)
    (hHbase := mul_pos hχ hHpos) (hdAnchor := hdAnchor)
    (hscale := hscale) (hanchor := hanchor) (z := z) (hz := hz)
  have hband := eventually_stage_pointed_auxiliary_scalar_band_CXSP
    (P := Ps) (g := gs) (Qbase := Qbase) (hQbase := hQbase)
    (anchor := anchor) (f := f) (Pl := Pl) (F := Phi)
    (M := M) (hcanonical := hcanonical) (χ := χ) (hχ := hχ) (z := z)
  have htSub : Tendsto (fun n => (t (f n) : ℝ)) atTop atTop :=
    htendsto.comp hf.tendsto_atTop
  have hdCenter : 0 ≤ dAnchor + rho / Real.sqrt (χ * H0) :=
    add_nonneg hdAnchor (div_nonneg hrho.le (Real.sqrt_nonneg _))
  filter_upwards [hdist, hband, htSub.eventually_ge_atTop T₀] with n hdn hbn htn
  change (Qbase (f n) / χ) * (L - 1) < metricScalarAt (gs (f n)) (Phi.map n z) ∧
    metricScalarAt (gs (f n)) (Phi.map n z) < (Qbase (f n) / χ) * (L + 1) at hbn
  have haux : Qbase (f n) / χ = H0 * (r (f n) ^ 2)⁻¹ := by
    rw [hscale (f n)]
    field_simp [hχ.ne', (hr (f n)).ne']
  rw [haux] at hbn
  have hQ : 0 < H0 * (r (f n) ^ 2)⁻¹ :=
    mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos (hr (f n))))
  have hRn : 0 < metricScalarAt (gs (f n)) (Phi.map n z) :=
    (mul_pos hQ (by linarith only [hL3] : 0 < L - 1)).trans hbn.1
  refine ⟨hRn, ?_⟩
  exact hmainN (idx (f n)) (t (f n)) (p (f n)) (r (f n)) htn
    (htime (f n)) (hsmall (f n)) (hvol (f n)) (hguard (f n))
    (Phi.map n z) (dAnchor + rho / Real.sqrt (χ * H0)) hdCenter hfit hdn hbn.1 hbn.2

end GC.LongTime.Ch11

end P6TimeMappedJetsCXSP

section P6TriangularMappedJetsCXSP

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- exists_strictMono_ge 的前缀 sup 构造同时支配先前各项的 eventual threshold。 -/
private theorem exists_triangular_subsequence_bdd_C11SP (Paid : ℕ → ℕ → Prop)
    (hPaid : ∀ m, ∀ᶠ n in atTop, Paid m n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n m : ℕ, m ≤ n → Paid m (ψ n) := by
  classical
  choose N hN using fun m => eventually_atTop.mp (hPaid m)
  obtain ⟨ψ, hψ, hψN⟩ := exists_strictMono_ge N
  refine ⟨ψ, hψ, ?_⟩
  intro n m hmn
  exact hN m (ψ n) ((hψN m).trans (hψ.monotone hmn))

/-- 同一真实 first-level maps 上的三角形付款；最后一项是任意严格后续子列的实际 consumer。 -/
theorem exists_prepared_time_triangular_mapped_jets_bdd_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, ∃ J : ℕ → ℝ, 0 < θ ∧ 0 < K0 ∧ (∀ m, 1 ≤ J m) ∧
        ∀ χ : ℝ, 0 < χ → ∀ rho dAnchor : ℝ, 0 < rho → 0 ≤ dAnchor →
          dAnchor + rho / Real.sqrt (χ * H0) + 1 / Real.sqrt H0 ≤ d0 →
        ∀ idx : ℕ → ℕ,
        let H := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 0 < r i) → Tendsto (fun i => (t i : ℝ)) atTop atTop →
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (Afac⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, q.neckRadius (t i) ≤ Λ * r i) →
        ∀ anchor : ∀ i, ((H i).stageAt (t i)).Carrier,
          (∀ i, riemannianEDistOf ((H i).stageMetric ((H i).activeStage (t i)) (t i))
            (p i) (anchor i) ≤ ENNReal.ofReal (dAnchor * r i)) →
        ∀ (Qbase : ℕ → ℝ) (hQbase : ∀ i, 0 < Qbase i),
          (∀ i, Qbase i = (χ * H0) * (r i ^ 2)⁻¹) →
        let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
          { obj := fun i =>
              { M := ((H i).stageAt (t i)).Carrier
                basepoint := anchor i
                metric := scaleMetric (Qbase i) (hQbase i)
                  ((H i).stageMetric ((H i).activeStage (t i)) (t i)) } }
        ∀ (f : ℕ → ℕ), StrictMono f →
        ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (Phi : PointedRiemannianConvergenceMaps X Pl f) (M : MetricConvergenceData Phi),
          (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) →
        ∀ z : ℕ → Pl.M,
          (∀ m, riemannianEDistOf Pl.metric Pl.basepoint (z m) < ENNReal.ofReal rho) →
          (∀ m, L0 ≤ χ * metricScalarAt Pl.metric (z m)) →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          (∀ n m : ℕ, m ≤ n →
            let Hn := H (f (ψ n))
            let tn := t (f (ψ n))
            let y := Phi.map (ψ n) (z m)
            let Rn := metricScalarAt (Hn.stageMetric (Hn.activeStage tn) tn) y
            0 < Rn ∧ Hn.isTracedRegion tn y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) ∧
              ∀ (hRn : 0 < Rn) (j : ℕ),
              ∀ w ∈ riemannianBallOf (Hn.stageMetric (Hn.activeStage tn) tn) y
                (1 / (2 * Real.sqrt Rn)),
                curvDerivNorm j
                  (scaleMetric Rn hRn (Hn.stageMetric (Hn.activeStage tn) tn)) w ≤ J j) ∧
          ∀ k : ℕ → ℕ, StrictMono k → ∀ m : ℕ,
            let Hm := H (f (ψ (k m)))
            let tm := t (f (ψ (k m)))
            let y := Phi.map (ψ (k m)) (z m)
            let Rm := metricScalarAt (Hm.stageMetric (Hm.activeStage tm) tm) y
            0 < Rm ∧ Hm.isTracedRegion tm y (Real.sqrt Rm)⁻¹ (θ / Rm) (K0 * Rm) ∧
              ∀ (hRm : 0 < Rm) (j : ℕ),
              ∀ w ∈ riemannianBallOf (Hm.stageMetric (Hm.activeStage tm) tm) y
                (1 / (2 * Real.sqrt Rm)),
                curvDerivNorm j
                  (scaleMetric Rm hRm (Hm.stageMetric (Hm.activeStage tm) tm)) w ≤ J j := by
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_prepared_time_mapped_jets_bdd_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨H0, L0, hH0, hL0, hmainA⟩ :=
    hmain S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨θ, K0, J, hθ, hK0, hJ, hpoint⟩ := hmainA d0 Δ γ hd0 hΔ hγ hbuffer
  refine ⟨θ, K0, J, hθ, hK0, hJ, ?_⟩
  intro χ hχ rho dAnchor hrho hdAnchor hfit idx H t p r hr htlim htime hsmall
    hvol hguard anchor hanchor Qbase hQbase hscale X f hf Pl Phi M hcanonical z hz hlevel
  have hpaid := fun m => hpoint χ hχ rho dAnchor hrho hdAnchor hfit idx t p r hr htlim
    htime hsmall hvol hguard anchor hanchor Qbase hQbase hscale
    f hf Pl Phi M hcanonical (z m) (hz m) (hlevel m)
  obtain ⟨ψ, hψ, htriangle⟩ := exists_triangular_subsequence_bdd_C11SP _ hpaid
  refine ⟨ψ, hψ, htriangle, ?_⟩
  intro k hk m
  exact htriangle (k m) m (hk.id_le m)

end GC.LongTime.Ch11

end P6TriangularMappedJetsCXSP
