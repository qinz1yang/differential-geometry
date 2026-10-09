import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeJetsAliveC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeJetsV2C11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeTimeEscapeC11SP

set_option autoImplicit false

/-!
# NJ（G48 槽形）⇐ hSL1 rev2 ∧ hBorn（O-CH11-NATIVE-NJ G2b rev2，后缀 `_C11SP`）

`native_NJslot_of_SL1_v2_C11SP`（PROVISIONAL[hSL1 rev2, hBorn]）：
G2 `native_scalarEscape_of_NJ_C11SP` 的 binder
`hNJ` 逐字 ⇐ G1 rev2 `native_boundedBall_of_SL1_v2_C11SP`（逐点 alive/born 二分）+ G1b
`innerJets_or_born_of_dichotomy_C11SP`（alive patch jets）+ binder `hBorn`（born patch jets，= SL2-c）。
证明 = G48 原 escape 步 jets 块逐行，G46 换成 G1，最后按 patch 二分取 `max J_alive J_born`。
`hBorn`：chain 语境（records 同 G1），对固定 `R < Rwide, θ, K, c` 与阶 k 给一致的 `J, T`；前提为
patch 球 `B(y, Rwide/√Q)` 上逐点 alive（从 `a = t − θ/Q`，Rm ≤ KQ）或 born（`a < u`、Rm ≤ KQ、起点在
`neck.scale ≤ cQ` 的 cap 内窗）且至少一个 born 点；结论为 `B_Q(y, R)` 上 k 阶 jets ≤ J。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **G2b rev2（PROVISIONAL[hSL1 rev2, hBorn]）**：NJ 的 G48 槽形 ⇐ hSL1 rev2 ∧ hBorn。 -/
theorem native_NJslot_of_SL1_v2_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q))
    (hBorn :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac →
      ∃ (Haux : ℝ) (hHaux : 4 ≤ Haux),
        ∀ d0 Δ gamma : ℝ, 0 ≤ d0 → 0 < Δ → 0 < gamma → d0 + Δ + gamma ≤ Afac →
        ∀ chi : ℝ, ∀ hchi : 1 ≤ chi,
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
          (∀ i, r i < q.neckRadius (time i)) →
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
        ∀ R Rwide : ℝ, 0 < R → R < Rwide → Rwide ≤ Rad →
        ∀ B : ℝ, (∀ᶠ i in atTop, ∀ z : (stage i).Carrier,
            riemannianEDistOf (Xall.obj i).metric (anchor i) z < ENNReal.ofReal Rwide →
            metricScalarAt (metric i) z / Qbase i ≤ B) →
        ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
          ∀ᶠ i in atTop, HasLocalCurvDerivBound (Xall.obj i) (Xall.obj i).basepoint R k J := by
  obtain ⟨ε₁, hε₁, hG1⟩ := native_boundedBall_of_SL1_v2_C11SP P g hSL1
  obtain ⟨ε₂, hε₂, hB2⟩ := hBorn
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨params, records, hmR, hmO, hmA, hpar, hcanW, hold, hdel, hrec⟩ :=
    exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  obtain ⟨H0, m0, hH0, _hm0, hG1A⟩ := hG1 S F q hTower hdiag (hacc.trans (min_le_left _ _))
    hrad hord hb params records hmR hmO hmA hpar hcanW hold hdel hrec Afac hA
  refine ⟨H0, hH0, ?_⟩
  intro d0 Δ gamma hd0 hΔ hgamma hbuffer
  obtain ⟨β0, hβ0, hG1M⟩ := hG1A d0 Δ gamma hd0 hΔ hgamma hbuffer
  intro chi hchi Rad dAnchor hdAnchor hfit idx H time p anchor r htime hsmall hvol hnat htlim
    stage metric Qbase hQbase Xall _hanchorR hanchorDist R Rwide hR hRRwide hRwRad B hB k
  have hchip : 0 < chi := zero_lt_one.trans_le hchi
  have hHpos : 0 < H0 := by linarith only [hH0]
  have hr (i : ℕ) : 0 < r i := (hsmall i).1
  have hRwide : 0 < Rwide := hR.trans hRRwide
  let m : ℝ := max m0 (max 1 (B * chi))
  have hmm0 : m0 ≤ m := le_max_left _ _
  have hm1 : 1 ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmp : 0 < m := zero_lt_one.trans_le hm1
  have hBm : B * chi ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hden : 0 < m + 1 := by linarith only [hm1]
  let RadAux : ℝ := Rwide / Real.sqrt chi
  have hRadAux : 0 < RadAux := div_pos hRwide (Real.sqrt_pos.mpr hchip)
  have hradEq : ∀ {Q' : ℝ}, 0 < Q' → RadAux / Real.sqrt Q' = Rwide / Real.sqrt (chi * Q') := by
    intro Q' hQ'
    change (Rwide / Real.sqrt chi) / Real.sqrt Q' = _
    rw [Real.sqrt_mul hchip.le]
    field_simp [(Real.sqrt_pos.mpr hchip).ne', (Real.sqrt_pos.mpr hQ').ne']
  have hfitAux : dAnchor + RadAux / Real.sqrt H0 ≤ d0 := by
    have hfitR : Rwide / Real.sqrt (chi * H0) ≤ Rad / Real.sqrt (chi * H0) :=
      div_le_div_of_nonneg_right hRwRad (Real.sqrt_nonneg _)
    rw [hradEq hHpos]
    linarith only [hfitR, hfit]
  let Km : ℝ := 2 * Real.sqrt 3 * ((2 * m) / 2 + max (2 * m) (2 * Real.exp 4))
  have hKm : 0 < Km := by dsimp only [Km]; positivity
  let theta : ℝ := chi * (β0 / (m + 1))
  let Kprim : ℝ := Km / chi
  have htheta : 0 < theta := mul_pos hchip (div_pos hβ0 hden)
  have hKprim : 0 < Kprim := div_pos hKm hchip
  let cB : ℝ := 4 * m / chi
  have hcB : 0 < cB := div_pos (by linarith only [hmp]) hchip
  obtain ⟨Tm, _hTm, hG1N⟩ := hG1M m hmm0
  obtain ⟨J1, hJ1, hmain⟩ := innerJets_or_born_of_dichotomy_C11SP R Rwide theta Kprim hR.le
    hRRwide htheta hKprim
  obtain ⟨J2, T2, hJ2, hB2N⟩ := hB2 S F q hTower hdiag (hacc.trans (min_le_right _ _)) hrad hord
    hb params records hmR hmO hmA hpar hcanW hold hdel hrec R Rwide theta Kprim cB hR hRRwide
    htheta hKprim hcB k
  refine ⟨max (J1 k) J2, (zero_le_one.trans (hJ1 k)).trans (le_max_left _ _), ?_⟩
  filter_upwards [hB, htlim.eventually_ge_atTop (max Tm T2)] with i hi hti
  let Qaux : ℝ := H0 * (r i ^ 2)⁻¹
  have hQaux : 0 < Qaux := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos (hr i)))
  have hprimary : Qbase i = chi * Qaux := rfl
  have hradius : RadAux / Real.sqrt Qaux = Rwide / Real.sqrt (Qbase i) := by
    rw [hprimary]
    exact hradEq hQaux
  have hterminal : ∀ w ∈ riemannianBallOf (metric i) (anchor i)
      (RadAux / Real.sqrt Qaux), metricScalarAt (metric i) w ≤ m * Qaux := by
    intro w hw
    have hwN : w ∈ riemannianBallOf (scaleMetric (Qbase i) (hQbase i) (metric i))
        (anchor i) Rwide := by
      have h := riemannianBallOf_scaleMetric (Qbase i) (hQbase i) (metric i) (anchor i)
        (Rwide / Real.sqrt (Qbase i))
      rw [mul_div_cancel₀ Rwide (Real.sqrt_pos.mpr (hQbase i)).ne'] at h
      rw [h, ← hradius]
      exact hw
    have hRz : metricScalarAt (metric i) w ≤ B * Qbase i :=
      (div_le_iff₀ (hQbase i)).mp (hi w hwN)
    refine hRz.trans ?_
    rw [hprimary]
    calc B * (chi * Qaux) = (B * chi) * Qaux := by ring
         _ ≤ m * Qaux := mul_le_mul_of_nonneg_right hBm hQaux.le
  obtain ⟨_hradpos, _htaupos, a, hat, ha, hdich⟩ := hG1N (idx i) (time i) (p i) (r i)
    ((le_max_left _ _).trans hti) (htime i) (hsmall i) (hvol i) (hnat i) (anchor i) RadAux
    dAnchor hRadAux hdAnchor hfitAux (hanchorDist i) hterminal
  have hKeq : Km * Qaux = Kprim * Qbase i := by
    rw [hprimary]
    change Km * Qaux = Km / chi * (chi * Qaux)
    field_simp [hchip.ne']
  have hceq : 4 * (m * Qaux) = cB * Qbase i := by
    rw [hprimary]
    change 4 * (m * Qaux) = 4 * m / chi * (chi * Qaux)
    field_simp [hchip.ne']
  have ha' : (a : ℝ) = (time i : ℝ) - theta / Qbase i := by
    rw [ha, hprimary]
    congr 1
    change β0 / (m + 1) / Qaux = chi * (β0 / (m + 1)) / (chi * Qaux)
    field_simp [hchip.ne', hQaux.ne']
  have hdich' : ∀ x ∈ riemannianBallOf (metric i) (anchor i) (Rwide / Real.sqrt (Qbase i)),
      (∃ Bt : BackwardPointTrace (H i) ((H i).activeStage a) ((H i).activeStage (time i))
          ((H i).activeStage_mono hat) x, Bt.isRmBoundedBy (hat := hat) (Kprim * Qbase i)) ∨
        ∃ (u : Icc (0 : ℝ) (H i).horizon) (hut : u ≤ time i), a < u ∧
          ∃ e : Fin (H i).eventCount, (H i).time e.succ = (u : ℝ) ∧
            e.succ = (H i).activeStage u ∧
          ∃ Bt : BackwardPointTrace (H i) ((H i).activeStage u) ((H i).activeStage (time i))
              ((H i).activeStage_mono hut) x,
            Bt.isRmBoundedBy (hat := hut) (Kprim * Qbase i) ∧
            ∃ (b : ((H i).event e).RetainedBoundaryIndex)
              (z : standardCapWindow params.modelRadius),
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
              HEq (((records (idx i) e).static b).window z)
                (Bt.point ((H i).activeStage u) le_rfl ((H i).activeStage_mono hut)) ∧
              ((records (idx i) e).static b).neck.scale ≤ cB * Qbase i := by
    intro x hx
    rw [← hradius] at hx
    rcases hdich x hx with ⟨Bt, hBt⟩ | ⟨u, hut, hau, e, he1, he2, Bt, hBt, b, z, hz, hw, hsc⟩
    · exact Or.inl ⟨Bt, hKeq ▸ hBt⟩
    · exact Or.inr ⟨u, hut, hau, e, he1, he2, Bt, hKeq ▸ hBt, b, z, hz, hw, hceq ▸ hsc⟩
  intro w hw
  rcases hmain (H i) (time i) (anchor i) (Qbase i) (hQbase i) a hat ha' _ hdich' with
    hborn | hjets
  · exact (hB2N (idx i) (time i) (anchor i) (Qbase i) (hQbase i) a hat
      ((le_max_right _ _).trans hti) ha' hdich' hborn w hw).trans (le_max_right _ _)
  · exact (hjets k w hw).trans (le_max_left _ _)

/-- consumer：native G48（G2）⇐ hSL1 ∧ hBorn，`hNJ` 槽由 G2b 逐字填上（类型对齐检查）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hSL1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      let Cbuf : ℝ := max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r < q.neckRadius t →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        (∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt <
                ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r)) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                ENNReal.ofReal Cbuf ^ (2 * n₀) *
                  (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                    ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)))) ∨
        ∃ (u : Icc (0 : ℝ) H.horizon) (hau : aSeed ≤ u) (hut : u ≤ t),
          (t : ℝ) - β / Q < u ∧
          ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
          ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          (let A := seedTrace.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
           ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hut) B v huv hvt <
              ENNReal.ofReal (Cbuf ^ (2 * n₀) * ((d0 + Δ) * r))) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ 4 * (m * Q))
    (hBorn :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J) : True := by
  have _h := native_scalarEscape_of_NJ_C11SP P g (native_NJslot_of_SL1_v2_C11SP P g hSL1 hBorn)
  trivial

end GC.LongTime.Ch11
