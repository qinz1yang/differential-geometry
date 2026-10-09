import DifferentialGeometry.Analysis.Asymptotics.RadiusEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TimeBoundedBallCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedInnerJetsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageCompactnessCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedVolumeBaseCXSP
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

/-!
# CX-SPINE：原 stage carrier 上的实际 first-level scalar escape

TimeCore 从同一个 small seed 生产 canonical base；canonical unit ball 直接启动纯
radius-escape，不需要 gradient 假设。每个严格内球上的纯 scalar bound 转为辅助种子尺度，
实际 bounded-ball traced-region producer 支付全部 jets，再由 stage compactness 生产
volume 与完整 pointed limit 数据。

辅助尺度和主尺度分别为 Qaux 与 Qbase = chi * Qaux；输入球半径为 Rwide/sqrt(chi)，
主尺度时间深度为 chi*beta0/(m+1)，Rm 系数为 Km/chi。每个固定 m 之后再选 late time。
不假设 Good、derivative、trace、volume 或 canonical-witness supply。
唯一 surgery-scale guard 是 neckRadius(t) <= r，没有 ratio 上界。
本定理生产实际 escape limit；最终 hspine 反证仍须消费该极限。
-/

set_option autoImplicit false
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

private theorem escape_scaled_ball_eq_CXSP
    {P : OrientedThreeStage.{u}} (g : P.Metric) (x : P.Carrier)
    {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    riemannianBallOf (scaleMetric Q hQ g) x R =
      riemannianBallOf g x (R / Real.sqrt Q) := by
  have h := riemannianBallOf_scaleMetric Q hQ g x (R / Real.sqrt Q)
  rwa [mul_div_cancel₀ R (Real.sqrt_pos.mpr hQ).ne'] at h

private theorem escape_primary_radius_CXSP {chi Q : ℝ}
    (hchi : 0 < chi) (hQ : 0 < Q) (R : ℝ) :
    (R / Real.sqrt chi) / Real.sqrt Q = R / Real.sqrt (chi * Q) := by
  rw [Real.sqrt_mul hchi.le]
  field_simp [(Real.sqrt_pos.mpr hchi).ne', (Real.sqrt_pos.mpr hQ).ne']

private theorem escape_primary_traced_region_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon} {x : (H.stageAt t).Carrier}
    {chi Q R beta K : ℝ} (hchi : 0 < chi) (hQ : 0 < Q)
    (h : H.isTracedRegion t x ((R / Real.sqrt chi) / Real.sqrt Q)
      (beta / Q) (K * Q)) :
    H.isTracedRegion t x (R / Real.sqrt (chi * Q))
      ((chi * beta) / (chi * Q)) ((K / chi) * (chi * Q)) := by
  have hr := escape_primary_radius_CXSP hchi hQ R
  have ht : (chi * beta) / (chi * Q) = beta / Q := by
    field_simp [hchi.ne', hQ.ne']
  have hk : (K / chi) * (chi * Q) = K * Q := by
    field_simp [hchi.ne']
  rw [ht, hk, ← hr]
  exact h

/-- TimeCore 与实际 prepared chain 在原 stage carrier 生产 scalar-escape pointed limit
的完整数据；辅助常数先于 sequence 及其 primary-scale multiplier 选取。 -/
theorem exists_prepared_time_scalar_escape_CXSP
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
      ∀ Afac : ℝ, 1 < Afac →
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
          (∀ i, q.neckRadius (time i) ≤ r i) →
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
  obtain ⟨ε₀, hε₀, hbounded⟩ := exists_prepared_time_bounded_ball_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨Kb, Tb, hKb, hTb, hcanonical⟩ := hb Afac (zero_lt_one.trans hA)
  obtain ⟨Haux, m0, hHaux, hm0, hboundedA⟩ :=
    hbounded S F q hTower hdiag hacc hrad hord hb Afac hA
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
    rw [escape_scaled_ball_eq_CXSP (metric i) (anchor i) (hQbase i) 1] at hzBall
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
        escape_primary_radius_CXSP hchip hHpos Rwide
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
      escape_primary_radius_CXSP hchip hQaux Rwide
    have hterminal : ∀ w ∈ riemannianBallOf (metric i) (anchor i)
        (RadAux / Real.sqrt Qaux), metricScalarAt (metric i) w ≤ m * Qaux := by
      intro w hw
      have hwN : w ∈ riemannianBallOf (scaleMetric (Qbase i) (hQbase i) (metric i))
          (anchor i) Rwide := by
        rw [escape_scaled_ball_eq_CXSP (metric i) (anchor i) (hQbase i) Rwide, ← hradius]
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
      escape_primary_traced_region_CXSP hchip hQaux htr
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
