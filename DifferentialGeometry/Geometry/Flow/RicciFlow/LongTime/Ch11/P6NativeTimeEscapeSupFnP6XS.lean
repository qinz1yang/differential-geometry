import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeTimeEscapePBC11SP

set_option autoImplicit false

/-!
# supply-threaded fn twin（O-CH11-XSUP2 层 X5，后缀 `_P6XS`）

孪生对象 `native_scalarEscape_of_NJ_PB_C11SP`。
生成器 `build-logs/scratch/O-CH11-XSUP2/gen/fnlib.py`；
源 `P6NativeTimeEscapePBC11SP.lean`（tracked，不改）。
记 SUP := `TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime`：由 v8 collar 引擎孪生
在同一 `T.toChain / F / q` 处用 `hTD` 付，不是对任意链的总前提。
`Rn mn : ClosedBirthConstants → _`：请求依赖 `Γf`，provider 先取 `Γ Γf` 再请求，不交换量词。
`ε₀ : ClosedBirthConstants → ℝ`：Dt 常数为 `Γf.Ctime`，精度门槛随 `Γf`。
INTEGRATION-ONLY（无新 def / Prop）。
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

private theorem escape_scaled_ball_eq_NJ_C11SP
    {P : OrientedThreeStage.{u}} (g : P.Metric) (x : P.Carrier)
    {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    riemannianBallOf (scaleMetric Q hQ g) x R =
      riemannianBallOf g x (R / Real.sqrt Q) := by
  have h := riemannianBallOf_scaleMetric Q hQ g x (R / Real.sqrt Q)
  rwa [mul_div_cancel₀ R (Real.sqrt_pos.mpr hQ).ne'] at h

/-- **XSUP2 supply-threaded fn twin** of `native_scalarEscape_of_NJ_PB_C11SP`：
PB 透传 binder 与结论经 (a) `hdiag` 后加供给前提 (b) `ε₀` 函数化 (c) `Rn Γf / mn Γf`；
冻结 binder 不动；证明逐字 + `hSUP` 透传。 -/
theorem native_scalarEscape_of_NJ_SupFn_P6XS
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hNJ :
      ∃ ε₀ : ClosedBirthConstants → ℝ, (∀ Γf, 0 < ε₀ Γf) ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
          pBase.modelAccuracy ≤ ε₀ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → (Rn Γf ≤ pBase.modelRadius ∧ mn Γf ≤ pBase.modelOrder) →
          CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
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
            ∀ᶠ i in atTop, HasLocalCurvDerivBound (Xall.obj i) (Xall.obj i).basepoint R k J) :
    ∃ ε₀ : ClosedBirthConstants → ℝ, (∀ Γf, 0 < ε₀ Γf) ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
        pBase.modelAccuracy ≤ ε₀ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → (Rn Γf ≤ pBase.modelRadius ∧ mn Γf ≤ pBase.modelOrder) →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
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
  obtain ⟨ε₀, hε₀, hnj⟩ := hNJ
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hSUP hacc hrad hord hPB hb Afac hA
  obtain ⟨Kb, Tb, hKb, hTb, hcanonical⟩ := hb Afac (zero_lt_one.trans hA)
  obtain ⟨Haux, hHaux, hnjA⟩ := hnj S F q hTower hdiag hSUP hacc hrad hord hPB hb Afac hA
  refine ⟨Haux, 1 / 2, Kb, Tb, hHaux, le_rfl, hKb, hTb, ?_⟩
  intro d0 Δ gamma hd0 hΔ hgamma hbuffer
  have hnjD := hnjA d0 Δ gamma hd0 hΔ hgamma hbuffer
  intro chi hchi hscale Rad dAnchor hdAnchor hfit idx H time p anchor r htime hsmall hvol
    hnat htlim stage metric Qbase hQbase Xall hanchorR hanchorDist hfailure
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
    rw [escape_scaled_ball_eq_NJ_C11SP (metric i) (anchor i) (hQbase i) 1] at hzBall
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
    have hRwiderho : Rwide < rho := by dsimp only [Rwide]; linarith only [hRrho]
    obtain ⟨B, hB⟩ := hinner Rwide hRwiderho
    exact hnjD chi hchi Rad dAnchor hdAnchor hfit idx time p anchor r htime hsmall hvol hnat
      htlim hanchorR hanchorDist R Rwide hR hRRwide (by linarith only [hRwiderho, hrhoRad]) B hB k
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
