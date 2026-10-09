import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScalarAnchorCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TimeScalarEscapeCXSP

/-!
# CX-SPINE：原 guard 分支的实际 first-level scalar escape consumer

Awork = 4*A+4、d0 = 2*A+2、Delta = gamma = 1 在 query sequence 前固定。
TimeCore 的实际 producer 先给 Haux 与 Kb，再取 chi≥1 支付 canonical threshold，
并固定 Hbase = chi*Haux≥4。原坏序列的 last-crossing anchor 与 scalar failure
由 P6ScalarAnchorCXSP 实际生产，不作为本定理的额外输入。

原 A-volume 只通过 seed_volume_of_parameter_le_CXSP 的显式数值单调性供给
TimeCore(Awork)；本定理不消费 hw(A)，也不扩大它的适用范围。原 p→x minimizing
segment 及其 high tail 始终保留在原 A*r 球中。全项 nr(t)≤r 是唯一 ratio guard。
输出实际正尺度 Q 及逐项等式 Q i = Hbase/r_i²，所有 pointed 数据直接使用同一 Q，
避免整份 dependent convergence data 的重写。本层仍未给出最终 cone 矛盾。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem guard_scaleMetric_congr_CXSP
    {P : OrientedThreeStage.{u}} (g : P.Metric) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hcd : c = d) :
    scaleMetric c hc g = scaleMetric d hd g := by
  subst d
  rfl

/-- 原 scalar 坏序列的 guard 分支直接产生完整 first-level pointed escape；所有尺度常数
先于该序列选取，anchor、fit、scalar failure 和几何紧性供给均在证明内完成。 -/
theorem exists_guard_scalar_escape_CXSP
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
      ∀ A : ℝ, 0 < A → ∃ Hbase : ℝ, 4 ≤ Hbase ∧
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
        (∀ i, q.neckRadius (t i) ≤ r i) →
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
  obtain ⟨ε₀, hε₀, hescape⟩ := exists_prepared_time_scalar_escape_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb A hA
  let Awork : ℝ := 4 * A + 4
  have hAwork : 1 < Awork := by dsimp only [Awork]; linarith only [hA]
  have hAAwork : A ≤ Awork := by dsimp only [Awork]; linarith only [hA]
  obtain ⟨Haux, _m0, Kb, _Tb, hHaux, _hm0, _hKb, _hTb, hrun⟩ :=
    hescape S F q hTower hdiag hacc hrad hord hb Awork hAwork
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
    guard_scaleMetric_congr_CXSP (metric i) (hQ i) (hQseed i) (hscaleSeed i)
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
