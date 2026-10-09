import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841RegionalCXSK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallScaleSeedC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineTowerC11Q6

/-!
# retention 的同源 Pre841 + 区域 κ producer（CX-SEEDK）

CXCW retention inputs 原样保持；在同一个 hK5、hloc、hsmallSeed 上构造两个输出。
不是从孤立 Pre841Data 反推 hκR，也不引入 global nr=0 window。
hseedWin、hwin、hdist 及原 retention/KDATA 条件仍明示保留。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- 具体 retention consumer：原 CXCW 前提直接产出同源 d 与 d.kappa 的区域供给。 -/
theorem exists_pre841Data_regional_of_retention_seedWindow_CXSK
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdomK3 : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    {A : ℝ} (hA : 0 < A) (hP3 : CollarWindowSupply_C11E.{u} N.params)
    (hprof : ModelConstraintsSupply_C11E N.params εProf_C11E.{u})
    (hacc₀ : N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P)
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n))
    (hseedWin : ∀ᶠ n in atTop,
      N.params.neckRadius ((t n : ℝ) - r n ^ 2 / 2) ≤ r n) :
    ∃ d : Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR,
    ∀ᶠ n in atTop,
      ∀ (j : Fin (F.tower.history (ind n)).eventCount)
        (c : ((F.tower.history (ind n)).stage j.castSucc).Carrier)
        (U : Set ((F.tower.history (ind n)).stage j.castSucc).Carrier) (a v ρU : ℝ),
      (t n : ℝ) - r n ^ 2 / 2 ≤ a → v ≤ (t n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon),
        a ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        (F.tower.history (ind n)).time j.castSucc < τ →
        (τ : ℝ) < (F.tower.history (ind n)).time j.succ →
        ∀ z ∈ U,
        ∀ zz cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier,
        HEq zz z → HEq cc c →
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage τ) τ) cc zz < ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon),
        a ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        (F.tower.history (ind n)).time j.castSucc < τ →
        (τ : ℝ) < (F.tower.history (ind n)).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ t n),
        ∀ cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage τ) τ)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage τ)
              ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) cc +
              ENNReal.ofReal ρU ≤ ENNReal.ofReal (A * r n)) →
      RegionalKappa_C11Q3 (F.tower.history (ind n)) j U a v (r n / 200) d.kappa := by
  obtain ⟨hK3, hnode, hure⟩ :=
    nodes_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hK4 := boundedReducedLengthScaled_of_end_C11Q4
    (weightedMinBoundEndScaled_of_nodeData_C11Q4 N.params N.records N.Ctime hnode) hK3
    (fun _ _ => le_rfl)
  have hK5 := seedReducedVolumeScaled_of_block_C11Q4 (fun A _ => ureBlockKappa_pos_C11Q3 A) hK4
    (seedRegularBlock_of_URE_C11Q4 N.params N.records N.Ctime hure)
  have hloc : LocalKappaSupply_P6B F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius :=
    localKappaP6B_of_reducedVolumeScaled_C11Q4 hK5
  obtain ⟨κ', hκ', hsmallSeed⟩ :=
    (hsmallSeed_of_wideScaledSupply_C11V5.{u} N.epsilon N.C1 N.C2 P).choose_spec.2 hA hP3 hprof
      hacc₀ N.records N.canonical_windows N.delta_antitone N.radius_antitone N.canonical
      (localKappaWideScaled_of_reducedVolumeScaled_C11Q4b hK5)
  exact exists_pre841Data_regional_of_localKappa_seedWindow_CXSK
    (largerBallAccuracySupply_diagonal_C11S N.params N.delta_antitone) hloc hA hκ' hsmallSeed ind
    (N.comp ind) t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin
    hdist N.radius_antitone hseedWin

end GC.LongTime.Ch11
