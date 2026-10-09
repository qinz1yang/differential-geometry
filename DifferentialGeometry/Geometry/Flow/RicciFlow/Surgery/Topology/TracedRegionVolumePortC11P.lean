import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.BallVolumeComparison
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

/-!
# S-CH11-FIX9 port of astra `TracedRegionVolume`（`PortC11P`）

来源：donor `TracedRegionVolume.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* 文件里 `riemannianVolumeMeasure ThreeModel P.Carrier …` 需要 `MeasurableSpace` / `BorelSpace`
  实例，而 `OrientedThreeStage.Carrier` 没有全局实例（同目录 `EventReducedDensity` /
  `EventTimeNonaccumulation` 都用 `private local instance … := borel _` 补）→ 在 `universe u` 后
  加两条同样的 `private local instance`；
* `hpU`：`rw [hU]` 的目标是 `Opens` 成员 `p ∈ U`，不含 `↑U` → `rw [← SetLike.mem_coe, hU]`；
* `htime`：`sub_nonneg.mpr hvt` 的 `hvt : v ≤ t` 是 `Icc` 子类型的序，elaborator 去找子类型的
  `AddGroup` → `sub_nonneg.mpr (show (v : ℝ) ≤ t from hvt)`。
* `hterminal` 的 `simp only [restrictOpen_inner, mfderiv_subtype_val_apply]` 之后剩
  `(H.stageMetric ↑jt ↑t).inner … = (H.stageMetric (H.activeStage t) ↑t).inner …`
  （`jt` 是 `let`，`↑jt` 不被 simp 归约）→ 补 `rfl`。

原路径 `TracedRegionVolume` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier := borel P.Carrier
private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private theorem volume_ball_restrictOpen_eq_of_subset
    {P : OrientedThreeStage.{u}} (g : P.Metric) (U : Opens P.Carrier)
    [SigmaCompactSpace U] (p : U) (r : ℝ)
    (hball : riemannianBallOf g p.val r ⊆ U) :
    riemannianVolumeMeasure ThreeModel U (g.restrictOpen U)
        (riemannianBallOf (g.restrictOpen U) p r) =
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p.val r) := by
  have hset : riemannianBallOf (g.restrictOpen U) p r =
      (Subtype.val : U → P.Carrier) ⁻¹' riemannianBallOf g p.val r := by
    ext x
    constructor
    · intro hx
      exact (riemannianEDistOf_le_restrictOpen g U p x).trans_lt hx
    · intro hx
      exact Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
        g U p x hball hx
  rw [hset]
  exact Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset g U
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g p.val)
      continuous_const).measurableSet hball

/-- Terminal volume ratios persist at earlier points of the same actual trace
inside a traced region, with a loss depending only on its curvature and depth. -/
theorem volume_ball_ge_along_trace_of_isTracedRegion
    (H : ObservedHistory.{u}) (t v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t)
    (p : (H.stageAt t).Carrier) {ρ τ K κ R r : ℝ} (hK : 0 ≤ K)
    (h : H.isTracedRegion t p ρ τ K) (hv : (t : ℝ) - τ ≤ v)
    (A : BackwardPointTrace H (H.activeStage v) (H.activeStage t)
      (H.activeStage_mono hvt) p)
    (hRρ : R ≤ ρ)
    (hvolume : ∀ s : ℝ, 0 < s → s ≤ R →
      ENNReal.ofReal κ * ENNReal.ofReal s ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p s))
    (hr : 0 < r) (hrR : r ≤ R) :
    ENNReal.ofReal (Real.exp (-54 * K * τ) * κ) * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
        (H.stageMetric (H.activeStage v) v)
        (riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) := by
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_isTracedRegion t p h
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hav : a ≤ v := by change a.val ≤ v.val; rwa [ha]
  have hpU : p ∈ U := by
    rw [← SetLike.mem_coe, hU]
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr h.radius_pos
  let x : U := ⟨p, hpU⟩
  let jt : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩
  let jv : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hflast : f jt = (Subtype.val : U → (H.stageAt t).Carrier) := funext hlast
  have hterminal : S.base.metric t =
      (H.stageMetric (H.activeStage t) t).restrictOpen U := by
    rw [hmetric jt t ⟨hat, le_rfl⟩ (H.activeStage_mem t)]
    apply SmoothRiemannianMetric.ext_inner
    intro y z w
    rw [localPullMetric_inner, hflast]
    simp only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
    rfl
  have hearlier : S.base.metric v =
      localPullMetric (H.stageMetric (H.activeStage v) v) (f jv) (hf jv) :=
    hmetric jv v ⟨hav, hvt⟩ (H.activeStage_mem v)
  let B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p :=
    { point := fun j hj hl => f ⟨j, hj, hl⟩ x
      endpoint_eq := hlast x
      crossing := fun i hi hl => hcross i hi hl x }
  have hcenter : f jv x = A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt) :=
    (B.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)).point_unique
      A (H.activeStage v) le_rfl (H.activeStage_mono hvt)
  let α : ℝ := Real.exp (-9 * K * τ)
  have hα : 0 < α := Real.exp_pos _
  have hα1 : α ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hK h.depth_pos.le]
  have hαr : 0 < α * r := mul_pos hα hr
  have hαrR : α * r ≤ R :=
    (mul_le_mul_of_nonneg_right hα1 hr.le).trans (by simpa only [one_mul] using hrR)
  have hsubset : riemannianBallOf (H.stageMetric (H.activeStage t) t) p (α * r) ⊆ U := by
    rw [hU]
    exact riemannianBallOf_mono _ _ (hαrR.trans hRρ)
  have hterminalVolume : ENNReal.ofReal κ * ENNReal.ofReal (α * r) ^ 3 ≤
      riemannianVolumeMeasure ThreeModel U (S.base.metric t)
        (riemannianBallOf (S.base.metric t) x (α * r)) := by
    rw [hterminal, volume_ball_restrictOpen_eq_of_subset
      (H.stageMetric (H.activeStage t) t) U x (α * r) hsubset]
    exact hvolume (α * r) hαr hαrR
  have hcomparison := riemannianVolumeMeasure_ball_le_exp_mul_of_curvature_bound S hS
    (a := a.val) (b := t.val) (C := K ^ 2) Subset.rfl Subset.rfl hRm
    (show t.val ∈ Icc a.val t.val from ⟨hat, le_rfl⟩)
    (show v.val ∈ Icc a.val t.val from ⟨hav, hvt⟩) x (α * r)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  norm_num only [hdim, Nat.cast_ofNat, Real.sqrt_sq hK] at hcomparison
  have htime : |(t : ℝ) - v| ≤ τ := by
    rw [abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ t from hvt))]
    linarith
  have hradius : Real.exp (9 * K * |(t : ℝ) - v|) * (α * r) ≤ r := by
    dsimp only [α]
    rw [← mul_assoc, ← Real.exp_add]
    have he : Real.exp (9 * K * |(t : ℝ) - v| + -9 * K * τ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hh := mul_le_mul_of_nonneg_left htime (by positivity : 0 ≤ 9 * K)
      linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he hr.le
  have hfactor : Real.exp (27 * K * |(t : ℝ) - v|) ≤ Real.exp (27 * K * τ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime (by positivity))
  have hmap := Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    (S.base.metric v) (H.stageMetric (H.activeStage v) v) (f jv) (hf jv) (hinj jv)
    (fun y z w => by rw [hearlier, localPullMetric_inner]) x r
  rw [hcenter] at hmap
  have hupper : ENNReal.ofReal κ * ENNReal.ofReal (α * r) ^ 3 ≤
      ENNReal.ofReal (Real.exp (27 * K * τ)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) := by
    refine hterminalVolume.trans (hcomparison.trans ?_)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor)
      ((MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hradius)).trans hmap)
  have hcancel : ENNReal.ofReal (Real.exp (-27 * K * τ)) *
      ENNReal.ofReal (Real.exp (27 * K * τ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [show -27 * K * τ + 27 * K * τ = 0 by ring,
      Real.exp_zero, ENNReal.ofReal_one]
  have hlower := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (-27 * K * τ)))) hupper
  have hcancelVolume : ENNReal.ofReal (Real.exp (-27 * K * τ)) *
      (ENNReal.ofReal (Real.exp (27 * K * τ)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r)) =
      riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
        (H.stageMetric (H.activeStage v) v)
        (riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) := by
    rw [← mul_assoc, hcancel, one_mul]
  rw [hcancelVolume] at hlower
  have hexp : Real.exp (-27 * K * τ) * α ^ 3 = Real.exp (-54 * K * τ) := by
    dsimp only [α]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hcoef : ENNReal.ofReal (Real.exp (-27 * K * τ)) *
      (ENNReal.ofReal κ * ENNReal.ofReal (α * r) ^ 3) =
      ENNReal.ofReal (Real.exp (-54 * K * τ) * κ) * ENNReal.ofReal r ^ 3 := by
    rw [ENNReal.ofReal_mul hα.le, mul_pow]
    calc
      _ = (ENNReal.ofReal (Real.exp (-27 * K * τ)) * ENNReal.ofReal α ^ 3) *
          ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_pow hα.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          hexp, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rwa [hcoef] at hlower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
