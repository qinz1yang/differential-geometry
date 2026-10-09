import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReservePhysicalInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialUniformPinching

/-!
# S-CH11-FIX9 port of astra `PreparedSpatialUniformReserveBall`（`PortC11P`）

来源：donor `PreparedSpatialUniformReserveBall.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 通过（overlay verbatim OK），但有 12 条 `unusedVariables` warning
（陈述里的 hypothesis binder 只在 `intro` 里引用）。本 port 只把这 12 个 binder 名加 `_` 前缀
（陈述 / 定义 / 证明思路不变，binder 名不改变陈述；不加 `set_option`）：
`hLR hshift hoffset hshift_nonneg hmodelRadius hmodelAccuracy hmodelOrder hclassScale hfit htop
hRle hback`。

原路径 `PreparedSpatialUniformReserveBall` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology

namespace GC.GeneralFlow
universe u

/-- Choose pinching from the original metric and one numerical reserve margin
before every native state and fine extension. The actual ball uses the retained
class quality, records and metric of that same old native history. -/
theorem exists_same_native_reserve_ball_control_of_retained_class_quality
    (Dstar : ℝ) (hDstar : StandardCap.transitionEnd < Dstar) :
    ∃ εcap : ℝ, 0 < εcap ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (C : ClosedBirthConstants),
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∃ cMax : ℝ, 0 < cMax ∧
    ∀ {pBase : CutoffParameters}
      {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
      {L : PreparedSpatialState pBase C P g E B}
      {R : PreparedSpatialState pBase C P g B Bnext}
      (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
      (_hLR : PreparedSpatialSuccessor L R activation eta d)
      (_hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
      (_hoffset : R.offset = L.history.eventCount)
      (_hshift_nonneg : 0 ≤ L.shift)
      (_hmodelRadius : Dstar ≤ L.prepared.parameters.modelRadius)
      (_hmodelAccuracy : L.prepared.parameters.modelAccuracy ≤ εcap)
      (_hmodelOrder : 2 ≤ L.prepared.parameters.modelOrder)
      (_hclassScale : 32 * L.prepared.Qall * L.prepared.radiusBound ^ 2 ≤ 1)
      (_hfit : L.radius * Real.sqrt L.prepared.Qall ≤ 100 * cMax)
      (t : Icc (0 : ℝ) W.oldNative.horizon) (_htop : (t : ℝ) < W.oldNative.horizon)
      (y : (W.oldNative.toHistory.stageAt t).Carrier)
      (_hRle : metricScalarAt
        (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage t) t) y ≤
          L.prepared.Qall)
      (_hback : (L.radius / 100) ^ 2 ≤ (t : ℝ)),
      W.oldNative.toHistory.isParabolicallyRmControlledBall t y (L.radius / 100) := by
  obtain ⟨εcap, hεcap, hcap⟩ := exists_old_native_cap_scalar_quality.{u} Dstar hDstar
  refine ⟨εcap, hεcap, ?_⟩
  intro P g C
  obtain ⟨phi, hphi, hpinch⟩ := exists_uniform_pinching_for_same_full_native_steps P g
  let Kphi : ℝ := 32 * Real.sqrt 3 * (1 + phi 1 + phi 0)
  have hKphi : 0 < Kphi := by
    have h1 := hphi.pos 1
    have h0 := hphi.pos 0
    dsimp only [Kphi]
    positivity
  let cMax : ℝ := min 1 (min (1 / (4 * ((C.Cgrad : ℝ) + 1)))
    (min (1 / (8 * ((C.Ctime : ℝ) + 1))) (1 / (Kphi + 1))))
  have hcMax : 0 < cMax := by dsimp only [cMax]; positivity
  have hcOne : cMax ≤ 1 := min_le_left _ _
  have hcGrad : cMax ≤ 1 / (4 * ((C.Cgrad : ℝ) + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcTime : cMax ≤ 1 / (8 * ((C.Ctime : ℝ) + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcPinch : cMax ≤ 1 / (Kphi + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcSq : cMax ^ 2 ≤ cMax := by nlinarith only [hcMax.le, hcOne]
  have hGradCap : (C.Cgrad : ℝ) * cMax ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * ((C.Cgrad : ℝ) + 1))).mp hcGrad
    nlinarith only [h, hcMax.le]
  have hTimeCap : 4 * (C.Ctime : ℝ) * cMax ^ 2 ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * ((C.Ctime : ℝ) + 1))).mp hcTime
    have hsq := mul_le_mul_of_nonneg_left hcSq C.Ctime.coe_nonneg
    nlinarith only [h, hsq, hcMax.le]
  have hPinchCap : Kphi ^ 2 * cMax ^ 4 ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < Kphi + 1)).mp hcPinch
    have hKc : Kphi * cMax ≤ 1 := by nlinarith only [h, hcMax.le]
    have hKsq : Kphi * cMax ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hcSq hKphi.le).trans hKc
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ Kphi * cMax ^ 2) hKsq 2
    calc
      Kphi ^ 2 * cMax ^ 4 = (Kphi * cMax ^ 2) ^ 2 := by ring
      _ ≤ 1 ^ 2 := hsquare
      _ = 1 := by norm_num
  refine ⟨phi, hphi, cMax, hcMax, ?_⟩
  intro pBase E B Bnext activation eta d εcut Dcut mcut L R W hLR hshift hoffset
    hshift_nonneg hmodelRadius hmodelAccuracy hmodelOrder hclassScale hfit t htop y hRle hback
  have hpinchW := hpinch W hLR hshift hoffset hshift_nonneg
  let M : ℝ := L.prepared.Qall
  let b : ℝ := L.radius / 100
  have hM : 0 < M := L.prepared.Qall_pos
  have hb : 0 < b := div_pos L.radius_pos (by norm_num)
  have hfit' : b * Real.sqrt M ≤ cMax := by
    dsimp only [b, M]
    nlinarith only [hfit]
  have hcNonneg : 0 ≤ b * Real.sqrt M := mul_nonneg hb.le (Real.sqrt_nonneg _)
  have hgradScale : (C.Cgrad : ℝ) * b * Real.sqrt M ≤ 1 / 4 := by
    calc
      (C.Cgrad : ℝ) * b * Real.sqrt M = C.Cgrad * (b * Real.sqrt M) := by ring
      _ ≤ C.Cgrad * cMax := mul_le_mul_of_nonneg_left hfit' C.Cgrad.coe_nonneg
      _ ≤ 1 / 4 := hGradCap
  have htimeScale : (C.Ctime : ℝ) * (4 * M) * b ^ 2 ≤ 1 / 2 := by
    calc
      (C.Ctime : ℝ) * (4 * M) * b ^ 2 =
          4 * C.Ctime * (b * Real.sqrt M) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hM.le]
        ring
      _ ≤ 4 * C.Ctime * cMax ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcNonneg hfit' 2) (by positivity)
      _ ≤ 1 / 2 := hTimeCap
  have hsqrtFour : Real.sqrt M ^ 4 = M ^ 2 := by
    calc
      Real.sqrt M ^ 4 = (Real.sqrt M ^ 2) ^ 2 := by ring
      _ = M ^ 2 := by rw [Real.sq_sqrt hM.le]
  have hpinchScale : b ^ 4 *
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) ^ 2 ≤ 1 := by
    calc
      b ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) ^ 2 =
          Kphi ^ 2 * (b * Real.sqrt M) ^ 4 := by
        dsimp only [Kphi]
        simp only [mul_pow, hsqrtFour]
        ring
      _ ≤ Kphi ^ 2 * cMax ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcNonneg hfit' 4) (sq_nonneg _)
      _ ≤ 1 := hPinchCap
  have hlast : W.oldNative.toHistory.activeStage t = Fin.last W.oldNative.eventCount →
      ∃ h : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab h).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi := by
    intro hlast
    have hstart : W.oldNative.time (Fin.last W.oldNative.eventCount) ≤ (t : ℝ) := by
      simpa only [hlast] using W.oldNative.toHistory.activeStage_time_le t
    have hfinal := hstart.trans_lt htop
    exact ⟨hfinal, hpinchW.2 hfinal⟩
  exact W.isParabolicallyRmControlledBall_at_reserve_of_scalar_le
    W.oldNative_hasCanonicalWindows
    (hcap W hmodelRadius hmodelAccuracy hmodelOrder) hphi hpinchW.1
    t htop hlast y hRle hback hgradScale htimeScale hpinchScale
    (fun i _ b' => W.static_scale_gt_sixteen_own_threshold_of_class_bound hclassScale i b')

end GC.GeneralFlow
