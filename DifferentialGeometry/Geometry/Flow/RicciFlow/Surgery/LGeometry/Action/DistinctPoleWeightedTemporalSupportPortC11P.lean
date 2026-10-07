import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ControlledPolePhysicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSupportBranches
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# S-CH11-FIX9 port of astra `DistinctPoleWeightedTemporalSupport`（`PortC11P`）

来源：donor `DistinctPoleWeightedTemporalSupport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* 陈述里的 `ℝ≥0` 需要 `open scoped NNReal`（donor 漏开）→ 在 `open scoped` 行补上 `NNReal`；
* `field_simp [hw.ne'] <;> ring`：`field_simp` 已关掉目标，`ring` 永不执行 → 删去 `<;> ring`；
* 2 处 `WithTop.not_top_le_coe hbootstrap`（本树 `a` 显式）→ `WithTop.not_top_le_coe _ hbootstrap`；
* `(mul_le_mul_left (mul_pos …)).mp hh`（本树 `mul_le_mul_left` 是 `Mul` 单调的另一个意思）→
  `le_of_mul_le_mul_left hh (mul_pos …)`；
* `hshifted` 的 `linarith`：`-2 * v ^ 3 / r ^ 2` 与 `2 * v ^ 3 / r ^ 2` 被当成不同原子 → 先给
  `hneg : -2 * v ^ 3 / r ^ 2 = -(2 * v ^ 3 / r ^ 2)`；
* `hinner` / `hclock` / `hpsi`：`convert … using 1 <;> ring` 在本树多出函数相等的目标（`e'_8`；
  `HasDerivAt.sub` 等的函数用 `Pi` 运算 / `Function.comp` 表示）→ `HasDerivAt.congr_deriv`
  （函数按 defeq 对上）后 `simp only [id_eq]`（`hpsi` 还要 `Function.comp_apply, Pi.mul_apply`）再 `ring`；
* `Ioi_mem_nhds hv` / `Iio_mem_nhds hE` 的 `.filter_mono nhdsWithin_le_nhds`（成员关系的点记号找不到）→
  `nhdsWithin_le_nhds (Ioi_mem_nhds hv)`；
* 主定理证明里 `hstart : gamma ⟨H.activeStage t, _⟩ 0 = x` / `hend`（来自 `hSupport` 的 `let last := …`
  已被 zeta 归约）与后文的 let 变量 `last` 在 `simp only` / `simpa only` 里不匹配 →
  先 `have hstart' : gamma ⟨last, hle, le_rfl⟩ 0 = x := hstart`、`hend'`（defeq），其后用 `hstart'` /
  `hend'`；`hjetTransport` 末尾的 `simpa only [hLoriginal] using hlap` →
  `rw [hLoriginal] at h; exact h`；
* `hnonnegative` 的 `unfold physicalWeightedCost; split_ifs`：unfold 之后是 `let …; if …`，
  `split_ifs` 看不见 → 先 `dsimp only`；
* 未限定的 `continuousAt_riemannianEDistOf`（donor 没开 `Geometry.Riemannian`）→ 全名；
* 2 处 `nlinarith` / `simpa [neg_div]` 的代数（`hd : toReal < r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)`
  与目标只差 `ring`；`-2 * v ^ 3 / r ^ 2` 不是 `-a / b` 形）→ `hd.trans_eq (by ring)` /
  `(le_of_eq (by ring)).trans …`；
* 其余 `field_simp … <;> ring`（`<;>` 触发 unnecessarySeqFocus）→ 换行 `ring`；陈述里未引用的 binder
  `identification`（两处）与第二处的 `records` → 加 `_`；
* `hmv` 的 `dsimp only [m]` 之后目标里是 let 变量 `M`，`rw [hMvalue]` 找不到 → `dsimp only [m, M]`。

原路径 `DistinctPoleWeightedTemporalSupport` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem regularizedCost_ge_neg_clock_of_recent
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T w : ℝ) (hw : 0 < w) (hT : 4 * w ^ 2 < T)
    (x : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    ((-w : ℝ) : WithTop ℝ) ≤ H.regularizedCost first last hle T (3 / a₀) 0 w x q := by
  let rAux : ℝ := Real.sqrt 2 * w
  have hrAux : 0 < rAux := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hw
  have hrAux2 : rAux ^ 2 = 2 * w ^ 2 := by
    dsimp only [rAux]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hhalf : w ^ 2 ≤ rAux ^ 2 / 2 := by rw [hrAux2]; nlinarith
  have hrecent : 2 * rAux ^ 2 < T := by rw [hrAux2]; nlinarith only [hT]
  have hlow := H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀
    hfixed hscalar first last hle hrAux hw.le hhalf hrecent x q
  have heq : -2 * w ^ 3 / rAux ^ 2 = -w := by
    rw [hrAux2]
    field_simp [hw.ne']
  simpa only [heq] using hlow

theorem regularizedCost_lt_action_budget_of_weighted_bootstrap
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B r A v D : ℝ) (x : (H.stage last).Carrier) (O q : (H.stage first).Carrier)
    (hr : 0 < r) (hv : 0 < v)
    (hshifted : ∀ L : ℝ,
      H.regularizedCost first last hle T B 0 v x q = (L : WithTop ℝ) → 0 < L + r)
    (hbootstrap : H.physicalWeightedCost first last hle T B r A v x O q ≤
      ((2 * r * v * D : ℝ) : WithTop ℝ)) :
    riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ L : ℝ,
      H.regularizedCost first last hle T B 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      H.regularizedCost first last hle T B 0 v x q < ((D * r : ℝ) : WithTop ℝ) := by
  have hinside : riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) := by
    by_contra hn
    have htop : H.physicalWeightedCost first last hle T B r A v x O q = ⊤ := by
      simp only [physicalWeightedCost, ite_eq_right hn]
    rw [htop] at hbootstrap
    exact WithTop.not_top_le_coe _ hbootstrap
  have hfinite : H.regularizedCost first last hle T B 0 v x q ≠ ⊤ := by
    intro htop
    simp only [physicalWeightedCost, ite_eq_left hinside, htop, WithTop.map_top] at hbootstrap
    exact WithTop.not_top_le_coe _ hbootstrap
  obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hcost : H.regularizedCost first last hle T B 0 v x q = (L : WithTop ℝ) := hL.symm
  have harg : (riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q).toReal / r -
      A * (1 - 2 * v ^ 2 / r ^ 2) < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hinside
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith only [hd]
  have hphi := DifferentialGeometry.Analysis.SingularBarrier.one_le harg
  have hpositive : 0 < 2 * v * L + 2 * r * v := by
    have hh := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hv) (hshifted L hcost)
    nlinarith only [hh]
  have hbound : DifferentialGeometry.Analysis.SingularBarrier.value
      ((riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q).toReal / r -
        A * (1 - 2 * v ^ 2 / r ^ 2)) * (2 * v * L + 2 * r * v) ≤ 2 * r * v * D := by
    simpa only [physicalWeightedCost, ite_eq_left hinside, hcost, WithTop.map_coe,
      WithTop.coe_le_coe] using hbootstrap
  have hplain : 2 * v * L + 2 * r * v ≤ 2 * r * v * D := by
    have hh := mul_le_mul_of_nonneg_right hphi hpositive.le
    have hbase : 2 * v * L + 2 * r * v ≤
        DifferentialGeometry.Analysis.SingularBarrier.value
          ((riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q).toReal / r -
            A * (1 - 2 * v ^ 2 / r ^ 2)) * (2 * v * L + 2 * r * v) := by
      simpa only [one_mul] using hh
    exact hbase.trans hbound
  have hLbound : L ≤ (D - 1) * r := by
    have hh : 2 * v * (L + r) ≤ 2 * v * (r * D) := by nlinarith only [hplain]
    have hcancel := le_of_mul_le_mul_left hh (mul_pos (by norm_num : (0 : ℝ) < 2) hv)
    nlinarith only [hcancel]
  refine ⟨hinside, L, hcost, hLbound, ?_⟩
  rw [hcost]
  exact WithTop.coe_lt_coe.mpr (by nlinarith only [hLbound, hr])

private theorem exists_nonpositive_clock_upper_support
    (T r C v L phi : ℝ) (m W : ℝ → ℝ)
    (hr : 0 < r) (hv : 0 < v) (hhalf : v ^ 2 ≤ r ^ 2 / 2)
    (hphi : 0 < phi) (hL : -(2 * v ^ 3 / r ^ 2) ≤ L)
    (hm : m v = 2 * v * phi * (L + r))
    (hcontact : W (T - v ^ 2) = m v)
    (hupper : ∀ᶠ w in 𝓝[>] v, m w ≤ W (T - w ^ 2))
    (hW : DifferentiableAt ℝ W (T - v ^ 2))
    (hheat : -(C / r ^ 2) * m v - (7 + r / v) * phi ≤
      deriv W (T - v ^ 2)) :
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    ∃ psi : ℝ → ℝ, ∃ d : ℝ,
      psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧
      HasDerivAt psi d v ∧ d ≤ 0 := by
  intro f
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hcube : 2 * v ^ 3 / r ^ 2 ≤ v := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf hv.le
    nlinarith only [hh]
  have hLv : -v ≤ L := by linarith only [hL, hcube]
  have hvr : v ≤ 3 * r / 4 := by
    apply (sq_le_sq₀ hv.le (by positivity : 0 ≤ 3 * r / 4)).mp
    nlinarith only [hhalf, hr2]
  have hLr : r / 4 ≤ L + r := by linarith only [hLv, hvr]
  have hLdiv : -1 ≤ L / v := (le_div_iff₀ hv).mpr (by linarith only [hLv])
  have hLrdiv : 8 ≤ 32 * (L + r) / r :=
    (le_div_iff₀ hr).mpr (by linarith only [hLr])
  have hnum : 7 - L / v - 32 * (L + r) / r ≤ 0 := by
    linarith only [hLdiv, hLrdiv]
  let psi : ℝ → ℝ := fun w =>
    Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * W (T - w ^ 2) / w
  let d : ℝ := Real.exp (-C * v ^ 2 / r ^ 2 - 32 * v / r) *
    ((-2 * C * v / r ^ 2 - 32 / r) * m v / v -
      2 * deriv W (T - v ^ 2) - m v / v ^ 2)
  have hinner : HasDerivAt (fun w : ℝ => -C * w ^ 2 / r ^ 2 - 32 * w / r)
      (-2 * C * v / r ^ 2 - 32 / r) v := by
    have h := ((((hasDerivAt_id v).pow 2).const_mul (-C)).div_const (r ^ 2)).sub
      (((hasDerivAt_id v).const_mul 32).div_const r)
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hclock : HasDerivAt (fun w : ℝ => T - w ^ 2) (-2 * v) v := by
    have h := ((hasDerivAt_id v).pow 2).const_sub T
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hcomp := hW.hasDerivAt.comp v hclock
  have hpsi : HasDerivAt psi d v := by
    change HasDerivAt
      (fun w => Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * W (T - w ^ 2) / w) d v
    have h := ((hinner.exp).mul hcomp).div (hasDerivAt_id v) hv.ne'
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply, id_eq]
    rw [hcontact]
    dsimp only [d]
    field_simp [hv.ne', hr.ne']
    ring
  have hderiv : d ≤ 0 := by
    have hbound :
        (-2 * C * v / r ^ 2 - 32 / r) * m v / v -
            2 * deriv W (T - v ^ 2) - m v / v ^ 2 ≤
          2 * phi * (7 - L / v - 32 * (L + r) / r) := by
      calc
        _ ≤ (-2 * C * v / r ^ 2 - 32 / r) * m v / v +
            2 * ((C / r ^ 2) * m v + (7 + r / v) * phi) - m v / v ^ 2 := by
          linarith only [hheat]
        _ = _ := by
          rw [hm]
          field_simp [hv.ne', hr.ne']
          ring
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (hbound.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnum))
  refine ⟨psi, d, ?_, ?_, hpsi, hderiv⟩
  · simp only [psi, f, hcontact]
  · have hpos : ∀ᶠ w in 𝓝[>] v, 0 < w :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hv)
    filter_upwards [hupper, hpos] with w hw hwp
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le) hwp.le


theorem exists_uniform_distinct_pole_half_clock_bootstrap_support
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P₀ g₀ H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ (Aact E rTerm qDeriv ρ : ℝ) (Cderiv : ℝ≥0),
      0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
    ∃ (m₀ : ℕ) (R₀ ε₀ δ₀ : ℝ), 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ →
      (∀ i : Fin H.eventCount,
        parameters.recenterConstant * parameters.delta (H.time i.succ) ≤ 1 / 2) →
      (∀ i : Fin H.eventCount, parameters.delta (H.time i.succ) ≤ δ₀) →
      (∀ i : Fin H.eventCount, parameters.neckRadius (H.time i.succ) ≤ ρ) →
    ∀ (records : ∀ i, GeometricCutoffRecord H i parameters)
      (_identification : InitialIdentification P₀ g₀ H)
      (t : Icc (0 : ℝ) H.horizon),
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
    ∀ (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
      H.isParabolicallyRmControlledBall t x rTerm →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    D * r ≤ Aact →
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ≤ E → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
      (∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
        ∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧ L < Aact ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0 := by
  classical
  obtain ⟨a₀, ha₀, hInitial, hPrepare⟩ :=
    exists_uniform_physical_cost_support_on_action_sublevel P₀ g₀
  refine ⟨a₀, ha₀, hInitial, ?_⟩
  intro Aact E rTerm qDeriv ρ Cderiv hE hrTerm hqDeriv hρ
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hSupport⟩ :=
    hPrepare Aact E rTerm qDeriv ρ Cderiv hE hrTerm hqDeriv hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hR hε hrecent hδ hneck records identification t hderiv
    p x r A hr hA hT hseed htest aSeed hSeedTime hSeedClock seedTrace C D hfit
    a has hat v hv hvE hhalf hclock hpole hpast hwindow first last hle O q hminimum hbootstrap
  obtain ⟨hfixed, hscalar⟩ := hInitial H identification
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hvr : v < 3 * r / 4 := by
    apply (sq_lt_sq₀ hv.le (by positivity : 0 ≤ 3 * r / 4)).mp
    nlinarith only [hhalf, hr2]
  have hcube : 2 * v ^ 3 / r ^ 2 ≤ v := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf hv.le
    nlinarith only [hh]
  have hshifted (L : ℝ)
      (hL : H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ)) :
      0 < L + r := by
    have hlow := H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀
      hfixed hscalar first last hle hr hv.le hhalf hT x q
    rw [hL] at hlow
    have hh := WithTop.coe_le_coe.mp hlow
    have hneg : -2 * v ^ 3 / r ^ 2 = -(2 * v ^ 3 / r ^ 2) := by ring
    linarith only [hh, hcube, hvr, hr, hneg]
  obtain ⟨hinside, L, hcost, hLbound, hcostD⟩ :=
    H.regularizedCost_lt_action_budget_of_weighted_bootstrap first last hle
      t.val (3 / a₀) r A v D x O q hr hv hshifted hbootstrap
  have hcostlt : H.regularizedCost first last hle t.val (3 / a₀) 0 v x q <
      (Aact : WithTop ℝ) := hcostD.trans_le (WithTop.coe_le_coe.mpr hfit)
  have hLact : L < Aact := by
    rw [hcost] at hcostlt
    exact WithTop.coe_lt_coe.mp hcostlt
  obtain ⟨gamma, hgamma, hgammaAC, hgammaInt, hstart, hend, hnodes,
      hattain, hcross, hSupports⟩ :=
    hSupport H parameters hm hR hε hrecent hδ hneck records identification t hderiv
      x htest first hle v hv hvE hpole hpast hwindow q hcostlt
  have hstart' : gamma ⟨last, hle, le_rfl⟩ 0 = x := hstart
  have hend' : gamma ⟨first, le_rfl, hle⟩ v = q := hend
  obtain ⟨U, F, hU, hqU, hFC2, hFvalue, hcontact, hupper,
      hgradient, hclockJet, hlap, _hphysical⟩ := hSupports 1 (by norm_num)
  have hqU' : (q, v) ∈ U := by
    have h := hqU
    rw [hend] at h
    exact h
  have hupper' : ∀ z ∈ U,
      H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤ (F z : WithTop ℝ) := by
    have h := hupper
    rw [hstart] at h
    exact h
  have hcontact' : H.regularizedCost first last hle t.val (3 / a₀) 0 v x q =
      (F (q, v) : WithTop ℝ) := by
    have h := hcontact
    rw [hstart, hend] at h
    exact h
  have hFcontact : F (q, v) = L :=
    WithTop.coe_injective (hcontact'.symm.trans hcost)
  have hLoriginal : (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) = L := by
    have hh : F (gamma ⟨first, le_rfl, hle⟩ v, v) = L := by
      have h := hFcontact
      rw [← hend] at h
      exact h
    exact hFvalue.symm.trans hh
  let g := H.stageMetric first (t.val - v ^ 2)
  have hjetTransport (y : (H.stage first).Carrier)
      (hy : gamma ⟨first, le_rfl, hle⟩ v = y) :
      let Vy : TangentSpace ThreeModel y :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hy)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      gradientFun g (fun z => F (z, v)) y = Vy ∧
      HasDerivAt (fun w => F (y, w))
        (2 * v ^ 2 * metricScalarAt g y - (1 / 2 : ℝ) * g.inner y Vy Vy) v ∧
      laplacian (LeviCivita g) g (fun z => F (z, v)) y <
        3 / v - v * metricScalarAt g y - L / (2 * v ^ 2) +
          g.inner y Vy Vy / (4 * v) + 1 / (2 * v) := by
    subst y
    dsimp only
    refine ⟨hgradient, hclockJet, ?_⟩
    have h := hlap
    rw [hLoriginal] at h
    exact h
  obtain ⟨hgradient', hclockJet', hlap'⟩ := hjetTransport q hend
  obtain ⟨hfinite, hlocalMin⟩ :=
    H.isLocalMin_physical_weighted_of_extended_minimum_and_same_support
      first last hle t.val (3 / a₀) r A hv x O q U F hU hqU' hupper' hinside hminimum
  let trace : BackwardPointTrace H first last hle p :=
    seedTrace.restrictFirst (H.activeStage_mono has) hle
  have hSeedRicci := hseed.ricci_le_on_past_seed_core_on_half_clock H t a hat p r v
    hv hhalf hclock trace
  have hcostCurve := hcontact.trans (congrArg (fun ell : ℝ => (ell : WithTop ℝ)) hFvalue)
  have hroomCurve : 0 < (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) + r := by
    rw [hLoriginal]
    exact hshifted L hcost
  have hinsideCurve : riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O
      (gamma ⟨first, le_rfl, hle⟩ v) <
      ENNReal.ofReal (r * (A * (1 - 2 * ((t.val - (t.val - v ^ 2)) / r ^ 2)) + 1 / 10)) := by
    simpa only [hend, show t.val - (t.val - v ^ 2) = v ^ 2 by ring, mul_div_assoc]
      using hinside
  obtain ⟨W, _hbranch, hWcontact, hWspace, hWtime, hWmin, hWdiff, hWlap, hWheat⟩ :=
    H.exists_weighted_physical_history_support_on_half_seed_clock A 3 hA (by norm_num)
      first last hle t.val (3 / a₀) hv hpast gamma U F hU hqU hFC2 hFvalue hcostCurve
      hupper hgradient hclockJet (1 / (2 * v)) hlap r hr hhalf hroomCurve O hSeedRicci
      hinsideCurve (by
        have h := hlocalMin
        rw [← hstart', ← hend'] at h
        exact h)
  have herror : 2 * v * (1 / (2 * v)) = 1 := by field_simp [hv.ne']
  simp only [hstart', hend', herror, show (6 : ℝ) + 1 = 7 by norm_num]
    at hWcontact hWspace hWtime hWmin hWdiff hWlap hWheat
  let t0 := t.val - v ^ 2
  let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
    (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
      A * (1 - 2 * ((t.val - s) / r ^ 2))
  let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
    DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
      (2 * Real.sqrt (t.val - s) *
        (H.regularizedCost first last hle t.val (3 / a₀) 0
          (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
  have hWheat' : -(C / r ^ 2) * actualWeighted t0 q -
      (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
      deriv (fun s => W (q, s)) t0 -
        laplacian (LeviCivita g) g (fun y => W (y, t0)) q := by
    simpa only [C, add_assoc] using hWheat
  let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
  let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
    (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
  let m : ℝ → ℝ := fun w => (M w).untopD 0
  have hclockCont : ContinuousAt (fun w : ℝ => t.val - w ^ 2) v := by fun_prop
  have hpastNear : ∀ᶠ w in 𝓝 v,
      t.val - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) :=
    hclockCont.eventually (Ioo_mem_nhds hpast.1 hpast.2)
  have hseedMargin : (aSeed : ℝ) < t.val - v ^ 2 := by
    rw [hSeedClock]
    nlinarith only [hhalf, hr2]
  have hseedNear : ∀ᶠ w in 𝓝 v, (aSeed : ℝ) < t.val - w ^ 2 :=
    hclockCont.eventually (Ioi_mem_nhds hseedMargin)
  have hMstage : ∀ᶠ w in 𝓝 v, M w = Mstage w := by
    filter_upwards [hpastNear, hseedNear] with w hpw hsw
    let aw : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - w ^ 2, aSeed.property.1.trans hsw.le,
        (sub_le_self t.val (sq_nonneg w)).trans t.property.2⟩
    have hawt : aw ≤ t := sub_le_self t.val (sq_nonneg w)
    have hawseed : aSeed ≤ aw := hsw.le
    have hawDomain : (aw : ℝ) ∈ H.stageDomain first :=
      H.mem_stageDomain_of_mem_Ioo hpw
    have hstage : H.activeStage aw = first := (H.mem_stageDomain_iff aw first).mp hawDomain
    have hwhole (j : Fin (H.eventCount + 1))
        (hjs : H.activeStage aSeed ≤ j) (hjl : j ≤ last) (hj : j = first) :
        sInf (Set.range (H.physicalWeightedCost j last hjl t.val (3 / a₀) r A w x
          (seedTrace.point j hjs hjl))) = Mstage w := by
      subst j
      rfl
    dsimp only [M, tracedPhysicalWeightedMinimum]
    rw [dite_eq_left hsw.le]
    exact hwhole (H.activeStage aw) (H.activeStage_mono hawseed)
      (H.activeStage_mono hawt) hstage
  have h4v : 4 * v ^ 2 < t.val := by nlinarith only [hhalf, hT]
  have h4Cont : ContinuousAt (fun w : ℝ => 4 * w ^ 2) v := by fun_prop
  have h4Near : ∀ᶠ w in 𝓝 v, 4 * w ^ 2 < t.val :=
    h4Cont.eventually (Iio_mem_nhds h4v)
  have hclockNear : ∀ᶠ w in 𝓝 v, 0 < w ∧ w < 3 * r / 4 := Ioo_mem_nhds hv hvr
  have hnonnegative (w : ℝ) (hw : 0 < w) (hwr : w < 3 * r / 4)
      (h4w : 4 * w ^ 2 < t.val) (y : (H.stage first).Carrier) :
      (0 : WithTop ℝ) ≤ H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O y := by
    unfold physicalWeightedCost
    dsimp only
    split_ifs with hins
    · have harg : (riemannianEDistOf (H.stageMetric first (t.val - w ^ 2)) O y).toReal / r -
          A * (1 - 2 * w ^ 2 / r ^ 2) < 1 / 10 := by
        have hd := ENNReal.toReal_lt_of_lt_ofReal hins
        apply (sub_lt_iff_lt_add).mpr
        apply (div_lt_iff₀ hr).mpr
        nlinarith only [hd]
      have hphi := DifferentialGeometry.Analysis.SingularBarrier.pos harg
      generalize hc : H.regularizedCost first last hle t.val (3 / a₀) 0 w x y = cost
      cases cost using WithTop.recTopCoe with
      | top => simp only [WithTop.map_top]; exact le_top
      | coe ell =>
        have hlow := H.regularizedCost_ge_neg_clock_of_recent records ha₀ hfixed hscalar
          first last hle t.val w hw h4w x y
        rw [hc] at hlow
        have hlowReal : -w ≤ ell := WithTop.coe_le_coe.mp hlow
        have hroom : 0 ≤ ell + r := by linarith only [hlowReal, hwr, hr]
        have hz : 0 ≤ 2 * w * ell + 2 * r * w := by
          have hh := mul_nonneg (show 0 ≤ 2 * w by positivity) hroom
          nlinarith only [hh]
        rw [WithTop.map_coe]
        exact WithTop.coe_le_coe.mpr (mul_nonneg hphi.le hz)
    · exact le_top
  have hBdd (w : ℝ) (hw : 0 < w) (hwr : w < 3 * r / 4) (h4w : 4 * w ^ 2 < t.val) :
      BddBelow (Set.range (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hnonnegative w hw hwr h4w y
  have hRange (w : ℝ) : (Set.range
      (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O)).Nonempty :=
    ⟨_, Set.mem_range_self q⟩
  have hValue (w : ℝ) (hw : 0 < w)
      (hinsidew : riemannianEDistOf (H.stageMetric first (t.val - w ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * w ^ 2 / r ^ 2) + 1 / 10)))
      (hcostw : H.regularizedCost first last hle t.val (3 / a₀) 0 w x q ≠ ⊤) :
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O q =
        (actualWeighted (t.val - w ^ 2) q : WithTop ℝ) := by
    obtain ⟨ell, hell⟩ := WithTop.ne_top_iff_exists.mp hcostw
    unfold physicalWeightedCost
    rw [ite_eq_left hinsidew, ← hell, WithTop.map_coe]
    apply congrArg (fun z : ℝ => (z : WithTop ℝ))
    simp only [actualWeighted, actualArg,
      show t.val - (t.val - w ^ 2) = w ^ 2 by ring, Real.sqrt_sq hw.le,
      ← hell, WithTop.untopD_coe, mul_div_assoc]
  have hcostne : H.regularizedCost first last hle t.val (3 / a₀) 0 v x q ≠ ⊤ := by
    rw [hcost]
    exact WithTop.coe_ne_top
  have hMstagev : Mstage v = (actualWeighted t0 q : WithTop ℝ) := by
    have hupperM : Mstage v ≤ H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q :=
      csInf_le (hBdd v hv hvr h4v) (Set.mem_range_self q)
    have hlowerM : H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤ Mstage v := by
      apply le_csInf (hRange v)
      rintro _ ⟨y, rfl⟩
      exact hminimum y
    exact (le_antisymm hupperM hlowerM).trans (hValue v hv hinside hcostne)
  have hMv : M v = (actualWeighted t0 q : WithTop ℝ) :=
    (Filter.EventuallyEq.eq_of_nhds hMstage).trans hMstagev
  have hmv : m v = actualWeighted t0 q := by
    dsimp only [m]
    rw [hMv]
    rfl
  obtain ⟨G, hGmetric⟩ := H.exists_stage_incomingSlab_metric first (hpast.1.trans hpast.2)
  have htG : t0 ∈ (RealTimeInterval.closedOpen (H.time first)
      (H.stageEndTime first) G.lt).regular := hpast
  have hcomplete : RiemannianMetricComplete (I := ThreeModel) (G.flow.base.metric t0) :=
    RiemannianMetricComplete.of_compact _
  have hmetricCont := DifferentialGeometry.Geometry.Riemannian.continuousAt_riemannianEDistOf
    G.flow.base.metric
    G.equation.smoothMetric.metricTensor_cont
    ((RealTimeInterval.closedOpen _ _ G.lt).regular_mem_nhds htG) hcomplete O q
  have hdistCont : ContinuousAt
      (fun w : ℝ => riemannianEDistOf (H.stageMetric first (t.val - w ^ 2)) O q) v := by
    have hcomp : ContinuousAt
        (fun w : ℝ => riemannianEDistOf (G.flow.base.metric (t.val - w ^ 2)) O q) v :=
      ContinuousAt.comp
        (g := fun p : ℝ × (H.stage first).Carrier =>
          riemannianEDistOf (G.flow.base.metric p.1) O p.2)
        (f := fun w : ℝ => (t.val - w ^ 2, q)) (x := v) hmetricCont
        (hclockCont.prodMk continuousAt_const)
    simpa only [hGmetric] using hcomp
  have hthresholdCont : ContinuousAt
      (fun w : ℝ => ENNReal.ofReal (r * (A * (1 - 2 * w ^ 2 / r ^ 2) + 1 / 10))) v := by
    have hreal : ContinuousAt (fun w : ℝ => r * (A * (1 - 2 * w ^ 2 / r ^ 2) + 1 / 10)) v := by
      fun_prop
    exact ENNReal.continuous_ofReal.continuousAt.comp hreal
  have hinsideNear := hdistCont.eventually_lt hthresholdCont hinside
  have hUNear : ∀ᶠ w in 𝓝 v, (q, w) ∈ U :=
    (continuousAt_const.prodMk continuousAt_id).eventually (hU.mem_nhds hqU')
  have hWNear : ∀ᶠ w in 𝓝 v,
      actualWeighted (t.val - w ^ 2) q ≤ W (q, t.val - w ^ 2) :=
    hclockCont.eventually hWtime
  have hNear : ∀ᶠ w in 𝓝 v,
      M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2) := by
    filter_upwards [hinsideNear, hUNear, hclockNear, h4Near, hWNear, hMstage]
      with w hins hUw hw h4w hWw hStage
    have hcostw : H.regularizedCost first last hle t.val (3 / a₀) 0 w x q ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (hupper' (q, w) hUw)
    have hMupper : M w ≤ (actualWeighted (t.val - w ^ 2) q : WithTop ℝ) := by
      rw [hStage]
      exact (csInf_le (hBdd w hw.1 hw.2 h4w) (Set.mem_range_self q)).trans_eq
        (hValue w hw.1 hins hcostw)
    have hMfin : M w ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hMupper
    have hMnonneg : (0 : WithTop ℝ) ≤ M w := by
      rw [hStage]
      apply le_csInf (hRange w)
      rintro _ ⟨y, rfl⟩
      exact hnonnegative w hw.1 hw.2 h4w y
    obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hMfin
    have hmw : m w = value := by
      dsimp only [m]
      rw [← hvalue]
      rfl
    rw [← hvalue] at hMnonneg hMupper
    refine ⟨hMfin, ?_, ?_⟩
    · rw [hmw]
      exact WithTop.coe_le_coe.mp hMnonneg
    · rw [hmw]
      exact (WithTop.coe_le_coe.mp hMupper).trans hWw
  have harg : actualArg t0 q < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hinside
    dsimp only [actualArg, t0]
    rw [show t.val - (t.val - v ^ 2) = v ^ 2 by ring]
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    exact hd.trans_eq (by ring)
  have hphi := DifferentialGeometry.Analysis.SingularBarrier.pos harg
  have hmformula : m v = 2 * v *
      DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) * (L + r) := by
    rw [hmv]
    dsimp only [actualWeighted]
    rw [show t.val - t0 = v ^ 2 by dsimp only [t0]; ring, Real.sqrt_sq hv.le, hcost]
    simp only [WithTop.untopD_coe]
    ring
  have hLfloor : -(2 * v ^ 3 / r ^ 2) ≤ L := by
    have hh := H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀ hfixed hscalar
      first last hle hr hv.le hhalf hT x q
    rw [hcost] at hh
    exact (le_of_eq (by ring)).trans (WithTop.coe_le_coe.mp hh)
  have hContactW : W (q, t.val - v ^ 2) = m v := hWcontact.trans hmv.symm
  have hUpperW : ∀ᶠ w in 𝓝[>] v, m w ≤ W (q, t.val - w ^ 2) :=
    (hNear.mono fun _ hw => hw.2.2).filter_mono nhdsWithin_le_nhds
  have hHeat : -(C / r ^ 2) * m v -
      (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
      deriv (fun s => W (q, s)) (t.val - v ^ 2) := by
    rw [hmv]
    linarith only [hWheat', hWlap]
  obtain ⟨psi, d, hpsiContact, hpsiUpper, hpsiDeriv, hd⟩ :=
    exists_nonpositive_clock_upper_support t.val r C v L
      (DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q))
      m (fun s => W (q, s)) hr hv hhalf hphi hLfloor hmformula hContactW hUpperW hWdiff hHeat
  exact ⟨L, hcost, hLbound, hLact, hinside,
    gamma, hgamma, hgammaAC, hgammaInt, hstart, hend, hnodes, hattain.trans hcost, hcross,
    U, F, hU, hqU', hFC2, hFcontact, hupper', hgradient', hclockJet', hlap', hfinite,
    hlocalMin, W, hWcontact, hWspace, hWtime, hWmin, hWdiff, hWlap, hWheat',
    hMstage, hMv, hmv, hNear, psi, d, hpsiContact, hpsiUpper, hpsiDeriv, hd⟩

theorem distinct_pole_initializer_receives_half_clock_bootstrap_support
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P₀ g₀ H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ (Aact E rTerm qDeriv ρ : ℝ) (Cderiv : ℝ≥0),
      0 < E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
    ∃ (m₀ : ℕ) (R₀ ε₀ δ₀ : ℝ), 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ →
      (∀ i : Fin H.eventCount,
        parameters.recenterConstant * parameters.delta (H.time i.succ) ≤ 1 / 2) →
      (∀ i : Fin H.eventCount, parameters.delta (H.time i.succ) ≤ δ₀) →
      (∀ i : Fin H.eventCount, parameters.neckRadius (H.time i.succ) ≤ ρ) →
    ∀ (_records : ∀ i, GeometricCutoffRecord H i parameters)
      (_identification : InitialIdentification P₀ g₀ H)
      (t : Icc (0 : ℝ) H.horizon),
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
    ∀ (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
      H.isParabolicallyRmControlledBall t x rTerm →
      H.time (H.activeStage t) < t.val →
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x < ENNReal.ofReal (A * r) →
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    D * r ≤ Aact →
    ∃ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 ∧
      ∃ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono hSeedTime) p,
        seedTrace.isRmControlled (hat := hSeedTime) r ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        Tendsto (fun w : ℝ => m w / w) (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) ∧
        ∀ᶠ v in 𝓝[>] (0 : ℝ),
          0 < v ∧ v ≤ E ∧ v ^ 2 ≤ r ^ 2 / 2 ∧ M v ≠ ⊤ ∧
          ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
            (a : ℝ) = t.val - v ^ 2 ∧ H.activeStage a = H.activeStage t ∧
            t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) ∧
            let first := H.activeStage a
            let last := H.activeStage t
            let hle := H.activeStage_mono hat
            let O := seedTrace.point first (H.activeStage_mono has) hle
            ∃ (q : (H.stage first).Carrier) (L : ℝ),
              H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
              (∀ y : (H.stage first).Carrier,
                H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
                  H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) ∧
              H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
                ((2 * r * v * D : ℝ) : WithTop ℝ) ∧
              ∃ psi : ℝ → ℝ, ∃ d : ℝ,
                psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0 := by
  classical
  obtain ⟨a₀, ha₀, hInitial, hPrepare⟩ :=
    exists_uniform_distinct_pole_half_clock_bootstrap_support P₀ g₀
  refine ⟨a₀, ha₀, hInitial, ?_⟩
  intro Aact E rTerm qDeriv ρ Cderiv hE hrTerm hqDeriv hρ
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hSupport⟩ :=
    hPrepare Aact E rTerm qDeriv ρ Cderiv hE.le hrTerm hqDeriv hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hR hε hrecent hδ hneck records identification t hderiv
    p x r A hr hA hT hseed htest hpole hdist C D hfit
  obtain ⟨hfixed, hscalar⟩ := hInitial H identification
  obtain ⟨_hrSeed, aSeed, hSeedTime, hSeedClock, hTraces⟩ := hseed
  have hpball : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨seedTrace, htrace⟩ := hTraces p hpball
  have hseedAgain : H.isParabolicallyRmControlledBall t p r :=
    ⟨hr, aSeed, hSeedTime, hSeedClock, hTraces⟩
  let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
  let m : ℝ → ℝ := fun w => (M w).untopD 0
  let f : ℝ → ℝ := fun w =>
    Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
  obtain ⟨⟨e, he, her, _heTerm, heage, _hecube, hminima⟩, hfinite, hlimit⟩ :=
    H.exists_distinct_pole_initial_weighted_minimum_and_limit parameters records ha₀
      hfixed hscalar aSeed t hSeedTime p x r rTerm A hr hA hSeedClock seedTrace
      htest hT hpole hdist
  have hD : 1 < D := by
    dsimp only [D]
    linarith only [Real.exp_pos (C / 2 + 32 / Real.sqrt 2)]
  have hgap : 2 * r < 2 * r * D := by
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hD (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
  have hbootstrapNear : ∀ᶠ v in 𝓝[>] (0 : ℝ), m v / v < 2 * r * D :=
    hlimit.eventually (Iio_mem_nhds hgap)
  have hENear : ∀ᶠ v in 𝓝[>] (0 : ℝ), v < E :=
    nhdsWithin_le_nhds (Iio_mem_nhds hE)
  refine ⟨aSeed, hSeedTime, hSeedClock, seedTrace, htrace, hlimit, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT he, hbootstrapNear, hENear, hfinite]
    with v hv hbootstrapReal hvE hvFinite
  obtain ⟨a, has, hat, hclock, hstage, poleTrace, _hpTrace, _hplateau,
      action, _hC1, _hAC, _hcostSeed, _haction, q, L, value,
      hcost, _hinner, _hLaction, _hLroom, hWvalue, hMvalue, _hvaluePos,
      _hvalueLower, _hvalueUpper, hminimum⟩ := hminima v hv.1 hv.2
  let first := H.activeStage a
  let last := H.activeStage t
  let hle := H.activeStage_mono hat
  let O := seedTrace.point first (H.activeStage_mono has) hle
  have hhalf : v ^ 2 ≤ r ^ 2 / 2 := by
    have hvr : v ≤ r / 4 := hv.2.le.trans her
    have hh := pow_le_pow_left₀ hv.1.le hvr 2
    nlinarith only [hh, sq_nonneg r]
  have hpast : t.val - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
    dsimp only [first]
    rw [hstage]
    constructor
    · have hve := (pow_le_pow_left₀ hv.1.le hv.2.le 2).trans_lt heage
      linarith only [hve]
    · have htEnd := H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)
      nlinarith only [htEnd, sq_pos_of_pos hv.1]
  have hwindow (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
      (b : (H.event i).RetainedBoundaryIndex) : ((records i).static b).hasCanonicalWindow := by
    have hf' : last ≤ i.castSucc := by simpa only [first, last, hstage] using hf
    exact False.elim ((not_lt_of_ge (hl.trans hf')) i.castSucc_lt_succ)
  have hmv : m v = value := by
    dsimp only [m, M]
    rw [hMvalue]
    rfl
  have hbootstrap : H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
      ((2 * r * v * D : ℝ) : WithTop ℝ) := by
    rw [hWvalue]
    apply WithTop.coe_le_coe.mpr
    rw [hmv] at hbootstrapReal
    have hh := (div_lt_iff₀ hv.1).mp hbootstrapReal
    nlinarith only [hh]
  obtain ⟨_Lsupport, _hcostSupport, _hLbound, _hLact, _hinside,
      gamma, _hgamma, _hgammaAC, _hgammaInt, _hstart, hEnd,
      _hnodes, _hattain, _hcross, U, F, _hU, _hqU, _hFC2, _hFcontact,
      _hupper, _hgradient, _hclockJet, _hlap, _hfiniteSupport, _hlocalMin,
      W, _hWcontact, _hWspace, _hWtime, _hWmin, _hWdiff, _hWlap, _hWheat,
      _hStage, _hMv, _hmv, _hNear, psi, d, hpsiContact, hpsiUpper, hpsiDeriv, hd⟩ :=
    hSupport H parameters hm hR hε hrecent hδ hneck records identification t hderiv
      p x r A hr hA hT hseedAgain htest aSeed hSeedTime hSeedClock seedTrace hfit
      a has hat v hv.1 hvE.le hhalf hclock hpole hpast hwindow q hminimum hbootstrap
  exact ⟨hv.1, hvE.le, hhalf, hvFinite,
    a, has, hat, hclock, hstage, hpast, q, L, hcost, hminimum, hbootstrap,
    psi, d, hpsiContact, hpsiUpper, hpsiDeriv, hd⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
