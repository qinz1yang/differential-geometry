import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.Velocity
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageGeneralST

/-!
# IMS04 / G3'（S-A10-BOUNDARY, suffix `_BD`）：velocity bound 改写到 `postMetric F.observation t`

G3 的 `velocity_transported_BD` 里速度界是在 patch 的 active-stage 度量
`(F.tower.history P.n).toHistory.stageMetric (activeStage t) t` 下给的。S-A14-STATIC G5
（`LongTime/PostStageGeneralST.lean`）给出一般 `t`、一般 `n ≥ t` 的 `postStage` / `postMetric` 与
`stageAt` / `stageMetric` 的对齐。本文件用它把速度界搬到 `postMetric F.observation t` 与
`γ_t(s) = loopLift (M.transported t ht) s` 上，于是与 G2 的 `speed_transported_le_BD`
（同一度量、同一点）可以直接相乘（IMS09 flux 被积函数 `|∂_tγ|·|γ'|`）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G3' 主定理**：`γ_t(s)` 处，patch 的 time-direction 速度 `v`（`∂_t track`）在
`postMetric F.observation t` 下满足 `g(t)(v, v) < acc² / t` 与 `√(g(t)(v,v))·√t < acc t`。 -/
theorem PrescribedCuspMeridian.velocity_postMetric_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ) :
    ∃ P : PersistentModelPatch F (cores.model M.model) cores.start cores.accuracy
        (cores.domain M.model) (cores.map M.model) t
        ((M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)),
      ∃ (hI : t ∈ Icc (0 : ℝ) (F.tower.history P.n).horizon) (hm : t ∈ Ioo P.a P.b),
        let history := (F.tower.history P.n).toHistory;
        let track := history.backwardSurvivorMap P.first P.last P.ordered
          (history.activeStage ⟨t, hI⟩) (P.stages ⟨t, hI⟩ hm).1 (P.stages ⟨t, hI⟩ hm).2 ∘ P.map;
        let v := mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) track (t,
          (M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)) (1, 0);
        (postMetric F.observation t).inner (loopLift (M.transported t ht) s) v v <
            cores.accuracy t ^ 2 / t ∧
          Real.sqrt ((postMetric F.observation t).inner (loopLift (M.transported t ht) s) v v) *
            Real.sqrt t < cores.accuracy t := by
  obtain ⟨P, hI, hm, hheq, hsp, hscaled⟩ := M.velocity_transported_BD t ht s
  refine ⟨P, hI, hm, ?_⟩
  have hinner := inner_eq_of_heq_ST (postStage_eq_stageAt_tower_ST F P.n ⟨t, hI⟩)
    (postMetric_heq_stageMetric_tower_ST F P.n ⟨t, hI⟩) (loopLift (M.transported t ht) s)
  intro history track v
  have hcast : cast (congrArg OrientedThreeStage.Carrier
      (postStage_eq_stageAt_tower_ST F P.n ⟨t, hI⟩)) (loopLift (M.transported t ht) s) =
      track (t, (M.exterior.truncation M.model).cuspMap M.port
        (loopLift M.loop s, halfZero)) := cast_eq_iff_heq.mpr hheq.symm
  rw [hinner v v, hcast]
  exact ⟨hsp, hscaled⟩

/-- 纯算术：`a·r < acc`，`sp ≤ r·c`，`a, c ≥ 0` ⇒ `a·sp ≤ acc·c`。 -/
theorem mul_le_of_scaled_BD {a sp r acc c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h1 : a * r < acc)
    (hsp : sp ≤ r * c) : a * sp ≤ acc * c := by
  calc a * sp ≤ a * (r * c) := mul_le_mul_of_nonneg_left hsp ha
    _ = (a * r) * c := by ring
    _ ≤ acc * c := mul_le_mul_of_nonneg_right h1.le hc

/-- **G3'' flux 被积函数界**：同一度量 `postMetric F.observation t`、同一点 `γ_t(s)` 上
`|∂_t γ|·|γ'| ≤ acc t · √(1 + acc t) · L`（`L < 1` 来自 `short`，G2 的 speed 界乘 G3' 的速度界；
`√t` 恰好消掉）。 -/
theorem PrescribedCuspMeridian.flux_integrand_le_BD (M : PrescribedCuspMeridian cores) :
    ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ),
      ∃ P : PersistentModelPatch F (cores.model M.model) cores.start cores.accuracy
          (cores.domain M.model) (cores.map M.model) t
          ((M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)),
        ∃ (hI : t ∈ Icc (0 : ℝ) (F.tower.history P.n).horizon) (hm : t ∈ Ioo P.a P.b),
          let history := (F.tower.history P.n).toHistory;
          let track := history.backwardSurvivorMap P.first P.last P.ordered
            (history.activeStage ⟨t, hI⟩) (P.stages ⟨t, hI⟩ hm).1 (P.stages ⟨t, hI⟩ hm).2 ∘ P.map;
          let v := mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) track (t,
            (M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)) (1, 0);
          Real.sqrt ((postMetric F.observation t).inner (loopLift (M.transported t ht) s) v v) *
            riemannianCurveSpeed (postMetric F.observation t) (loopLift (M.transported t ht)) s ≤
          cores.accuracy t * Real.sqrt (1 + cores.accuracy t) * L := by
  obtain ⟨L, hL0, hL1, hsp⟩ := M.speed_transported_le_BD
  refine ⟨L, hL0, hL1, fun t ht s => ?_⟩
  obtain ⟨P, hI, hm, h1, h2⟩ := M.velocity_postMetric_BD t ht s
  refine ⟨P, hI, hm, ?_⟩
  have htpos : 0 < t := cores.start_pos.trans_le (M.exterior.after_cores.trans ht)
  have hspeed := hsp t ht s
  rw [Real.sqrt_mul htpos.le, mul_assoc] at hspeed
  rw [mul_assoc]
  exact mul_le_of_scaled_BD (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hL0.le) h2 hspeed

end GC.LongTime
