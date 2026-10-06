import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.Length

/-!
# IMS04 / G3（S-A10-BOUNDARY, suffix `_BD`）：prescribed 曲线的 velocity bound `|∂_t γ_t|`

`PersistentHyperbolicCores` **有** 时间导数信息：`static_patches`（`PersistentModelPatch`）在每个
`x ∈ domain i t` 处给出邻域上的光滑 `map : ℝ × H.Carrier → backwardSurvivorDomain`，其 `speed` 字段是
`g(stage, t)(∂_t track, ∂_t track) < α(t)² / t`（`α = accuracy`，`track = backwardSurvivorMap ∘ map`，
`stage = activeStage t`）。所以不是 obstruction：对 `γ_t(s) = map i t (cuspMap port (loop s, halfZero))`，
取 `x = cuspMap port (loop s, halfZero) ∈ ball ⊆ domain i t`（G2 的 `slice_mem_ball_BD`）即可。

`velocity_transported_BD`：存在 patch `P`，使 `track (t, x)` 与 `γ_t(s)` HEq（`agrees`），且
`|∂_t track|²_{g(stage,t)} < accuracy t ^ 2 / t`，等价地 `|∂_t track|·√t < accuracy t`（parabolic
scaling 下的速度 `→ 0`）。度量是 patch 的 active stage 度量
`(F.tower.history P.n).toHistory.stageMetric (activeStage t) t`；它与 `postMetric F.observation t`
的 HEq 桥（`SamePresentation`）不在本文件（见 DELIVERIES 的接口备注）。
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

/-- 纯算术：`Q < a² / t` ⇒ `√Q · √t < a`（`Q ≥ 0`，`a, t > 0`）。 -/
theorem sqrt_mul_sqrt_lt_of_lt_div_BD {Q a t : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) (ht : 0 < t)
    (h : Q < a ^ 2 / t) : Real.sqrt Q * Real.sqrt t < a := by
  rw [← Real.sqrt_mul hQ, Real.sqrt_lt' ha]
  exact (lt_div_iff₀ ht).mp h

/-- **G3 主定理**：`γ_t(s)` 处的 time-direction velocity bound（经 `static_patches`）。

结论三部分（`let` 内）：`track (t, x₀)` 就是 `γ_t(s)`（HEq）；`g(stage,t)(v, v) < acc² / t`（patch 的
`speed` 原样）；`√(g(v,v))·√t < acc t`（scaled 形式）。 -/
theorem PrescribedCuspMeridian.velocity_transported_BD (M : PrescribedCuspMeridian cores)
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
        HEq (track (t, (M.exterior.truncation M.model).cuspMap M.port
          (loopLift M.loop s, halfZero))) (loopLift (M.transported t ht) s) ∧
        (history.stageMetric (history.activeStage ⟨t, hI⟩) t).inner
          (track (t, (M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)))
          v v < cores.accuracy t ^ 2 / t ∧
        Real.sqrt ((history.stageMetric (history.activeStage ⟨t, hI⟩) t).inner
          (track (t, (M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)))
          v v) * Real.sqrt t < cores.accuracy t := by
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have htpos : 0 < t := cores.start_pos.trans_le ht'
  have hball := M.slice_mem_ball_BD t ht s
  have hdomain := cores.advertised_ball M.model t ht' hball
  obtain ⟨P⟩ := cores.static_patches M.model t ht' _ hdomain
  have hm : t ∈ Ioo P.a P.b := ⟨P.before, P.after⟩
  have hI : t ∈ Icc (0 : ℝ) (F.tower.history P.n).horizon :=
    ⟨P.a_nonneg.trans P.before.le, P.after.le.trans P.horizon⟩
  refine ⟨P, hI, hm, ?_⟩
  have hagree := P.agrees ⟨t, hI⟩ hm ht' _ P.mem_neighborhood
  have hsp := P.speed ⟨t, hI⟩ hm ht' _ P.mem_neighborhood
  have heq : (loopLift (M.transported t ht) s) =
      cores.map M.model t ht' ((M.exterior.truncation M.model).cuspMap M.port
        (loopLift M.loop s, halfZero)) := congrFun (M.transported_eq_comp_BD t ht) s
  refine ⟨hagree.trans (heq_of_eq heq.symm), hsp, ?_⟩
  exact sqrt_mul_sqrt_lt_of_lt_div_BD (metric_inner_self_nonneg _ _ _)
    (cores.accuracy_pos t ht') htpos hsp

/-- **consumer**：`accuracy → 0` ⇒ parabolic scaling 下的速度任意小：`|∂_t track|·√t < ε`（`t` 够大）。

用到 `velocity_transported_BD` 的第三部分与 `cores.accuracy_decay`；这就是 IMS09 flux 项里
`sup |∂_t γ_t| · L(γ_t) ≤ (acc/√t) · ℓ√t = ℓ · acc → 0` 的速度因子。 -/
theorem PrescribedCuspMeridian.eventually_velocity_small_BD (M : PrescribedCuspMeridian cores)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, M.exterior.start ≤ t → T ≤ t → ∀ s : ℝ,
      ∃ P : PersistentModelPatch F (cores.model M.model) cores.start cores.accuracy
          (cores.domain M.model) (cores.map M.model) t
          ((M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)),
        ∃ (hI : t ∈ Icc (0 : ℝ) (F.tower.history P.n).horizon) (hm : t ∈ Ioo P.a P.b),
          let history := (F.tower.history P.n).toHistory;
          let track := history.backwardSurvivorMap P.first P.last P.ordered
            (history.activeStage ⟨t, hI⟩) (P.stages ⟨t, hI⟩ hm).1 (P.stages ⟨t, hI⟩ hm).2 ∘ P.map;
          let v := mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) track (t,
            (M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)) (1, 0);
          Real.sqrt ((history.stageMetric (history.activeStage ⟨t, hI⟩) t).inner
            (track (t, (M.exterior.truncation M.model).cuspMap M.port
              (loopLift M.loop s, halfZero))) v v) * Real.sqrt t < ε := by
  obtain ⟨T, hT⟩ := cores.accuracy_decay ε hε
  refine ⟨T, fun t ht hTt s => ?_⟩
  obtain ⟨P, hI, hm, h⟩ := M.velocity_transported_BD t ht s
  exact ⟨P, hI, hm, h.2.2.trans (hT t hTt)⟩

end GC.LongTime
