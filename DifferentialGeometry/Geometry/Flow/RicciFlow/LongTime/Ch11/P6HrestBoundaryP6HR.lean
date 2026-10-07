import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeHIP6X2

/-!
# hrest 的有损边界支按位置重分（O-CH11-HREST G2，后缀 `_P6HR`）

P6SEL2 `hPN_of_pureClass_lateHI_P6X2` 的 `hrest`（与 P6SEL3 G4 的 `hrestS`，前缀多种子小曲率）的第二支
`∀ k, ¬ ∃ spatial witness` 丢了位置（来自 `exists_strictMono_interior_or_boundary_P6S`）。前缀里已有
`hsel : ¬Good`，故该支是冗余信息：本文件按位置**重新四分**（`exists_strictMono_position_P6S`）并证出
* event 内部子类 ⇒ 下标平移 `ψ (k+1)` 后交 event 支 `hev`（`k+1 < R`）；final 内部子类 ⇒ `hfinal`；
* stage 时刻子类：`time 0 = 0 < 1 ≤ aSeed ≤ σ` 排除 `m = 0` ⇒ `σ = time i.succ`
  （`exists_succ_of_eq_time_P6HR`）⇒ `hstage`；
* 视界子类：再二分（`exists_strictMono_or_P6HR`）——`time last = horizon`（seam）⇒ 落回 stage 子类；
  `time last < horizon = σ`（final slab 闭端点）⇒ `hhor`。
显式 binder（**PROVISIONAL**）只剩带完整位置的 **`hstage`**（`σ k = time (i k).succ`）与 **`hhor`**
（`time last < horizon ∧ σ k = horizon`）；`hev` / `hfinal` 由 P6SEL2 `eventBranch_lateHI_P6X2` 与本车道 G1
`finalBranch_lateHI_P6HR` 供给（G3 组装）。repair target 见
docs/geometrization/chapter8/design-C11-hrest-20261007.md §3。
陈述由 build-logs/scratch/O-CH11-HREST/mk_g2.py 从 `hrest` binder 文本生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- 二分鸽笼：任意 `P : ℕ → Prop` 有严格单调子列整条满足 `P` 或整条满足 `¬P`。 -/
theorem exists_strictMono_or_P6HR (P : ℕ → Prop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ((∀ k, P (φ k)) ∨ ∀ k, ¬ P (φ k)) := by
  by_cases h : (Set.ofPred P).Infinite
  · exact ⟨Nat.nth P, Nat.nth_strictMono h, Or.inl fun k => Nat.nth_mem_of_infinite h k⟩
  have h' : (Set.ofPred fun k => ¬ P k).Infinite := by
    intro hfin
    refine Set.infinite_univ (((Set.not_infinite.mp h).union hfin).subset fun n _ => ?_)
    by_cases hn : P n
    · exact Or.inl hn
    · exact Or.inr hn
  exact ⟨Nat.nth fun k => ¬ P k, Nat.nth_strictMono h',
    Or.inr fun k => Nat.nth_mem_of_infinite h' k⟩

/-- stage 时刻 `s = time m` 且 `0 < s` ⇒ `m` 是某个 event 的 `succ`（`time 0 = 0`）。 -/
theorem exists_succ_of_eq_time_P6HR (H : ObservedHistory.{u}) {s : ℝ} (hs : 0 < s)
    {m : Fin (H.eventCount + 1)} (h : s = H.time m) :
    ∃ i : Fin H.eventCount, s = H.time i.succ := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
  · rw [H.time_zero] at h
    linarith
  · exact ⟨i, h⟩

/-- **`hrest`（P6SEL2 形）⇐ event 支 + final 支 + `hstage` + `hhor`**：见文件头。 -/
theorem hrest_of_branches_P6HR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hev :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) → (∀ k : ℕ, (k : ℝ) + 1 < R k) → False)
    (hfinal :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) → False)
    (hstage :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, ∃ i : Fin (Kh k).eventCount, (σ k : ℝ) = (Kh k).time i.succ) → False)
    (hhor :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon ∧
          (σ k : ℝ) = (Kh k).horizon) → False) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii hcls
  have hσpos : ∀ k, 0 < (σ k : ℝ) := fun k => by
    have h' : (aSeed k : ℝ) ≤ σ k := has k
    linarith [h1 k]
  have key : ∀ φ : ℕ → ℕ, StrictMono φ →
      (((∀ k, ∃ j : Fin (Kh (φ k)).eventCount, (Kh (φ k)).time j.castSucc < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).time j.succ) ∧ ∀ k : ℕ, (k : ℝ) + 1 < R (φ k)) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).horizon) ∨
        (∀ k, ∃ i : Fin (Kh (φ k)).eventCount, (σ (φ k) : ℝ) = (Kh (φ k)).time i.succ) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (Kh (φ k)).horizon ∧
          (σ (φ k) : ℝ) = (Kh (φ k)).horizon)) → False := by
    intro φ hφ hcls'
    have hφt := hφ.tendsto_atTop
    have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hTc (φ k))
    have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R (φ k) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hRr (φ k))
    rcases hcls' with ⟨hev', hlt⟩ | hfin' | hst | hho
    · exact hev
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => seedTrace (φ k))
          (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k)) (fun k => hsT (φ k))
          (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k)) (fun k => hRpos (φ k))
          hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hev' hlt
    · exact hfinal
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => seedTrace (φ k))
          (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k)) (fun k => hsT (φ k))
          (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k)) (fun k => hRpos (φ k))
          hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hfin'
    · exact hstage
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => seedTrace (φ k))
          (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k)) (fun k => hsT (φ k))
          (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k)) (fun k => hRpos (φ k))
          hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hst
    · exact hhor
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => seedTrace (φ k))
          (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k)) (fun k => hsT (φ k))
          (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k)) (fun k => hRpos (φ k))
          hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hho
  rcases hcls with hfin | -
  · exact key id strictMono_id (Or.inr (Or.inl hfin))
  obtain ⟨ψ, hψ, h | h | h | h⟩ := exists_strictMono_position_P6S (Kh := Kh) σ
  · have hs : StrictMono fun k : ℕ => ψ (k + 1) :=
      hψ.comp fun a b hab => Nat.add_lt_add_right hab 1
    refine key (fun k => ψ (k + 1)) hs (Or.inl ⟨fun k => h (k + 1), fun k => ?_⟩)
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (ψ (k + 1) : ℝ) := by exact_mod_cast hψ.id_le (k + 1)
    have hk2 := hRr (ψ (k + 1))
    push_cast at hk1
    linarith
  · exact key ψ hψ (Or.inr (Or.inl h))
  · refine key ψ hψ (Or.inr (Or.inr (Or.inl fun k => ?_)))
    obtain ⟨m, hm⟩ := h k
    exact (Kh (ψ k)).exists_succ_of_eq_time_P6HR (hσpos (ψ k)) hm
  · obtain ⟨φ, hφ, h' | h'⟩ :=
      exists_strictMono_or_P6HR fun k =>
        (Kh (ψ k)).time (Fin.last (Kh (ψ k)).eventCount) < (Kh (ψ k)).horizon
    · exact key (fun k => ψ (φ k)) (hψ.comp hφ)
        (Or.inr (Or.inr (Or.inr fun k => ⟨h' k, h (φ k)⟩)))
    · refine key (fun k => ψ (φ k)) (hψ.comp hφ) (Or.inr (Or.inr (Or.inl fun k => ?_)))
      have hle := (Kh (ψ (φ k))).time_le_horizon
      have heq : (σ (ψ (φ k)) : ℝ) = (Kh (ψ (φ k))).time (Fin.last (Kh (ψ (φ k))).eventCount) :=
        (h (φ k)).trans (le_antisymm (not_lt.mp (h' k)) hle)
      exact (Kh (ψ (φ k))).exists_succ_of_eq_time_P6HR (hσpos (ψ (φ k))) heq

/-- **`hrestS`（P6SEL3 G4 形，前缀带种子小曲率）⇐ 四支**：同 `hrest_of_branches_P6HR`。 -/
theorem hrestS_of_branches_P6HR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hev :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) → (∀ k : ℕ, (k : ℝ) + 1 < R k) → False)
    (hfinal :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) → False)
    (hstage :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, ∃ i : Fin (Kh k).eventCount, (σ k : ℝ) = (Kh k).time i.succ) → False)
    (hhor :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon ∧
          (σ k : ℝ) = (Kh k).horizon) → False) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii hcls
  have hσpos : ∀ k, 0 < (σ k : ℝ) := fun k => by
    have h' : (aSeed k : ℝ) ≤ σ k := has k
    linarith [h1 k]
  have key : ∀ φ : ℕ → ℕ, StrictMono φ →
      (((∀ k, ∃ j : Fin (Kh (φ k)).eventCount, (Kh (φ k)).time j.castSucc < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).time j.succ) ∧ ∀ k : ℕ, (k : ℝ) + 1 < R (φ k)) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).horizon) ∨
        (∀ k, ∃ i : Fin (Kh (φ k)).eventCount, (σ (φ k) : ℝ) = (Kh (φ k)).time i.succ) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (Kh (φ k)).horizon ∧
          (σ (φ k) : ℝ) = (Kh (φ k)).horizon)) → False := by
    intro φ hφ hcls'
    have hφt := hφ.tendsto_atTop
    have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hTc (φ k))
    have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R (φ k) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hRr (φ k))
    rcases hcls' with ⟨hev', hlt⟩ | hfin' | hst | hho
    · exact hev
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
          (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
          (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
          (fun k => hRpos (φ k)) hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hev' hlt
    · exact hfinal
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
          (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
          (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
          (fun k => hRpos (φ k)) hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hfin'
    · exact hstage
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
          (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
          (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
          (fun k => hRpos (φ k)) hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hst
    · exact hhor
        (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
          (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
          (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
          (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
          (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
          (fun k => hRpos (φ k)) hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
          (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
          (hroom.comp hφt) (hradii.comp hφt) hho
  rcases hcls with hfin | -
  · exact key id strictMono_id (Or.inr (Or.inl hfin))
  obtain ⟨ψ, hψ, h | h | h | h⟩ := exists_strictMono_position_P6S (Kh := Kh) σ
  · have hs : StrictMono fun k : ℕ => ψ (k + 1) :=
      hψ.comp fun a b hab => Nat.add_lt_add_right hab 1
    refine key (fun k => ψ (k + 1)) hs (Or.inl ⟨fun k => h (k + 1), fun k => ?_⟩)
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (ψ (k + 1) : ℝ) := by exact_mod_cast hψ.id_le (k + 1)
    have hk2 := hRr (ψ (k + 1))
    push_cast at hk1
    linarith
  · exact key ψ hψ (Or.inr (Or.inl h))
  · refine key ψ hψ (Or.inr (Or.inr (Or.inl fun k => ?_)))
    obtain ⟨m, hm⟩ := h k
    exact (Kh (ψ k)).exists_succ_of_eq_time_P6HR (hσpos (ψ k)) hm
  · obtain ⟨φ, hφ, h' | h'⟩ :=
      exists_strictMono_or_P6HR fun k =>
        (Kh (ψ k)).time (Fin.last (Kh (ψ k)).eventCount) < (Kh (ψ k)).horizon
    · exact key (fun k => ψ (φ k)) (hψ.comp hφ)
        (Or.inr (Or.inr (Or.inr fun k => ⟨h' k, h (φ k)⟩)))
    · refine key (fun k => ψ (φ k)) (hψ.comp hφ) (Or.inr (Or.inr (Or.inl fun k => ?_)))
      have hle := (Kh (ψ (φ k))).time_le_horizon
      have heq : (σ (ψ (φ k)) : ℝ) = (Kh (ψ (φ k))).time (Fin.last (Kh (ψ (φ k))).eventCount) :=
        (h (φ k)).trans (le_antisymm (not_lt.mp (h' k)) hle)
      exact (Kh (ψ (φ k))).exists_succ_of_eq_time_P6HR (hσpos (ψ (φ k))) heq

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
