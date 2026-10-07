import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceChainCapture_P6L

/-!
# L6-A spine 1(d)：`BoundedCurvatureAtDistanceSlice:23/73` 的 footprint 局部化（`_P6L`）

原 `ST/BoundedCurvatureAtDistanceSlice.lean` 的 private `:23`
`nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux` 与 `:73`
`chain_traces_of_not_capWindowPoint_of_incomingSlab`（L6 `htrace` 的供给方）。导数界只经 `BTCC:409`
在链球点及其 backward trace 上用 [V] ⇒ 改调 O-CH11-P6A3 G1 `BTCC:409_P6L`：
* `:23_P6L`：区域 `U`（stage `k`）、链球成员 `hchainU`；`hslabs`/`hfinal` 照 `BTCC:409_P6L` 形。
* `:73_P6L`：`U`（last stage）放 `hslabs` 前；`hslabs` 为 RetainedCoreHistory footprint 形（P6C 约定的
  单 history 版，同 TL:47_P6L 的 `hderiv`）、`hderG` 限于 `U`；rebase 链 `pc` 的成员 `hchainUc`；
  结论（= L6 `htrace` 形）在 `0 < δ k` 后加链球成员前提（与 P6C2 `_P6Lm` 的 `htrace` 同位）。
  拼接链 `P` 的成员 `hchainUP` 照 `hspaceP` 的分支写；`extendHorizon` 后的 trace 照原文以
  `⟨A.point, A.endpoint_eq, A.crossing⟩` 转回 `H`。
私有 `:64` `sum_range_ite_add` 复制为 `_P6L`。证明体照抄；结论其余逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory


private theorem nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_P6L
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (k : Fin (H.eventCount + 1)) (hk : H.toHistory.activeStage t = k)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage k).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ j ≤ N, 0 < δ j)
    (hchain : ∀ j < N, pc (j + 1) ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j))
    (U : Set (H.toHistory.stage k).Carrier)
    (hchainU : ∀ j ≤ N, ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ k),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ k,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first k hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ),
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y : (H.toHistory.stage (Fin.last H.eventCount)).Carrier, ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t,
      qcan < ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤ Ctime * ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ j ≤ N, ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      metricScalarAt (H.toHistory.stageMetric k t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap)
    (hnot : ¬ H.CapWindowPoint records k (pc 0) t Dcap θcap) :
    ∀ j ≤ N, ∀ z ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u) k
        (hk ▸ H.toHistory.activeStage_mono hut) z) := by
  subst hk
  intro j hj z hz
  by_contra hne
  exact hnot (H.capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_P6L records
    hcan hscale hacc hphi hpinch hut h hlastA hfinalPinch pc δ hδ hchain z ⟨j, hj, hz⟩
    (not_nonempty_iff.mp hne) U hchainU hslabs hfinal hM hqcan hspace htime hDstar hDmodel hθ
    hwin)

private theorem sum_range_ite_add_P6L {Nc N : ℕ} (a b : ℕ → ℝ) :
    ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then a j else b (j - Nc)) =
      ∑ j ∈ Finset.range Nc, a j + ∑ j ∈ Finset.range (N + 1), b j := by
  rw [show Nc + N + 1 = Nc + (N + 1) by ring, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- **`_P6L`**：原 `RetainedCoreHistory.chain_traces_of_not_capWindowPoint_of_incomingSlab`（`SL:73`）。
改动：区域 `U`（last stage）放 `hslabs` 前；`hslabs` footprint 形（RC 序列约定的单 history 版，trace 名
`B`）、`hderG` 限于 `U`；rebase 链成员前提 `hchainUc`；结论的 `∀ N pp δ …` 在 `0 < δ k` 后加
链球成员前提 `∀ k ≤ N, ∀ z ∈ B_t(pp k, δ k), z ∈ U`（rev1a C2.2；与 P6C2 `_P6Lm` 的 `htrace` 同位）。
证明体照抄；结论其余逐字。 -/
theorem chain_traces_of_not_capWindowPoint_of_incomingSlab_P6L
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {t : ℝ} (ht : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    {p : CutoffParameters} (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan Dcap Dstar θ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hpinchG : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi)
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (hslabs : ∀ j : Fin H.eventCount,
      ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      qcan < (H.toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
        (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderG : ∀ y ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t,
      qcan < G.flow.scalar v y →
      |derivWithin (fun w => G.flow.scalar w y) (Iic v) v| ≤ Ctime * G.flow.scalar v y ^ 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (hnot : ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θ)
    {Nc : ℕ} (pc : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δc : ℕ → ℝ) (hpc0 : pc 0 = y)
    (hδc : ∀ k < Nc, 0 < δc k)
    (hchainc : ∀ k < Nc, pc (k + 1) ∈
      riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t) (pc k) (δc k))
    (hchainUc : ∀ k < Nc, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
      (pc k) (δc k), z ∈ U)
    {Mc lamc : ℝ}
    (hMc : ∀ k < Nc, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
      (pc k) (δc k), (G.closedPrefix t ht hts).flow.scalar t z ≤ Mc)
    (hlamc : ∑ k ∈ Finset.range Nc, δc k ≤ lamc) :
    ∀ (N : ℕ) (pp : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ) (M τ : ℝ),
      pp 0 = pc Nc → (∀ k ≤ N, 0 < δ k) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k), z ∈ U) →
      (∀ k < N, pp (k + 1) ∈
        riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t) (pp k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k), (G.closedPrefix t ht hts).flow.scalar t z ≤ M) →
      Mc ≤ M → qcan ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ t →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
          (lamc + ∑ k ∈ Finset.range (N + 1), δ k) < Dcap →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ t - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z) := by
  intro N pp δ M τ h0 hδ hUpp hch hb hMcM hq hM1 hτ0 hτt hC h4 hD k hk z hz
  have hHt : H.horizon ≤ t := hend ▸ ht.le
  set S := G.closedPrefix t ht hts with hSdef
  set H' := H.extendHorizon t hHt S hG with hH'def
  have hh : H'.time (Fin.last H'.eventCount) < H'.horizon := ht
  let t' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t, H'.horizon_nonneg, le_rfl⟩
  have hu0 : 0 ≤ t - τ := by linarith
  let u' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t - τ, hu0, by
    change t - τ ≤ t
    linarith⟩
  have hut : u' ≤ t' := by
    change t - τ ≤ t
    linarith
  have hlastA : H'.toHistory.activeStage t' = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last hHt S hG t' ht.le
  obtain ⟨h, hfp⟩ := RetainedCoreHistory.extendHorizon_finalSlab_phiAlmostNonnegative
    (H := H) (G := G) (hG := hG) (T := t) (hHT := hHt) (hT := ht) (hTs := hts) hpinchG
  have hmet : H'.toHistory.stageMetric (Fin.last H.eventCount) t = S.flow.base.metric t :=
    H.stageMetric_extendHorizon_last hHt S hG ht t
  let records' : ∀ i : Fin H'.eventCount, GeometricCutoffRecord H'.toHistory i p :=
    fun i => (records i).extendHorizon t hHt S hG
  let P : ℕ → (H.stage (Fin.last H.eventCount)).Carrier := fun j =>
    if j < Nc then pc j else pp (j - Nc)
  let Δ : ℕ → ℝ := fun j => if j < Nc then δc j else δ (j - Nc)
  have hP0 : P 0 = y := by
    by_cases hN : 0 < Nc
    · exact (ite_eq_left hN).trans hpc0
    · have : Nc = 0 := by omega
      change (if 0 < Nc then pc 0 else pp (0 - Nc)) = y
      rw [ite_eq_right hN, Nat.zero_sub, h0, this, hpc0]
  have hΔ : ∀ j ≤ Nc + N, 0 < Δ j := by
    intro j hj
    by_cases hjc : j < Nc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc]
      exact hδc j hjc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc]
      exact hδ _ (by omega)
  have hchainP : ∀ j < Nc + N, P (j + 1) ∈
      riemannianBallOf (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j) := by
    intro j hj
    rw [hmet]
    by_cases hjc : j < Nc
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc, ite_eq_left hjc]
      by_cases hjc' : j + 1 < Nc
      · rw [ite_eq_left hjc']
        exact hchainc j hjc
      · rw [ite_eq_right hjc', show j + 1 - Nc = 0 by omega, h0, show Nc = j + 1 by omega]
        exact hchainc j (by omega)
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc, ite_eq_right hjc, ite_eq_right (show ¬ (j + 1 < Nc) by omega),
        show j + 1 - Nc = j - Nc + 1 by omega]
      exact hch (j - Nc) (by omega)
  have hspaceP : ∀ j ≤ Nc + N, ∀ w ∈ riemannianBallOf
      (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j),
      metricScalarAt (H'.toHistory.stageMetric (Fin.last H.eventCount) t) w ≤ M := by
    intro j hj w hw
    rw [hmet] at hw ⊢
    by_cases hjc : j < Nc
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_left hjc, ite_eq_left hjc] at hw
      exact (hMc j hjc w hw).trans hMcM
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_right hjc, ite_eq_right hjc] at hw
      exact hb _ (by omega) w hw
  have hchainUP : ∀ j ≤ Nc + N, ∀ w ∈ riemannianBallOf
      (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j), w ∈ U := by
    intro j hj w hw
    rw [hmet] at hw
    by_cases hjc : j < Nc
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_left hjc, ite_eq_left hjc] at hw
      exact hchainUc j hjc w hw
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_right hjc, ite_eq_right hjc] at hw
      exact hUpp _ (by omega) w hw
  have hsum : ∑ j ∈ Finset.range (Nc + N + 1), Δ j ≤ lamc + ∑ j ∈ Finset.range (N + 1), δ j := by
    have := sum_range_ite_add_P6L (Nc := Nc) (N := N) δc δ
    change ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then δc j else δ (j - Nc)) ≤ _
    rw [this]
    linarith
  have htu : (t' : ℝ) - u' = τ := by
    change t - (t - τ) = τ
    ring
  have hnot' : ¬ H'.CapWindowPoint records' (Fin.last H.eventCount) (P 0) t Dcap θ := by
    rw [hP0]
    rintro ⟨j, hl, A, b, xw, h1, h2, h3⟩
    exact hnot ⟨j, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, xw, h1, h2, h3⟩
  have hres := nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_P6L H' records'
    (fun i b => hcan i b) (fun i b w => hscale i b w) hacc hphi hpinch hut hh hlastA hfp
    (Fin.last H.eventCount) hlastA P Δ hΔ hchainP U hchainUP
    (fun i first _ hf _ z hz A v hv hR =>
      hslabs i first hf z hz ⟨A.point, A.endpoint_eq, A.crossing⟩ v hv hR)
    (fun y z hz hyz v hv hR => by
      obtain rfl := eq_of_heq hyz
      exact hderG y hz v hv hR)
    hM1 hq hspaceP (by rw [htu]; exact hC) hDstar hDmodel (by rw [htu]; exact h4)
    (by
      rw [htu]
      refine lt_of_le_of_lt ?_ hD
      have hs0 : 0 ≤ Real.sqrt (8 * M) *
          Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hsum hs0
      linarith)
    hnot' (Nc + k) (by omega) z (by
      rw [hmet]
      change z ∈ riemannianBallOf (S.flow.base.metric t)
        (if Nc + k < Nc then pc (Nc + k) else pp (Nc + k - Nc))
        (if Nc + k < Nc then δc (Nc + k) else δ (Nc + k - Nc))
      rw [ite_eq_right (show ¬ (Nc + k < Nc) by omega),
        ite_eq_right (show ¬ (Nc + k < Nc) by omega),
        Nat.add_sub_cancel_left]
      exact hz)
  obtain ⟨A⟩ := hres
  refine ⟨H'.toHistory.activeStage u', ?_, ⟨⟨A.point, A.endpoint_eq, A.crossing⟩⟩⟩
  exact H'.toHistory.activeStage_time_le u'

/-- consumer：原 `SL:73`（carrier 全局 `EventSlabsDerivative` / `DerivativeBoundBefore`）由 `_P6L` 版取
`U = univ` 推出（成员前提平凡）。 -/
example : type_of% @chain_traces_of_not_capWindowPoint_of_incomingSlab.{u} := by
  intro H hend s G hG t ht hts p records hcan hscale hacc Ctime qcan Dcap Dstar θ phi hphi hpinch
    hpinchG hslabs hderG hDstar hDmodel y hnot Nc pc δc hpc0 hδc hchainc Mc lamc hMc hlamc N pp δ
    M τ h0 hδ
  exact chain_traces_of_not_capWindowPoint_of_incomingSlab_P6L H hend G hG ht hts records hcan
    hscale hacc hphi hpinch hpinchG univ
    (fun j _ hf _ _ _ v hv hR => hslabs j (j.castSucc_lt_succ.trans_le (Fin.le_last _)) _ v hv hR)
    (fun y _ v hv hR => hderG y v hv hR) hDstar hDmodel y hnot pc δc hpc0 hδc hchainc
    (fun _ _ _ _ => trivial) hMc hlamc N pp δ M τ h0 hδ (fun _ _ _ _ => trivial)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
