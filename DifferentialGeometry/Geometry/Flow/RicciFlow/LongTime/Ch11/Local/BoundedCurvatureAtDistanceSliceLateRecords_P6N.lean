import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceTimeWindow_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceChainCaptureLateRecords_P6N

/-!
# G2（方案 B）窗口 spine 2：`BoundedCurvatureAtDistanceSlice:23/73` 的 late-records 形（`_P6N`）

`SL:73` 在 `extendHorizon t` 后的 history 上、窗口 `[t − τ, t]` 内调 `BTCC:409`；records 只经 BTCC 在
`T₀ ≤ u' ≤ time j.succ` 的事件上用 ⇒ late records（`T₀ ≤ a ≤ t − τ`）足够；pinching 只在窗口用。
改动（在 G1 `SL:23′/73′` 之上）：late records、窗口 pinching（`∩ Ici a`）、`hnot` 展开形，
`extendHorizon` 的 final-slab pinching 直接由窗口 `hpinchG` 给（`v ≤ t < s`、`a ≤ t − τ ≤ v`）。
consumer：G1 `SL:73′`（全 family、全 pinching、`¬ CapWindowPoint`）⇐ 本形取 `T₀ = a`。
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


private theorem nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_late_P6N
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hTu : T₀ ≤ (u : ℝ))
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (u : ℝ))
      phi)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici (u : ℝ)) phi)
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
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y : (H.toHistory.stage (Fin.last H.eventCount)).Carrier, ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, (u : ℝ) ≤ v →
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
    (hnot : ¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (A : BackwardPointTrace H.toHistory j.succ k hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        (t : ℝ) - H.time j.succ ≤ θcap * (((records j hT).static b).neck.scale)⁻¹) :
    ∀ j ≤ N, ∀ z ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u) k
        (hk ▸ H.toHistory.activeStage_mono hut) z) := by
  subst hk
  intro j hj z hz
  by_contra hne
  exact hnot (H.capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_late_P6N
    records hcan hscale hacc hphi hut hTu hpinch h hlastA hfinalPinch pc δ hδ hchain z ⟨j, hj, hz⟩
    (not_nonempty_iff.mp hne) U hchainU hslabs hfinal hM hqcan hspace htime hDstar hDmodel hθ
    hwin)

private theorem sum_range_ite_add_late_P6N {Nc N : ℕ} (a b : ℕ → ℝ) :
    ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then a j else b (j - Nc)) =
      ∑ j ∈ Finset.range Nc, a j + ∑ j ∈ Finset.range (N + 1), b j := by
  rw [show Nc + N + 1 = Nc + (N + 1) by ring, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- **`_P6N`（`SL:73` late-records + 窗口形）**：G1 `SL:73′` 之上：`{T₀} records` late family
（`hcan`/`hscale` 同形）、窗口起点 `a`（`hphi` 后）与 `hTa : T₀ ≤ a`、`hpinch`/`hpinchG` 窗口 pinching
（`∩ Ici a`）、`hnot` = `¬ CapWindowPoint` 的展开形（late records）。结论与 `SL:73′` 逐字。 -/
theorem chain_traces_of_not_capWindowPoint_of_incomingSlab_late_P6N
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {t : ℝ} (ht : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan Dcap Dstar θ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (a : ℝ) (hTa : T₀ ≤ a)
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici a) phi)
    (hpinchG : Perelman.PhiAlmostNonnegative G.flow
      (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici a) phi)
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (hslabs : ∀ j : Fin H.eventCount,
      ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), a ≤ v →
      qcan < (H.toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
        (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderG : ∀ y ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, a ≤ v →
      qcan < G.flow.scalar v y →
      |derivWithin (fun w => G.flow.scalar w y) (Iic v) v| ≤ Ctime * G.flow.scalar v y ^ 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (hnot : ¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ)
      (hl : j.succ ≤ Fin.last H.eventCount)
      (A : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹)
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
      Mc ≤ M → qcan ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ t → a ≤ t - τ →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
          (lamc + ∑ k ∈ Finset.range (N + 1), δ k) < Dcap →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ t - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z) := by
  intro N pp δ M τ h0 hδ hUpp hch hb hMcM hq hM1 hτ0 hτt haτ hC h4 hD k hk z hz
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
  have hfp : Perelman.PhiAlmostNonnegative (H'.finalSlab hh).flow
      (Icc (H.time (Fin.last H.eventCount)) H'.horizon ∩ Ici (u' : ℝ)) phi :=
    fun v hv x => hpinchG v ⟨⟨hv.1.1, hv.1.2.trans_lt hts⟩, haτ.trans hv.2⟩ x
  have hmet : H'.toHistory.stageMetric (Fin.last H.eventCount) t = S.flow.base.metric t :=
    H.stageMetric_extendHorizon_last hHt S hG ht t
  let records' : ∀ i : Fin H'.eventCount, T₀ ≤ H'.time i.succ →
      GeometricCutoffRecord H'.toHistory i p :=
    fun i hi => (records i hi).extendHorizon t hHt S hG
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
    have := sum_range_ite_add_late_P6N (Nc := Nc) (N := N) δc δ
    change ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then δc j else δ (j - Nc)) ≤ _
    rw [this]
    linarith
  have htu : (t' : ℝ) - u' = τ := by
    change t - (t - τ) = τ
    ring
  have hres := nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_late_P6N H' records'
    (θcap := θ) (fun i hi b => hcan i hi b) (fun i hi b w => hscale i hi b w) hacc hphi hut
    (hTa.trans haτ)
    (fun j => phiAlmostNonnegative_mono_P6N (hpinch j)
      (inter_subset_inter_right _ (Ici_subset_Ici.mpr haτ))) hh hlastA hfp
    (Fin.last H.eventCount) hlastA P Δ hΔ hchainP U hchainUP
    (fun i first _ hf _ z hz A v hv huv hR =>
      hslabs i first hf z hz ⟨A.point, A.endpoint_eq, A.crossing⟩ v hv (haτ.trans huv) hR)
    (fun y z hz hyz v hv huv hR => by
      obtain rfl := eq_of_heq hyz
      exact hderG y hz v hv (haτ.trans huv) hR)
    hM1 hq hspaceP (by rw [htu]; exact hC) hDstar hDmodel (by rw [htu]; exact h4)
    (by
      rw [htu]
      refine lt_of_le_of_lt ?_ hD
      have hs0 : 0 ≤ Real.sqrt (8 * M) *
          Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hsum hs0
      linarith)
    (by
      rw [hP0]
      rintro ⟨j, hT, hl, A, b, xw, h1, h2, h3⟩
      exact hnot ⟨j, hT, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, xw, h1, h2, h3⟩)
    (Nc + k) (by omega) z (by
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

/-- consumer：G1 `SL:73′`（全 family、`EventSlabsPinched`、`¬ CapWindowPoint`）⇐ late 形取 `T₀ = a`。 -/
example : type_of% @chain_traces_of_not_capWindowPoint_of_incomingSlab_window_P6N.{u} := by
  intro H hend s G hG t ht hts p records hcan hscale hacc Ctime qcan Dcap Dstar θ phi hphi hpinch
    hpinchG U a hslabs hderG hDstar hDmodel y hnot Nc pc δc hpc0 hδc hchainc hchainUc Mc lamc hMc
    hlamc
  exact chain_traces_of_not_capWindowPoint_of_incomingSlab_late_P6N H hend G hG ht hts (T₀ := a)
    (fun i _ => records i) (fun i _ b => hcan i b) (fun i _ b z => hscale i b z) hacc hphi a le_rfl
    (fun j => phiAlmostNonnegative_mono_P6N (hpinch j) inter_subset_left)
    (phiAlmostNonnegative_mono_P6N hpinchG inter_subset_left) U hslabs hderG hDstar hDmodel y
    (fun ⟨j, _, hl, A, b, x, h1, h2, h3⟩ => hnot ⟨j, hl, A, b, x, h1, h2, h3⟩) pc δc hpc0 hδc
    hchainc hchainUc hMc hlamc

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
