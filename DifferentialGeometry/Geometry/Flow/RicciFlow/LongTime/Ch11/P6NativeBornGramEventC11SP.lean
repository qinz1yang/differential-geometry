import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeBornShiScaledC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

set_option autoImplicit false

/-!
# event 时刻的闭窗 Gram（O-CH11-NATIVE-BORN G5 = O2 repair，后缀 `_C11SP`）

SPINE-B G6 `commonFlow_closedGram_C11SP` 要正 stage age `H.time (activeStage t) < t`，因为右端靠
`activeStage t` 的 slab 往左延伸。t 恰为 event 时刻（`activeStage t = i.succ`，`time i.succ = t`）时，
右端改用树内 survivor slab：`backwardSurvivorSlabMetric i`（`HistorySurvivorFlow`）=
`localPullMetric (terminal.extendedMetric v) (backwardSurvivorTerminalMap)`，在**闭**区间
`[time i.castSucc, time i.succ]` 上联合光滑（`backwardSurvivorSlabMetric_jointContMDiffOn`，
`TerminalLimitMetric.extendedMetric` 在终端处光滑），并且
* `v < time i.succ`：`= localPull(incoming v)(backwardSurvivorMap i.castSucc)`（`_before`）；
* `v = time i.succ`：`= backwardSurvivorInitialMetric i.succ`（`_terminal`，即 crossing 处 output 度量）。
公共 flow 的 `f j` 由 trace 唯一性认成 `backwardSurvivorMap j ∘ Ψ'`（`Ψ' : U → survivor domain`），
所以 `[max a (time i.castSucc), t]` 上 `S(v) = localPull(slab v)(Ψ')`，闭窗 Gram 由
`chartGramMatrix_joint_contMDiffOn_of_pullback` 给出。
* `commonFlow_closedGram_traced_C11SP`：G6 的**无 hpos** 版（多一个输入：`f` 由 trace 给出）；
* `exists_reset_shi_commonFlow_scaled_traced_C11SP`：G3b 的无 hpos 孪生。
-/

noncomputable section

open Set Bundle Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- 局部拉回只依赖映射本身（局部微分同胚证明无关）。 -/
theorem localPullMetric_congr_C11SP {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel N) {f₁ f₂ : M → N} (h : f₁ = f₂)
    (h₁ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f₁)
    (h₂ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f₂) :
    localPullMetric g f₁ h₁ = localPullMetric g f₂ h₂ := by
  subst h
  rfl

/-- **G5a（PROVED）**：公共 flow 的闭窗 chart Gram 联合光滑，**不要正 stage age**。 -/
theorem commonFlow_closedGram_traced_C11SP (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) (hlt : (a : ℝ) < t)
    (U : TopologicalSpace.Opens (H.stageAt t).Carrier)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (htr : ∀ x : U, ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) x.val, ∀ j, f j x = B.point j.val j.property.1 j.property.2)
    (S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat))
    (hS : IsSolutionOn S)
    (hmetric : ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
        S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j))
    (x₀ : U) (i k : Fin (Module.finrank ℝ ThreeSpace)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
      (Icc a.val t.val ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
  classical
  by_cases hpos : H.time (H.activeStage t) < t
  · exact commonFlow_closedGram_C11SP H hat hlt hpos f hf S hS hmetric x₀ i k
  have htime : H.time (H.activeStage t) = t :=
    le_antisymm (H.activeStage_time_le t) (not_lt.mp hpos)
  set B := (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet with hB
  -- activeStage t = i.succ
  have hne0 : H.activeStage t ≠ 0 := by
    intro h0
    have h := htime
    rw [h0, H.time_zero] at h
    have ha0 : (0 : ℝ) ≤ a := a.2.1
    linarith
  obtain ⟨e, he⟩ : ∃ e : Fin H.eventCount, e.succ = H.activeStage t := by
    obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr hne0
    exact ⟨m, hm⟩
  have hetime : H.time e.succ = t := by rw [he]; exact htime
  have hfirst : H.activeStage a ≤ e.castSucc := by
    by_contra hcon
    have hlt' : e.castSucc < H.activeStage a := lt_of_not_ge hcon
    have hsucc : e.succ ≤ H.activeStage a := Fin.castSucc_lt_iff_succ_le.mp hlt'
    have h1 : H.time e.succ ≤ H.time (H.activeStage a) := H.time_strictMono.monotone hsucc
    have h2 := H.activeStage_time_le a
    linarith
  have hlast : e.succ ≤ H.activeStage t := he.le
  have hle : H.activeStage a ≤ H.activeStage t := H.activeStage_mono hat
  -- survivor domain 与 Ψ'
  have hsurv : ∀ x : U, x.val ∈ H.backwardSurvivorDomain (H.activeStage a) (H.activeStage t) hle :=
    fun x =>
    ⟨(htr x).choose⟩
  let Ψ : U → H.backwardSurvivorDomain (H.activeStage a) (H.activeStage t) hle :=
    fun x => ⟨x.val, hsurv x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hsurv (isLocalDiffeomorph_subtype_val U x)
  have hmap : ∀ (j : H.StageInterval (H.activeStage a) (H.activeStage t)),
      H.backwardSurvivorMap (H.activeStage a) (H.activeStage t) hle j.val
      j.property.1 j.property.2 ∘ Ψ = f j := by
    intro j
    funext x
    change H.backwardSurvivorMap (H.activeStage a) (H.activeStage t) hle j.val j.property.1
      j.property.2 (Ψ x) = f j x
    rw [H.backwardSurvivorMap_eq_point (H.activeStage a) (H.activeStage t) hle j.val j.property.1
      j.property.2 (Ψ x)
      (htr x).choose]
    exact ((htr x).choose_spec j).symm
  let slab := H.backwardSurvivorSlabMetric (H.activeStage a) (H.activeStage t) hle e hfirst hlast
  let c : ℝ := max a.val (H.time e.castSucc)
  have hct : c < t := max_lt hlt (by
    rw [← hetime]
    exact H.time_strictMono e.castSucc_lt_succ)
  -- 闭窗上 S = Ψ' 拉回 slab
  have hSv : ∀ v ∈ Icc c t.val, S.base.metric v = localPullMetric (slab v) Ψ hΨ := by
    intro v hv
    have hva : v ∈ Icc a.val t.val := ⟨(le_max_left _ _).trans hv.1, hv.2⟩
    rcases lt_or_eq_of_le hv.2 with hvt | hvt
    · let jj : H.StageInterval (H.activeStage a) (H.activeStage t) :=
        ⟨e.castSucc, hfirst, e.castSucc_lt_succ.le.trans hlast⟩
      have hdom : v ∈ H.stageDomain e.castSucc := by
        have hd : H.stageDomain e.castSucc = Ico (H.time e.castSucc) (H.time e.succ) := by
          simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
        rw [hd, hetime]
        exact ⟨(le_max_right _ _).trans hv.1, hvt⟩
      rw [hmetric jj v hva hdom, ObservedHistory.stageMetric_castSucc_apply]
      have hslab : slab v = localPullMetric ((H.event e).incoming.flow.base.metric v)
          (H.backwardSurvivorMap (H.activeStage a) (H.activeStage t) hle e.castSucc hfirst
            (e.castSucc_lt_succ.le.trans hlast))
          (H.backwardSurvivorMap_isLocalDiffeomorph (H.activeStage a) (H.activeStage t) hle
            e.castSucc hfirst
            (e.castSucc_lt_succ.le.trans hlast)) :=
        H.backwardSurvivorSlabMetric_before (H.activeStage a) (H.activeStage t) hle e hfirst
          hlast (by rw [hetime]; exact hvt)
      rw [hslab, localPullMetric_comp _ _ _ _ hΨ ((hmap jj) ▸ hf jj)]
      exact localPullMetric_congr_C11SP _ (hmap jj).symm _ _
    · let jj : H.StageInterval (H.activeStage a) (H.activeStage t) :=
        ⟨e.succ, hfirst.trans e.castSucc_lt_succ.le, hlast⟩
      have hdom : H.time e.succ ∈ H.stageDomain e.succ := by
        have h := H.activeStage_mem (H.stageTime e.succ)
        rw [H.activeStage_stageTime] at h
        exact h
      have hv' : v = H.time e.succ := hvt.trans hetime.symm
      subst hv'
      rw [hmetric jj (H.time e.succ) hva hdom, H.stageMetric_initial]
      have hslab : slab (H.time e.succ) = localPullMetric (H.initialMetric e.succ)
          (H.backwardSurvivorMap (H.activeStage a) (H.activeStage t) hle e.succ
            (hfirst.trans e.castSucc_lt_succ.le) hlast)
          (H.backwardSurvivorMap_isLocalDiffeomorph (H.activeStage a) (H.activeStage t) hle e.succ
            (hfirst.trans e.castSucc_lt_succ.le) hlast) :=
        H.backwardSurvivorSlabMetric_terminal (H.activeStage a) (H.activeStage t) hle e hfirst hlast
      rw [hslab, localPullMetric_comp _ _ _ _ hΨ ((hmap jj) ▸ hf jj)]
      exact localPullMetric_congr_C11SP _ (hmap jj).symm _ _
  have hright : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
      (Icc c t.val ×ˢ B) := by
    have hsub : Icc c t.val ⊆ Icc (H.time e.castSucc) (H.time e.succ) := fun v hv =>
      ⟨(le_max_right _ _).trans hv.1, hv.2.trans hetime.ge⟩
    refine chartGramMatrix_joint_contMDiffOn_of_pullback slab (Icc c t.val)
      ((H.backwardSurvivorSlabMetric_jointContMDiffOn (H.activeStage a) (H.activeStage t) hle e
        hfirst hlast).mono
        (prod_mono hsub subset_rfl)) (fun v => S.base.metric v) Ψ hΨ.contMDiff ?_ x₀ i k
    intro v hv x u w
    rw [hSv v hv, localPullMetric_inner]
  have hint : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
      (Ioo a.val t.val ×ˢ B) :=
    hS.smoothMetric.chartGramMatrix_contDiffOn (G := S.family) (fun _ h => h) x₀ i k
  let ja : H.StageInterval (H.activeStage a) (H.activeStage t) := ⟨H.activeStage a, le_rfl, hle⟩
  have hja : ja.val = Fin.last H.eventCount → H.time ja.val < H.horizon := fun _ =>
    (H.activeStage_time_le a).trans_lt (hlt.trans_le t.2.2)
  have hleft : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
      ((Icc a.val t.val ∩ H.stageDomain ja.val) ×ˢ B) := by
    let S' : SolutionOn (I := ThreeModel) (M := (H.stage ja.val).Carrier)
        (RealTimeInterval.closed a.val t.val hat) := { base := { metric := H.stageMetric ja.val } }
    have hsm := stageMetric_smoothUpTo_C11SP H ja.val hja
    have hpb := SolutionOn.localPullback_chartGramMatrix_joint_contMDiffOn S' (f ja) (hf ja)
      (H.stageDomain ja.val)
      (fun y₀ i' k' => chartGramMatrix_joint_contMDiffOn (H.stageMetric ja.val)
        (H.stageDomain ja.val) hsm.jointContMDiffOn y₀ i' k') x₀ i k
    refine (hpb.mono (prod_mono inter_subset_right subset_rfl)).congr ?_
    intro q hq
    change Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k =
      Tensor.Coordinates.chartGramMatrix
        (localPullMetric (H.stageMetric ja.val q.1) (f ja) (hf ja)) x₀ q.2 i k
    rw [hmetric ja q.1 hq.1.1 hq.1.2]
  intro q hq
  rcases eq_or_lt_of_le hq.1.1 with hqa | hqa
  · -- 左端
    obtain ⟨O, hO, haO, hOsub⟩ := exists_open_right_stageDomain_C11SP H (H.activeStage a)
      (H.activeStage_mem a)
    refine (hleft q ⟨⟨hq.1, ?_⟩, hq.2⟩).mono_of_mem_nhdsWithin ?_
    · rw [← hqa]; exact H.activeStage_mem a
    · refine mem_nhdsWithin.2 ⟨O ×ˢ univ, hO.prod isOpen_univ, ⟨hqa ▸ haO, mem_univ _⟩, ?_⟩
      rintro r ⟨⟨hrO, -⟩, hrI, hrB⟩
      exact ⟨⟨hrI, hOsub r.1 hrI.1 (hrI.2.trans t.2.2) hrO⟩, hrB⟩
  · rcases eq_or_lt_of_le hq.1.2 with hqt | hqt
    · -- 右端（event 时刻）：survivor slab
      refine (hright q ⟨⟨?_, hq.1.2⟩, hq.2⟩).mono_of_mem_nhdsWithin ?_
      · rw [hqt]; exact hct.le
      · refine mem_nhdsWithin.2 ⟨Ioi c ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
          ⟨by rw [hqt]; exact hct, mem_univ _⟩, ?_⟩
        rintro r ⟨⟨hrc, -⟩, hrI, hrB⟩
        exact ⟨⟨le_of_lt hrc, hrI.2⟩, hrB⟩
    · refine (hint q ⟨⟨hqa, hqt⟩, hq.2⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.2 ⟨Ioo a.val t.val ×ˢ univ, isOpen_Ioo.prod isOpen_univ,
        ⟨⟨hqa, hqt⟩, mem_univ _⟩, ?_⟩
      rintro r ⟨⟨hrO, -⟩, -, hrB⟩
      exact ⟨hrO, hrB⟩

/-- **G5b（PROVED）**：G3b 的**无 hpos** 孪生（`f` 由 trace 给出，闭窗 Gram 用 G5a）。 -/
theorem exists_reset_shi_commonFlow_scaled_traced_C11SP (N : ℕ) (T R K : ℝ) (hR : 0 < R)
    (A : ℕ → ℝ) (hA : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ A k) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
      (Q : ℝ) (hQ : 0 < Q),
      (a : ℝ) < t → Q * ((t : ℝ) - a) ≤ T →
      ∀ (U : TopologicalSpace.Opens (H.stageAt t).Carrier)
        (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U →
          (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
        (S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat)),
        IsSolutionOn S →
        (∀ x : U, ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x.val, ∀ j, f j x = B.point j.val j.property.1 j.property.2) →
        (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
          ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
            S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) →
        (∀ v ∈ Icc a.val t.val, ∀ x : U,
          normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K * Q ^ 2) →
        S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U →
      ∀ (pU : U) (Rbig : ℝ≥0),
        {x | riemannianEDistOf (H.stageMetric (H.activeStage t) t) pU.val x ≤ Rbig} ⊆ U →
        ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
          Real.sqrt (K * Q ^ 2) * |(a : ℝ) - t|)) * ENNReal.ofReal (R / Real.sqrt Q) ≤ Rbig →
        (∀ k, 1 ≤ k → k ≤ N → ∀ x : U,
          riemannianEDistOf (S.base.metric a) pU x ≤ ENNReal.ofReal (R / Real.sqrt Q) →
          curvDerivNormSq k (H.stageMetric (H.activeStage a) a)
            (f ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩ x) ≤ A k * Q ^ (2 + k)) →
      ∀ k ≤ N, curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) pU.val ≤
        Real.sqrt B := by
  obtain ⟨B, hB, hb⟩ := exists_initial_shi_scaled_C11SP.{u} N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro H a t hat Q hQ hlt hT U f hf S hS htr hmetric hRm hterm pU Rbig hball hfit hinit k hk
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hcar : Icc a.val t.val ⊆ (RealTimeInterval.closed a.val t.val hat).carrier :=
    fun _ h => h
  have hreg : Ioo a.val t.val ⊆ (RealTimeInterval.closed a.val t.val hat).regular :=
    fun _ h => h
  have h0 : (S.timeShift a.val).base.metric 0 = S.base.metric a.val := by
    rw [SolutionOn.timeShift_base_metric, zero_add]
  have hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix
          ((S.timeShift a.val).base.metric q.1) x₀ q.2 i j)
        (Icc 0 (t.val - a.val) ×ˢ
          (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
    intro x₀ i j
    have hG := commonFlow_closedGram_traced_C11SP H hat hlt U f hf htr S hS hmetric x₀ i j
    have hφ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1 + a.val, q.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    refine (hG.comp hφ.contMDiffOn ?_).congr ?_
    · intro q hq
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩
    · intro q _
      rfl
  have hcomp : IsCompact
      {x | riemannianEDistOf (H.stageMetric (H.activeStage t) t) pU.val x ≤ (Rbig : ℝ≥0∞)} := by
    have h := (Geometry.Metric.isClosed_riemannianClosedBallOf
      (H.stageMetric (H.activeStage t) t) pU.val (Rbig : ℝ)).isCompact
    simpa only [riemannianClosedBallOf, ENNReal.ofReal_coe_nnreal] using h
  have hcpt : IsCompact {x : U |
      riemannianEDistOf ((S.timeShift a.val).base.metric 0) pU x ≤
        ENNReal.ofReal (R / Real.sqrt Q)} := by
    rw [h0]
    exact isCompact_intrinsic_closedBall_of_terminal_ball (H.stageMetric (H.activeStage t) t) U
      S hS hcar hreg hRm ⟨le_rfl, hat⟩ hterm pU (r := (R / Real.sqrt Q).toNNReal) (R := Rbig)
      hcomp hball hfit
  have key := hb U (RealTimeInterval.closed a.val t.val hat |>.timeShift a.val)
    (S.timeShift a.val) Q hQ (t.val - a.val) (by linarith) hT (isSolutionOn_timeShift hS a.val)
    (fun r hr => hcar ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (fun r hr => hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩) hgram pU hcpt
    (fun s hs x _ => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
        FILL910.curvDerivNormSq_zero_eq_normSq0S_metricRm04At]
      exact hRm (s + a.val) ⟨by linarith [hs.1], by linarith [hs.2]⟩ x)
    (fun j hj1 hjN x hx => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, h0,
        hmetric ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩ a.val ⟨le_rfl, hat⟩
          (H.activeStage_mem a), curvDerivNormSq_localPullMetric]
      exact hinit j hj1 hjN x (h0 ▸ hx))
    k hk (t.val - a.val) ⟨by linarith, le_rfl⟩ pU
    (by rw [h0, riemannianEDistOf_self]; exact bot_le)
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
    sub_add_cancel, hterm] at key
  have hQpow : Q ^ (2 + k) = (Q * Real.sqrt Q ^ k) ^ 2 := by
    have hs : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
    calc Q ^ (2 + k) = Q ^ 2 * (Real.sqrt Q ^ 2) ^ k := by rw [hs, pow_add]
      _ = (Q * Real.sqrt Q ^ k) ^ 2 := by ring
  have hden : 0 < Q * Real.sqrt Q ^ k := mul_pos hQ (pow_pos (Real.sqrt_pos.mpr hQ) k)
  have hnorm : curvDerivNorm k (H.stageMetric (H.activeStage t) t) pU.val ≤
      Real.sqrt B * (Q * Real.sqrt Q ^ k) := by
    calc curvDerivNorm k (H.stageMetric (H.activeStage t) t) pU.val
        = curvDerivNorm k ((H.stageMetric (H.activeStage t) t).restrictOpen U) pU :=
          (curvDerivNorm_restrictOpen _ U k pU).symm
      _ ≤ Real.sqrt (B * Q ^ (2 + k)) := Real.sqrt_le_sqrt key
      _ = Real.sqrt B * (Q * Real.sqrt Q ^ k) := by
          rw [hQpow, Real.sqrt_mul (by linarith), Real.sqrt_sq hden.le]
  rw [curvDerivNorm_scaleMetric]
  exact (div_le_iff₀ hden).mpr hnorm


end GC.LongTime.Ch11
