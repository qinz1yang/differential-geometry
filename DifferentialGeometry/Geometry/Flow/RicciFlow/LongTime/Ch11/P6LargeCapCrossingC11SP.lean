import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryNoShortcutDisjC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceLeftWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionBackwardStep

set_option autoImplicit false

/-!
# 窗内大 cap crossing 计数 CC 与 (D4′) 乘性链（O-CH11-NATIVE-CC G1，后缀 `_C11SP`）

SPINE-B 拆分表 L4 的 Lean 形：SL1（`exists_prepared_time_trace_window_CXSP` 去 `nr ≤ r` 的孪生）的
pair 距离第二行 ⇐ (D4′) 乘性（NATIVE-SHORT `surgery_no_shortcut_buffer_of_disj_C11SP`，A2 G5 结论逐字；
余 binder `hdisj`）∧ CC（计数 `≤ n₀`）。

**每个 crossing 的因子**：沿窗 `[a, t]` 两条 trace `A`（seed）、`A'`（query）。crossed event `e`：
* 两端点都受保护（不在任何 cap 内窗 `‖z‖ ≤ transitionEnd + 10`）：原 (D4) `surgery_no_shortcut_C11D`，因子 `1`；
* 至少一端点在某大 cap（`neck.scale ≤ M`）的 buffer `transitionEnd < ‖z‖ ≤ transitionEnd + 10`：
  (D4′) 乘性，因子 `C_buf = max (1 + 4·(22/c)) Cs`（NATIVE-SHORT 显式 `c`、`Cs = 4K(TE+13)`，`K = TE+11`）。
这样的 `e` 属于 `CC(A) ∪ CC(A')`，个数 `≤ 2 n₀`；slab 内 drift 加性。从 `t` 倒推，对 `(v, t]` 内
crossed event 个数强归纳（`pairEDist_le_pow_mul_of_crossings_C11SP`）：
`d_v ≤ C_buf^{2n₀}·(d_t + Λ (t − v))`。**两条 trace ⇒ 指数 `2 n₀`**；`A′ = C_buf^{2n₀}·A`。

**CC 合同（统一形，`pairEDist_window_of_CC_C11SP` 的 binder `hCC`）**：`ε₀, θ̄, n₀` 在 S 之前；
records/params 合取逐字 = `exists_records_of_prepared_chain_CXSP`；`∀ B` 在 records 之后，`T₀` 在 `B` 之后
（`T₀` 依赖 hrecent / hdecay）；窗深 `θ·B ≤ θ̄`（即归一化时间 `≤ 4θ̄`）；全部先于 `n, t, Q, a, y`。
`n₀` 必须与 `B` 无关：Window 里 scalar 倍数 `m`（= B）在 `H0` 之后选，而 `A′ = C_buf^{2n₀}·A` 要在
`H0` 之前选（`timeCore_absorb_C11SP`）。G2 给 `n₀ = 1`（CC ⇐ NR）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
  {p q : (H.stageAt t).Carrier}

/-- `pairEDist_CXSP` 在已知 active stage `j` 时的展开。 -/
theorem pairEDist_eq_of_activeStage_C11SP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (j : Fin (H.eventCount + 1))
    (hj : H.activeStage v = j) (hf : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t) :
    A.pairEDist_CXSP (hat := hat) B v hav hvt =
      riemannianEDistOf (H.stageMetric j v) (A.point j hf hl) (B.point j hf hl) := by
  subst hj
  rfl

/-- **乘性 crossing 链（PROVED）**：slab 内加性 drift（`hslab`），crossed event 处左极限跳跃——
`e ∈ K` 因子 `C`（`hjumpK`），`e ∉ K` 因子 `1`（`hjump1`）；`K` 中被 `(a, t]` crossed 的个数 `≤ n`
⇒ `d_v ≤ C^n (d_t + Λ (t − v))`。全部条件化在 `(v, t]` 上 `d < X`（first-exit 用）。 -/
theorem pairEDist_le_pow_mul_of_crossings_C11SP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {C X : ℝ≥0∞} (hC : 1 ≤ C) (K : Set (Fin H.eventCount)) (n : ℕ)
    (hKn : (K ∩ {e | H.time e.succ ∈ Ioc (a : ℝ) t}).ncard ≤ n)
    (hslab : ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)))
    (hjumpK : ∀ e ∈ K, ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (haw : a ≤ w) (hwt : w ≤ t), (w : ℝ) = H.time e.succ → H.activeStage v = e.castSucc →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        C * A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)))
    (hjump1 : ∀ e ∉ K, ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (haw : a ≤ w) (hwt : w ≤ t), (w : ℝ) = H.time e.succ → H.activeStage v = e.castSucc →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v))) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        C ^ n * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal (Λ * ((t : ℝ) - v))) := by
  classical
  intro v hav hvt hG
  let S : Icc (0 : ℝ) H.horizon → Finset (Fin H.eventCount) := fun w =>
    Finset.univ.filter (fun e => (w : ℝ) < H.time e.succ ∧ H.time e.succ ≤ (t : ℝ))
  let k : Icc (0 : ℝ) H.horizon → ℕ := fun w => ((S w).filter (· ∈ K)).card
  have key : ∀ (m : ℕ) (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
      (S w).card = m →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), w < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B w haw hwt ≤
        C ^ k w * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal (Λ * ((t : ℝ) - w))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro w haw hwt hm hGw
      have hCk : 1 ≤ C ^ k w := one_le_pow₀ hC
      by_cases hempty : S w = ∅
      · have hst : H.activeStage w = H.activeStage t := by
          apply H.activeStage_eq_of_forall_time_not_mem_Ioc hwt
          intro i hi
          have hiS : i ∈ S w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1, hi.2⟩
          rw [hempty] at hiS
          exact absurd hiS (Finset.notMem_empty _)
        have h1 := hslab w t haw hwt hat le_rfl hwt hst hGw
        exact h1.trans (le_mul_of_one_le_left zero_le hCk)
      · obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have he₀' := (Finset.mem_filter.mp he₀).2
        have hcr := (H.crossed_event_iff_mem_Ioc w t e₀).mpr he₀'
        have hlt : H.activeStage w < H.activeStage t :=
          hcr.1.trans_lt (Fin.castSucc_lt_iff_succ_le.mpr hcr.2)
        obtain ⟨e, he⟩ :=
          Fin.exists_castSucc_eq.mpr (ne_of_lt (hlt.trans_le (Fin.le_last _)))
        have hesucc : e.succ ≤ H.activeStage t :=
          Fin.castSucc_lt_iff_succ_le.mp (by rw [he]; exact hlt)
        have heIoc := (H.crossed_event_iff_mem_Ioc w t e).mp ⟨he.ge, hesucc⟩
        let τ : Icc (0 : ℝ) H.horizon :=
          ⟨H.time e.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
        have hwτ : w < τ := heIoc.1
        have haτ : a ≤ τ := haw.trans hwτ.le
        have hτt : τ ≤ t := heIoc.2
        have hGτ : ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), τ < s →
            A.pairEDist_CXSP (hat := hat) B s has hst < X :=
          fun s has hst hτs => hGw s has hst (hwτ.trans hτs)
        have hsub : S τ ⊆ S w := by
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (show (w : ℝ) < τ from hwτ).trans hi'.1, hi'.2⟩
        have heS : e ∈ S w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heIoc⟩
        have heSτ : e ∉ S τ := fun h => lt_irrefl _ (Finset.mem_filter.mp h).2.1
        have hcard : (S τ).card < m :=
          (Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
            ⟨e, heS, heSτ⟩)).trans_eq hm
        have hIH := ih _ hcard τ haτ hτt rfl hGτ
        have hsplit : ENNReal.ofReal (Λ * ((t : ℝ) - w)) =
            ENNReal.ofReal (Λ * ((t : ℝ) - τ)) + ENNReal.ofReal (Λ * ((τ : ℝ) - w)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hΛ (sub_nonneg.mpr hτt))
            (mul_nonneg hΛ (sub_nonneg.mpr hwτ.le))]
          congr 1
          ring
        have hfilt : (S τ).filter (· ∈ K) ⊆ (S w).filter (· ∈ K) :=
          Finset.filter_subset_filter _ hsub
        by_cases heK : e ∈ K
        · have hj := hjumpK e heK w τ haw hwt haτ hτt rfl he.symm hGw
          have hkk : k τ + 1 ≤ k w := by
            have hins : insert e ((S τ).filter (· ∈ K)) ⊆ (S w).filter (· ∈ K) := by
              intro i hi
              rcases Finset.mem_insert.mp hi with rfl | hi
              · exact Finset.mem_filter.mpr ⟨heS, heK⟩
              · exact hfilt hi
            have hc := Finset.card_le_card hins
            rwa [Finset.card_insert_of_notMem
              (fun h => heSτ (Finset.mem_filter.mp h).1)] at hc
          have hpow : C * C ^ k τ ≤ C ^ k w := by
            rw [← pow_succ']
            exact pow_le_pow_right₀ hC hkk
          calc A.pairEDist_CXSP (hat := hat) B w haw hwt
              ≤ C * A.pairEDist_CXSP (hat := hat) B τ haτ hτt +
                  ENNReal.ofReal (Λ * ((τ : ℝ) - w)) := hj
            _ ≤ C * (C ^ k τ * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - τ)))) +
                  ENNReal.ofReal (Λ * ((τ : ℝ) - w)) :=
                add_le_add (mul_le_mul_right hIH C) le_rfl
            _ = (C * C ^ k τ) * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - τ))) +
                  ENNReal.ofReal (Λ * ((τ : ℝ) - w)) := by rw [mul_assoc]
            _ ≤ C ^ k w * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - τ))) +
                  C ^ k w * ENNReal.ofReal (Λ * ((τ : ℝ) - w)) :=
                add_le_add (mul_le_mul_left hpow _) (le_mul_of_one_le_left zero_le hCk)
            _ = C ^ k w * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - w))) := by
                rw [← mul_add, add_assoc, ← hsplit]
        · have hj := hjump1 e heK w τ haw hwt haτ hτt rfl he.symm hGw
          have hkk : k τ ≤ k w := Finset.card_le_card hfilt
          have hpow : C ^ k τ ≤ C ^ k w := pow_le_pow_right₀ hC hkk
          calc A.pairEDist_CXSP (hat := hat) B w haw hwt
              ≤ A.pairEDist_CXSP (hat := hat) B τ haτ hτt +
                  ENNReal.ofReal (Λ * ((τ : ℝ) - w)) := hj
            _ ≤ C ^ k τ * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - τ))) +
                  ENNReal.ofReal (Λ * ((τ : ℝ) - w)) := add_le_add hIH le_rfl
            _ ≤ C ^ k w * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - τ))) +
                  C ^ k w * ENNReal.ofReal (Λ * ((τ : ℝ) - w)) :=
                add_le_add (mul_le_mul_left hpow _) (le_mul_of_one_le_left zero_le hCk)
            _ = C ^ k w * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal (Λ * ((t : ℝ) - w))) := by
                rw [← mul_add, add_assoc, ← hsplit]
  have hk : k v ≤ n := by
    refine le_trans ?_ hKn
    change ((S v).filter (· ∈ K)).card ≤ _
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro i hi
    have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have h2 := (Finset.mem_filter.mp h1.1).2
    exact ⟨h1.2, (show (a : ℝ) ≤ v from hav).trans_lt h2.1, h2.2⟩
  exact (key _ v hav hvt rfl hG).trans (mul_le_mul_left (pow_le_pow_right₀ hC hk) _)

/-- **单 crossing 跳跃（PROVED）**：(D4)/(D4′) 的左极限形（`∀ δ > 0, ∀ᶠ s ↑ τ_e, d_{e⁻,s} ≤ c·d_{e⁺,τ_e} + δ`）
+ slab 内 drift ⇒ `d_v ≤ c·d_{τ_e} + Λ (τ_e − v)`（`v` 在 stage `e⁻`）。 -/
theorem jump_of_eventually_C11SP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {c X : ℝ≥0∞}
    (hslab : ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)))
    (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc) (hl : e.succ ≤ H.activeStage t)
    (hev : ∀ δ : ℝ, 0 < δ → ∀ᶠ s in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc s)
          (A.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl))
          (B.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl)) ≤
        c * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
          (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
          (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) + ENNReal.ofReal δ) :
    ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w) (hwt : w ≤ t),
      (w : ℝ) = H.time e.succ → H.activeStage v = e.castSucc →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        c * A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)) := by
  intro v w hav hvt haw hwt hw hv hG
  have hwstage : H.activeStage w = e.succ := by
    have hweq : w = ⟨H.time e.succ, H.time_nonneg _, H.time_le_horizon_at _⟩ := Subtype.ext hw
    rw [hweq]
    exact H.activeStage_at_time e.succ
  rw [pairEDist_eq_of_activeStage_C11SP A B w haw hwt e.succ hwstage
    (hf.trans e.castSucc_lt_succ.le) hl, hw]
  have hvT : (v : ℝ) < H.time e.succ := by
    by_contra hcon
    have hle := H.le_activeStage v e.succ (le_of_not_gt hcon)
    rw [hv] at hle
    exact absurd hle (not_le_of_gt e.castSucc_lt_succ)
  have hTt : H.time e.succ ≤ (t : ℝ) := hw ▸ hwt
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  obtain ⟨s, hs1, hs2⟩ := ((hev ε hε').and (Ioo_mem_nhdsLT hvT)).exists
  let sI : Icc (0 : ℝ) H.horizon :=
    ⟨s, v.2.1.trans hs2.1.le, hs2.2.le.trans (H.time_le_horizon_at _)⟩
  have hvs : v ≤ sI := hs2.1.le
  have has : a ≤ sI := hav.trans hvs
  have hst : sI ≤ t := (show s ≤ (t : ℝ) from hs2.2.le.trans hTt)
  have hsstage : H.activeStage sI = e.castSucc := by
    apply le_antisymm
    · by_contra hcon
      have h1 : e.succ ≤ H.activeStage sI := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hcon)
      have h2 := (H.time_strictMono.monotone h1).trans (H.activeStage_time_le sI)
      exact absurd hs2.2 (not_lt_of_ge h2)
    · rw [← hv]
      exact H.activeStage_mono hvs
  have hsl := hslab v sI hav hvt has hst hvs (hv.trans hsstage.symm) hG
  rw [pairEDist_eq_of_activeStage_C11SP A B sI has hst e.castSucc hsstage hf
    (e.castSucc_lt_succ.le.trans hl)] at hsl
  have hdrift : ENNReal.ofReal (Λ * ((sI : ℝ) - v)) ≤
      ENNReal.ofReal (Λ * (H.time e.succ - v)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [hs2.2]) hΛ)
  calc A.pairEDist_CXSP (hat := hat) B v hav hvt
      ≤ (c * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
          (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
          (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) + ENNReal.ofReal ε) +
          ENNReal.ofReal (Λ * (H.time e.succ - v)) := hsl.trans (add_le_add hs1 hdrift)
    _ = c * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
          (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
          (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) +
          ENNReal.ofReal (Λ * (H.time e.succ - v)) + ε := by
        rw [ENNReal.ofReal_coe_nnreal, add_right_comm]

theorem activeStage_eq_succ_of_time_C11SP (e : Fin H.eventCount) (w : Icc (0 : ℝ) H.horizon)
    (hw : (w : ℝ) = H.time e.succ) : H.activeStage w = e.succ := by
  have hweq : w = ⟨H.time e.succ, H.time_nonneg _, H.time_le_horizon_at _⟩ := Subtype.ext hw
  rw [hweq]
  exact H.activeStage_at_time e.succ

/-- **G1 consumer（L4 的 Lean 形；PROVISIONAL[hdisj, CC]）**：Window 孪生的 pair 距离第二行
⇐ (D4′) 乘性（NATIVE-SHORT `surgery_no_shortcut_buffer_of_disj_C11SP`：A2 G5 孪生 + `hshort′` PROVED，
余 binder `hdisj`）
∧ 原 (D4)（`surgery_no_shortcut_C11D`，受保护 crossing 因子 1）∧ CC（`hCCA`、`hCCB`：两条 trace 各自
落入大 cap buffer 的 crossed event 数 `≤ n₀`）。`hclassA/B` = 每个 crossed 端点"受保护或在大 cap buffer"
（小 cap 由 G19 保护排除，born 点不是 crossing 像）；`hslab` = slab 内 drift（同 guard 链）。
结论：`d_v ≤ C_buf^{2 n₀} (d_t + Λ (t − v))`，`C_buf = max (1 + 4·(22/c)) Cs`。 -/
theorem pairEDist_window_of_largeCap_count_C11SP
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hOld : ∀ e, (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hε : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    (hdisj : ∀ (e : Fin H.eventCount) (b b' : (H.event e).RetainedBoundaryIndex), b ≠ b' →
      ∀ y z : standardCapWindow params.modelRadius,
        ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records e).static b).window y ≠ ((records e).static b').window z)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {X : ℝ≥0∞} {M : ℝ} (n₀ : ℕ)
    (hclassA : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t),
      (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉ ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M)
    (hclassB : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t),
      (∀ b, B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉ ((records e).static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M)
    (hCCA : Set.ncard {e : Fin H.eventCount | ∃ (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M} ≤ n₀)
    (hCCB : Set.ncard {e : Fin H.eventCount | ∃ (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M} ≤ n₀)
    (hslab : ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v))) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
            ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
              (StandardCap.transitionEnd + 11) ^ 2)))
            (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))) ^ (2 * n₀) *
          (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal (Λ * ((t : ℝ) - v))) := by
  have hTE := StandardCap.transitionEnd_pos
  have hc : 0 < min (1 / (2 * (StandardCap.transitionEnd + 11)))
      ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
        (StandardCap.transitionEnd + 11) ^ 2) :=
    lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hC : 1 ≤ ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
        ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
          (StandardCap.transitionEnd + 11) ^ 2)))
        (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))) := by
    refine ENNReal.one_le_ofReal.mpr (le_max_of_le_left ?_)
    have h4 : 0 ≤ 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
        ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
          (StandardCap.transitionEnd + 11) ^ 2)) := by positivity
    linarith
  have hfl : ∀ (e : Fin H.eventCount) (v w : Icc (0 : ℝ) H.horizon), a ≤ v → w ≤ t →
      (w : ℝ) = H.time e.succ → H.activeStage v = e.castSucc →
      H.activeStage a ≤ e.castSucc ∧ e.succ ≤ H.activeStage t := by
    intro e v w hav hwt hw hv
    refine ⟨hv ▸ H.activeStage_mono hav, ?_⟩
    rw [← activeStage_eq_succ_of_time_C11SP e w hw]
    exact H.activeStage_mono hwt
  refine pairEDist_le_pow_mul_of_crossings_C11SP A B hΛ hC
    ({e : Fin H.eventCount | ∃ (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M} ∪
      {e : Fin H.eventCount | ∃ (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t) (b : (H.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        ((records e).static b).window z = B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
        ((records e).static b).neck.scale ≤ M}) (2 * n₀) ?_ hslab ?_ ?_
  · refine (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans ?_)
    rw [two_mul]
    exact Nat.add_le_add hCCA hCCB
  · intro e _ v w hav hvt haw hwt hw hv hG
    obtain ⟨hf, hl⟩ := hfl e v w hav hwt hw hv
    refine jump_of_eventually_C11SP A B hΛ hslab e hf hl
      (fun δ hδ => ObservedHistory.surgery_no_shortcut_buffer_of_disj_C11SP H e
        ((records e).static) (hOld e) (hcan e) hε hD (hdisj e)
        (A.crossing e hf hl) (B.crossing e hf hl) ?_ ?_ hδ)
      v w hav hvt haw hwt hw hv hG
    · rcases hclassA e hf hl with h | ⟨b, z, h1, h2, h3, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, z, h1, h2, h3⟩
    · rcases hclassB e hf hl with h | ⟨b, z, h1, h2, h3, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, z, h1, h2, h3⟩
  · intro e he v w hav hvt haw hwt hw hv hG
    obtain ⟨hf, hl⟩ := hfl e v w hav hwt hw hv
    have hpA := (hclassA e hf hl).resolve_right (by
      rintro ⟨b, z, h1, h2, h3, h4⟩
      exact he (Set.mem_union_left _ (Set.mem_ofPred_eq.mpr ⟨hf, hl, b, z, h1, h2, h3, h4⟩)))
    have hpB := (hclassB e hf hl).resolve_right (by
      rintro ⟨b, z, h1, h2, h3, h4⟩
      exact he (Set.mem_union_right _ (Set.mem_ofPred_eq.mpr ⟨hf, hl, b, z, h1, h2, h3, h4⟩)))
    have hj := jump_of_eventually_C11SP A B hΛ (c := 1) hslab e hf hl
      (fun δ hδ => by
        filter_upwards [ObservedHistory.surgery_no_shortcut_C11D H e ((records e).static)
          (hOld e) (hcan e) hε hD (A.crossing e hf hl) (B.crossing e hf hl) hpA hpB hδ]
          with s hs
        rwa [one_mul])
      v w hav hvt haw hwt hw hv hG
    rwa [one_mul] at hj

/-- consumer：`K = ∅`、`n = 0` 时乘性链退化为 guard 链的加性形（`C^0 = 1`）。 -/
example (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {X : ℝ≥0∞}
    (hslab : ∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
      (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)))
    (hjump1 : ∀ (e : Fin H.eventCount) (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (haw : a ≤ w) (hwt : w ≤ t), (w : ℝ) = H.time e.succ → H.activeStage v = e.castSucc →
      (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
        A.pairEDist_CXSP (hat := hat) B s has hst < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v)))
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
    (hG : ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
      A.pairEDist_CXSP (hat := hat) B s has hst < X) :
    A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
      A.pairEDist_CXSP (hat := hat) B t hat le_rfl + ENNReal.ofReal (Λ * ((t : ℝ) - v)) := by
  have h := pairEDist_le_pow_mul_of_crossings_C11SP A B hΛ (C := 2) (by norm_num) ∅ 0
    (by simp) hslab (fun e he => absurd he (Set.notMem_empty e))
    (fun e _ => hjump1 e) v hav hvt hG
  rwa [pow_zero, one_mul] at h

/-- **TimeCore `∀ A` 吸收（PROVED，算术）**：Window 预算 `d0 + Δ + γ ≤ Afac` 在 `A′ = C^N·Afac`
下对 `C^N d0, C^N Δ, C^N γ` 成立。`N = 2 n₀` 必须与 `m`（scalar 倍数，Window 里在 `H0` 之后选）无关，
所以 CC 的 `n₀` 要放在 `∀ B` 之前（见 `pairEDist_window_of_CC_C11SP` 的量词序）。 -/
theorem timeCore_absorb_C11SP {C d0 Δ γ Afac : ℝ} (N : ℕ) (hC : 1 ≤ C) (hA : 1 < Afac)
    (hbud : d0 + Δ + γ ≤ Afac) :
    1 < C ^ N * Afac ∧ C ^ N * d0 + C ^ N * Δ + C ^ N * γ ≤ C ^ N * Afac := by
  have hCN : 1 ≤ C ^ N := one_le_pow₀ hC
  refine ⟨?_, ?_⟩
  · nlinarith
  · rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left hbud (zero_le_one.trans hCN)

/-- **G1 合同 consumer（PROVISIONAL[CC, hdisj]）**：`hCC` = CC 合同（统一形：`ε₀, θ̄, n₀`
在 S 之前，`∀ B` 在 records 之后，`T₀` 在 `B` 之后，窗深 `θ·B ≤ θ̄`；records/params 合取逐字取
`exists_records_of_prepared_chain_CXSP`）。结论 = 同一量词骨架下，任意两条满足 scalar `≤ 2BQ` 的
trace 的 pair 距离第二行带因子 `C_buf^{2 n₀}`（`hclass`、`hslab` 为 Window 孪生内部已有的事实）。 -/
theorem pairEDist_window_of_CC_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hCC : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ (θbar : ℝ) (n₀ : ℕ), 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        Set.ncard {e : Fin H.eventCount |
          ∃ (hf : H.activeStage a ≤ e.castSucc)
            (hl : e.succ ≤ H.activeStage t)
            (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ (θbar : ℝ) (n₀ : ℕ), 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y x : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y)
        (A' : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A'.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        params.modelAccuracy ≤ 1 / 2 → StandardCap.transitionEnd + 10 < params.modelRadius →
        (∀ (e : Fin H.eventCount) (b b' : (H.event e).RetainedBoundaryIndex),
          b ≠ b' → ∀ y z : standardCapWindow params.modelRadius,
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
            ((records n e).static b).window y ≠ ((records n e).static b').window z) →
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {X : ℝ≥0∞},
        (∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t),
          (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records n e).static b).window ''
              {y : standardCapWindow params.modelRadius |
                ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)) →
        (∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t),
          (∀ b, A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records n e).static b).window ''
              {y : standardCapWindow params.modelRadius |
                ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)) →
        (∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
          (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
          (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
            A.pairEDist_CXSP (hat := hat) A' s has hst < X) →
          A.pairEDist_CXSP (hat := hat) A' v hav hvt ≤
            A.pairEDist_CXSP (hat := hat) A' w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v))) →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
          A.pairEDist_CXSP (hat := hat) A' s has hst < X) →
        A.pairEDist_CXSP (hat := hat) A' v hav hvt ≤
          ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
              ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
                (StandardCap.transitionEnd + 11) ^ 2)))
              (4 * (StandardCap.transitionEnd + 11) *
                (StandardCap.transitionEnd + 13))) ^ (2 * n₀) *
            (A.pairEDist_CXSP (hat := hat) A' t hat le_rfl +
              ENNReal.ofReal (Λ * ((t : ℝ) - v))) := by
  obtain ⟨ε₀, hε₀, θbar, n₀, hθbar, hCC⟩ := hCC
  refine ⟨ε₀, hε₀, θbar, n₀, hθbar, ?_⟩
  intro pBase Γf S F hT q hdiag hacc hrad hord params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  have hm := hCC S F hT q hdiag hacc hrad hord params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  obtain ⟨T₀, hT₀, hmain⟩ := hm
  refine ⟨T₀, hT₀, ?_⟩
  intro n θ hθ hθB H t ht Q hQ a hat hwin y x A A' hRA hRA' hε hD hdisj Λ hΛ X
    hclassA hclassA' hslab
  have hcA := hmain n θ hθ hθB t ht Q hQ a hat hwin y A hRA
  have hcB := hmain n θ hθ hθB t ht Q hQ a hat hwin x A' hRA'
  exact pairEDist_window_of_largeCap_count_C11SP (H := H)
    (a := a) (t := t) (hat := hat) (params := params) (records n) (h6 n) (h5 n) hε hD
    hdisj A A' hΛ n₀ hclassA hclassA' hcA hcB hslab

end GC.LongTime.Ch11
