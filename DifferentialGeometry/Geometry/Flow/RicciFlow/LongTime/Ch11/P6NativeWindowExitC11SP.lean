import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapCrossingRecordC11SP

set_option autoImplicit false

/-!
# 乘性 first-exit（O-CH11-NATIVE-WINDOW G1a，后缀 `_C11SP`）

CXSP `pair_distance_of_unexited_suffix_CXSP` / `exists_left_pair_distance_window_CXSP` 的乘性孪生。
原件在 crossing 处要求两端点受保护（(D4)，左极限不增）；native 下大 cap buffer crossing 只有
(D4′) 左极限形 `∀ δ > 0, ∀ᶠ s ↑ τ_e, d_{e⁻,s} ≤ c·d_{e⁺,τ_e} + δ`（`c = C_buf ≥ 1`），
故左延拓要求严格余量 `c·d_v < X`（`exists_left_pair_distance_window_mul_C11SP`），
first-exit 的余量改为 `c·K·(d_t + Λ(t − a)) < X`，条件链为乘性 `d_v ≤ K·(d_t + Λ(t − v))`
（`pair_distance_of_unexited_suffix_mul_C11SP`；`K = C_buf^{2n₀}` 由 CC 计数给出）。
两个定理都是纯 first-exit 拓扑论证，**PROVED**，0 合同 binder。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
  {p q : (H.stageAt t).Carrier}

/-- **乘性左延拓（PROVED）**：`v` 处若是 crossing 出生时刻，用 (D4′) 左极限形 `hev`（因子 `c ≥ 1`）；
严格余量 `c·d_v < X` ⇒ `v` 左侧一小段上 `d < X`。slab 内部点同原件（`d_v ≤ c·d_v`）。 -/
theorem exists_left_pair_distance_window_mul_C11SP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {c X : ℝ≥0∞} (hc : 1 ≤ c)
    (v : Icc (0 : ℝ) H.horizon) (hav : a < v) (hvt : v ≤ t)
    (hev : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t), H.time e.succ = (v : ℝ) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ s in 𝓝[<] H.time e.succ,
        riemannianEDistOf (H.stageMetric e.castSucc s)
            (A.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl))
            (B.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl)) ≤
          c * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
            (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) + ENNReal.ofReal δ)
    (hpost : c * A.pairEDist_CXSP (hat := hat) B v hav.le hvt < X) :
    ∃ d ∈ Ico (a : ℝ) (v : ℝ),
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        d < (w : ℝ) → w < v → A.pairEDist_CXSP (hat := hat) B w haw hwt < X := by
  by_cases hage : H.time (H.activeStage v) < (v : ℝ)
  · have hpost1 : A.pairEDist_CXSP (hat := hat) B v hav.le hvt < X :=
      (le_mul_of_one_le_left zero_le hc).trans_lt hpost
    obtain ⟨d, hd, hnear⟩ := H.exists_stage_left_window_CXSP v hage
      (A.point (H.activeStage v) (H.activeStage_mono hav.le) (H.activeStage_mono hvt))
      (B.point (H.activeStage v) (H.activeStage_mono hav.le) (H.activeStage_mono hvt)) hpost1
    refine ⟨max (a : ℝ) d, ⟨le_max_left _ _, max_lt hav hd.2⟩, ?_⟩
    intro w haw hwt hdw hwv
    have hdw' : d < (w : ℝ) := (le_max_right _ _).trans_lt hdw
    have hact : H.activeStage w = H.activeStage v :=
      H.activeStage_eq_of_time_le_C11G w v (hd.1.trans hdw'.le) hwv.le
    rw [pairEDist_eq_of_activeStage_C11SP A B w haw hwt _ hact
      ((H.activeStage_mono hav.le)) (H.activeStage_mono hvt)]
    exact hnear w ⟨hdw', hwv⟩
  · have hbirth : H.time (H.activeStage v) = (v : ℝ) :=
      le_antisymm (H.activeStage_time_le v) (le_of_not_gt hage)
    have hnzero : H.activeStage v ≠ 0 := by
      intro hz
      have hvzero : (v : ℝ) = 0 := by simpa only [hz, H.time_zero] using hbirth.symm
      have hav' : (a : ℝ) < v := hav
      linarith [a.2.1]
    obtain ⟨e, he⟩ := Fin.exists_succ_eq_of_ne_zero hnzero
    have htime : H.time e.succ = (v : ℝ) := by rw [he]; exact hbirth
    have hf : H.activeStage a ≤ e.castSucc :=
      Fin.le_castSucc_iff.mpr (H.time_strictMono.lt_iff_lt.mp
        (((H.activeStage_time_le a).trans_lt hav).trans_eq htime.symm))
    have hl : e.succ ≤ H.activeStage t := he.le.trans (H.activeStage_mono hvt)
    have hpost' : c * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
        (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
        (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) < X := by
      rw [htime]
      rwa [pairEDist_eq_of_activeStage_C11SP A B v hav.le hvt e.succ he.symm
        (hf.trans e.castSucc_lt_succ.le) hl] at hpost
    obtain ⟨r, hr, hrX⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hpost'
    have hδ : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
    have hevr := hev e hf hl htime (r : ℝ) hδ
    obtain ⟨l, hlτ, hlI⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hevr
    have hcs : H.time e.castSucc < H.time e.succ := H.time_strictMono e.castSucc_lt_succ
    let d := max (H.time e.castSucc) l
    have hdτ : d < H.time e.succ := max_lt hcs hlτ
    have hdv : d < (v : ℝ) := hdτ.trans_eq htime
    refine ⟨max (a : ℝ) d, ⟨le_max_left _ _, max_lt hav hdv⟩, ?_⟩
    intro w haw hwt hdw hwv
    have hdw' : d < (w : ℝ) := (le_max_right _ _).trans_lt hdw
    have hwτ : (w : ℝ) < H.time e.succ := (show (w : ℝ) < v from hwv).trans_eq htime.symm
    have hact : H.activeStage w = e.castSucc :=
      H.activeStage_eq_castSucc_C11G e w ((le_max_left _ _).trans hdw'.le) hwτ
    rw [pairEDist_eq_of_activeStage_C11SP A B w haw hwt e.castSucc hact hf
      (e.castSucc_lt_succ.le.trans hl)]
    have hmem := hlI ⟨(le_max_right _ _).trans_lt hdw', hwτ⟩
    refine lt_of_le_of_lt hmem ?_
    rw [ENNReal.ofReal_coe_nnreal]
    exact hrX

/-- **乘性 first-exit（PROVED）**：条件链 `hbound`（`(v, t)` 上 `d < X` ⇒ `d_v ≤ K·(d_t + Λ(t − v))`）
+ crossing 出生时刻的 (D4′) 左极限 `hev`（条件化在 stay 上）+ 余量 `c·K·(d_t + Λ(t − a)) < X`
⇒ 整窗 `d_v < X` 且乘性链成立。 -/
theorem pair_distance_of_unexited_suffix_mul_C11SP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {c K X : ℝ≥0∞} (hc : 1 ≤ c) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hev : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a < v) (_hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t), H.time e.succ = (v : ℝ) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ s in 𝓝[<] H.time e.succ,
        riemannianEDistOf (H.stageMetric e.castSucc s)
            (A.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl))
            (B.point e.castSucc hf (e.castSucc_lt_succ.le.trans hl)) ≤
          c * riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
            (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) + ENNReal.ofReal δ)
    (hmargin : c * (K * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
      ENNReal.ofReal (Λ * ((t : ℝ) - a)))) < X)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        K * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal (Λ * ((t : ℝ) - v)))) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
        A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
          K * (A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal (Λ * ((t : ℝ) - v))) := by
  classical
  let D : ℝ → ℝ≥0∞ := fun s => if hs : s ∈ Icc (a : ℝ) (t : ℝ) then
    A.pairEDist_CXSP (hat := hat) B
      ⟨s, a.2.1.trans hs.1, hs.2.trans t.2.2⟩ hs.1 hs.2 else 0
  have hDval (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      D v = A.pairEDist_CXSP (hat := hat) B v hav hvt := by
    simp only [D, dite_eq_left (show (v : ℝ) ∈ Icc (a : ℝ) (t : ℝ) from ⟨hav, hvt⟩)]
  have hmono (s : ℝ) (hs : (a : ℝ) ≤ s) :
      K * (D t + ENNReal.ofReal (Λ * ((t : ℝ) - s))) ≤
        K * (D t + ENNReal.ofReal (Λ * ((t : ℝ) - a))) :=
    mul_le_mul_right (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hs _) hΛ))) _
  have hmarginD : c * (K * (D t + ENNReal.ofReal (Λ * ((t : ℝ) - a)))) < X := by
    rw [hDval t hat le_rfl]
    exact hmargin
  have hstep (s : ℝ) (hs : s ∈ Icc (a : ℝ) (t : ℝ))
      (hstay : ∀ w ∈ Ioo s (t : ℝ), D w < X) :
      D s ≤ K * (D t + ENNReal.ofReal (Λ * ((t : ℝ) - s))) := by
    let v : Icc (0 : ℝ) H.horizon := ⟨s, a.2.1.trans hs.1, hs.2.trans t.2.2⟩
    have hb := hbound v hs.1 hs.2 (fun w haw hwt hvw hwt' => by
      rw [← hDval w haw hwt]
      exact hstay w ⟨hvw, hwt'⟩)
    simpa only [← hDval v hs.1 hs.2, ← hDval t hat le_rfl] using hb
  have hcD (s : ℝ) (hs : s ∈ Icc (a : ℝ) (t : ℝ))
      (hstay : ∀ w ∈ Ioo s (t : ℝ), D w < X) : c * D s < X :=
    ((mul_le_mul_right ((hstep s hs hstay).trans (hmono s hs.1)) c)).trans_lt hmarginD
  have hDlt (s : ℝ) (hs : s ∈ Icc (a : ℝ) (t : ℝ))
      (hstay : ∀ w ∈ Ioo s (t : ℝ), D w < X) : D s < X :=
    (le_mul_of_one_le_left zero_le hc).trans_lt (hcD s hs hstay)
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ t ∧ ∀ w ∈ Icc s (t : ℝ), D w < X}
  have htS : (t : ℝ) ∈ S := by
    refine ⟨hat, le_rfl, ?_⟩
    intro w hw
    obtain rfl : w = (t : ℝ) := le_antisymm hw.2 hw.1
    exact hDlt _ ⟨hat, le_rfl⟩ (fun w hw => absurd hw.2 (not_lt_of_gt hw.1))
  have hne : S.Nonempty := ⟨t, htS⟩
  have hbdd : BddBelow S := ⟨a, fun s hs => hs.1⟩
  have hastar : (a : ℝ) ≤ sInf S := le_csInf hne fun s hs => hs.1
  have hstart : sInf S ≤ (t : ℝ) := csInf_le hbdd htS
  have hup : ∀ w ∈ Ioc (sInf S) (t : ℝ), D w < X := by
    intro w hw
    obtain ⟨s, hsS, hsw⟩ := exists_lt_of_csInf_lt hne hw.1
    exact hsS.2.2 w ⟨hsw.le, hw.2⟩
  have hupo : ∀ w ∈ Ioo (sInf S) (t : ℝ), D w < X := fun w hw => hup w ⟨hw.1, hw.2.le⟩
  have hstar_lt : D (sInf S) < X := hDlt _ ⟨hastar, hstart⟩ hupo
  have hstarS : sInf S ∈ S := by
    refine ⟨hastar, hstart, ?_⟩
    intro w hw
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h]
      exact hstar_lt
    · exact hup w ⟨h, hw.2⟩
  have hstar_eq : sInf S = (a : ℝ) := by
    by_contra hneq
    have hlt : (a : ℝ) < sInf S := lt_of_le_of_ne hastar (Ne.symm hneq)
    let v : Icc (0 : ℝ) H.horizon :=
      ⟨sInf S, a.2.1.trans hastar, hstart.trans t.2.2⟩
    have hstayv : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X := by
      intro w haw hwt hvw hwt'
      rw [← hDval w haw hwt]
      exact hupo w ⟨hvw, hwt'⟩
    have hpost : c * A.pairEDist_CXSP (hat := hat) B v hlt.le hstart < X := by
      rw [← hDval v hlt.le hstart]
      exact hcD _ ⟨hastar, hstart⟩ hupo
    obtain ⟨d, hd, hnear⟩ := exists_left_pair_distance_window_mul_C11SP (hat := hat) A B hc
      v hlt hstart (fun e hf hl he => hev v hlt hstart hstayv e hf hl he) hpost
    let d' := (d + sInf S) / 2
    have hdd' : d < d' := by dsimp [d']; linarith [hd.2]
    have hd's : d' < sInf S := by dsimp [d']; linarith [hd.2]
    have had' : (a : ℝ) ≤ d' := hd.1.trans hdd'.le
    have hd'S : d' ∈ S := by
      refine ⟨had', hd's.le.trans hstart, ?_⟩
      intro w hw
      rcases lt_or_ge w (sInf S) with hwlt | hwge
      · let u : Icc (0 : ℝ) H.horizon :=
          ⟨w, a.2.1.trans (had'.trans hw.1), hw.2.trans t.2.2⟩
        rw [hDval u (had'.trans hw.1) hw.2]
        exact hnear u (had'.trans hw.1) hw.2 (hdd'.trans_le hw.1) hwlt
      · exact hstarS.2.2 w ⟨hwge, hw.2⟩
    have := csInf_le hbdd hd'S
    exact (not_lt_of_ge this) hd's
  intro v hav hvt
  have hstay : ∀ w ∈ Icc (a : ℝ) (t : ℝ), D w < X := by
    simpa only [hstar_eq] using hstarS.2.2
  refine ⟨?_, hbound v hav hvt ?_⟩
  · rw [← hDval v hav hvt]
    exact hstay v ⟨hav, hvt⟩
  · intro w haw hwt _ _
    rw [← hDval w haw hwt]
    exact hstay w ⟨haw, hwt⟩

end GC.LongTime.Ch11
