import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceLeftWindowCXSP

set_option autoImplicit false

/-!
# CX-SPINE G18：已有 trace pair 的整史首次退出

输入是尚未退出的整个开后缀上的定量距离估计；不是把最终 footprint 当作前提。
由尚未退出的后缀提供当前 birth 的保护，实际 crossings 支付其左延拓，同一 stage 的 closed endpoint 支付其余点。
本定理不生产条件距离估计、endpoint protection 或 trace 存在性。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

/-- 跨全部实际 stages 的首次退出：开后缀距离估计和 protected crossings 给整窗定量界。 -/
theorem pair_distance_of_unexited_suffix_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p q : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hOld : ∀ e : Fin H.eventCount,
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hacc : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {X : ℝ≥0∞}
    (hprot : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a < v) (_hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
        (hl : e.succ ≤ H.activeStage t), H.time e.succ = (v : ℝ) → ∀ b,
      A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hmargin : A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
      ENNReal.ofReal (Λ * ((t : ℝ) - a)) < X)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
      A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal (Λ * ((t : ℝ) - v))) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
        A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
          A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal (Λ * ((t : ℝ) - v)) := by
  classical
  let D : ℝ → ℝ≥0∞ := fun s => if hs : s ∈ Icc (a : ℝ) (t : ℝ) then
    A.pairEDist_CXSP (hat := hat) B
      ⟨s, a.2.1.trans hs.1, hs.2.trans t.2.2⟩ hs.1 hs.2 else 0
  have hDval (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      D v = A.pairEDist_CXSP (hat := hat) B v hav hvt := by
    simp only [D, dite_eq_left (show (v : ℝ) ∈ Icc (a : ℝ) (t : ℝ) from ⟨hav, hvt⟩)]
  have hmarginD : D t + ENNReal.ofReal (Λ * ((t : ℝ) - a)) < X := by
    rw [hDval t hat le_rfl]
    exact hmargin
  have hstep (s : ℝ) (hs : s ∈ Icc (a : ℝ) (t : ℝ))
      (hstay : ∀ w ∈ Ioo s (t : ℝ), D w < X) :
      D s ≤ D t + ENNReal.ofReal (Λ * ((t : ℝ) - s)) := by
    let v : Icc (0 : ℝ) H.horizon := ⟨s, a.2.1.trans hs.1, hs.2.trans t.2.2⟩
    have hb := hbound v hs.1 hs.2 (fun w haw hwt hvw hwt' => by
      rw [← hDval w haw hwt]
      exact hstay w ⟨hvw, hwt'⟩)
    simpa only [← hDval v hs.1 hs.2, ← hDval t hat le_rfl] using hb
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ t ∧ ∀ w ∈ Icc s (t : ℝ), D w < X}
  have htS : (t : ℝ) ∈ S := by
    refine ⟨hat, le_rfl, ?_⟩
    intro w hw
    obtain rfl : w = (t : ℝ) := le_antisymm hw.2 hw.1
    exact le_self_add.trans_lt hmarginD
  have hne : S.Nonempty := ⟨t, htS⟩
  have hbdd : BddBelow S := ⟨a, fun s hs => hs.1⟩
  have hastar : (a : ℝ) ≤ sInf S := le_csInf hne fun s hs => hs.1
  have hstart : sInf S ≤ (t : ℝ) := csInf_le hbdd htS
  have hup : ∀ w ∈ Ioc (sInf S) (t : ℝ), D w < X := by
    intro w hw
    obtain ⟨s, hsS, hsw⟩ := exists_lt_of_csInf_lt hne hw.1
    exact hsS.2.2 w ⟨hsw.le, hw.2⟩
  have hstar_lt : D (sInf S) < X :=
    ((hstep (sInf S) ⟨hastar, hstart⟩ (fun w hw => hup w ⟨hw.1, hw.2.le⟩)).trans
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (sub_le_sub_left hastar _) hΛ)))).trans_lt hmarginD
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
    have hpost : A.pairEDist_CXSP (hat := hat) B v hlt.le hstart < X := by
      rw [← hDval v hlt.le hstart]
      exact hstar_lt
    obtain ⟨d, hd, hnear⟩ := A.exists_left_pair_distance_window_CXSP (hat := hat) B
      records hOld hcan hacc hD v hlt hstart (hprot v hlt hstart (by
        intro w haw hwt hvw hwt'
        rw [← hDval w haw hwt]
        exact hup w ⟨hvw, hwt'.le⟩)) hpost
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
