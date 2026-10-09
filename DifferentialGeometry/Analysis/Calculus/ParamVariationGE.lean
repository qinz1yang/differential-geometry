import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.Compact

/-!
# 参数族积分的一阶 / 二阶变分（纯分析；S-W-GEO G2）

`f(ε) = ∫₀ᴸ F(ε, s) ds`，`ε ∈ [−ε₀, ε₀]`，`f(0) ≤ f(ε)`。**不对积分号下求导**，只用逐点的
中值定理（Taylor 型）+ `(ε, s)` 的紧集上的一致连续性：

* `sym_second_diff_GE`：`F(ε) + F(−ε) − 2F(0) = ε² F″(ξ)`（`ξ ∈ [−ε, ε]`；两次中值定理）；
* `integral_second_nonneg_GE`：`F″ = G2` 联合连续 ⇒ `0 ≤ ∫₀ᴸ G2(0, s) ds`（二阶变分非负）；
* `integral_first_eq_zero_GE`：`F′ = G1` 联合连续 ⇒ `∫₀ᴸ G1(0, s) ds = 0`（一阶变分为零）。

`F`、`G1`、`G2` 是显式函数参数（`G1`、`G2` 由下游给出显式公式），没有新结构 / 新 Prop。
-/

set_option autoImplicit false

open Set intervalIntegral

namespace DifferentialGeometry.Analysis

/-- 对称二阶差分的中值公式：`F(ε) + F(−ε) − 2F(0) = ε² G2(ξ)`，`ξ ∈ [−ε, ε]`。 -/
theorem sym_second_diff_GE {F G1 G2 : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h1 : ∀ t ∈ Icc (-ε) ε, HasDerivAt F (G1 t) t)
    (h2 : ∀ t ∈ Icc (-ε) ε, HasDerivAt G1 (G2 t) t) :
    ∃ ξ ∈ Icc (-ε) ε, F ε + F (-ε) - 2 * F 0 = ε ^ 2 * G2 ξ := by
  set g : ℝ → ℝ := fun t => F t + F (-t) - 2 * F 0 with hg
  have hgd : ∀ t ∈ Icc (-ε) ε, HasDerivAt g (G1 t - G1 (-t)) t := by
    intro t ht
    have hneg : HasDerivAt (fun t => F (-t)) (-(G1 (-t))) t := by
      have h := (h1 (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).scomp t (hasDerivAt_neg t)
      exact h.congr_deriv (by simp)
    have h := ((h1 t ht).add hneg).sub_const (2 * F 0)
    convert h using 1
  have hgc : ContinuousOn g (Icc 0 ε) := fun t ht =>
    (hgd t ⟨by linarith [ht.1], ht.2⟩).continuousAt.continuousWithinAt
  have hG1c : ∀ c : ℝ, 0 < c → c ≤ ε → ContinuousOn G1 (Icc (-c) c) := fun c hc hce t ht =>
    (h2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcm⟩ := exists_ratio_hasDerivAt_eq_ratio_slope g (fun t => G1 t - G1 (-t))
    hε hgc (fun x hx => hgd x ⟨by linarith [hx.1], hx.2.le⟩) (fun t => t ^ 2) (fun t => 2 * t)
    (continuousOn_pow 2) (fun x _ => by simpa using hasDerivAt_pow 2 x)
  have hcε : c < ε := hc.2
  have hg0 : g 0 = 0 := by simp only [hg, neg_zero]; ring
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope G1 G2 (by linarith [hc.1] : -c < c)
    (hG1c c hc.1 hcε.le) (fun x hx => h2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  refine ⟨ξ, ⟨by linarith [hξ.1], by linarith [hξ.2]⟩, ?_⟩
  rw [hg0] at hcm
  have hc0 : 0 < c := hc.1
  have h3 : G1 c - G1 (-c) = 2 * c * G2 ξ := by
    rw [hξe]
    field_simp
    ring
  have h4 : (ε ^ 2 - 0 ^ 2) * (G1 c - G1 (-c)) = (g ε - 0) * (2 * c) := hcm
  have h5 : g ε * (2 * c) = ε ^ 2 * G2 ξ * (2 * c) := by
    rw [h3] at h4
    nlinarith [h4]
  have h6 : g ε = ε ^ 2 * G2 ξ := by
    have := mul_right_cancel₀ (by positivity : (2 * c) ≠ 0) h5
    exact this
  simpa [hg] using h6

/-- 一致连续性的使用形式：紧集 `[−ε₀, ε₀] × [0, L]` 上联合连续的 `G` 对每个 `η > 0` 有 `δ > 0`，
使 `|ξ| < δ` ⇒ `∀ s ∈ [0, L], |G ξ s − G 0 s| < η`。 -/
theorem uniform_in_second_GE {G : ℝ → ℝ → ℝ} {L ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc (-ε₀) ε₀ ×ˢ Icc 0 L))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ξ ∈ Icc (-ε₀) ε₀, |ξ| < δ → ∀ s ∈ Icc 0 L, |G ξ s - G 0 s| < η := by
  have hK : IsCompact (Icc (-ε₀) ε₀ ×ˢ Icc (0 : ℝ) L) :=
    isCompact_Icc.prod isCompact_Icc
  have hu := hK.uniformContinuousOn_of_continuous hG
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1 hu η hη
  refine ⟨δ, hδ, fun ξ hξ hξδ s hs => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc (-ε₀) ε₀ := ⟨by linarith, hε₀.le⟩
  have := h (ξ, s) ⟨hξ, hs⟩ (0, s) ⟨h0, hs⟩ (by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, sub_self, abs_zero]
    exact max_lt hξδ hδ)
  simpa [Real.dist_eq] using this

/-- 二阶变分非负：`F(0) ≤ F(ε)`（积分意义），`F″ = G2` 联合连续 ⇒ `0 ≤ ∫₀ᴸ G2(0, s) ds`。 -/
theorem integral_second_nonneg_GE {F G1 G2 : ℝ → ℝ → ℝ} {L ε₀ : ℝ} (hL : 0 ≤ L) (hε₀ : 0 < ε₀)
    (h1 : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc (-ε₀) ε₀, HasDerivAt (fun ε => F ε s) (G1 t s) t)
    (h2 : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc (-ε₀) ε₀, HasDerivAt (fun ε => G1 ε s) (G2 t s) t)
    (hG2 : ContinuousOn (fun p : ℝ × ℝ => G2 p.1 p.2) (Icc (-ε₀) ε₀ ×ˢ Icc 0 L))
    (hFc : ∀ ε ∈ Icc (-ε₀) ε₀, ContinuousOn (F ε) (Icc 0 L))
    (hmin : ∀ ε ∈ Icc (-ε₀) ε₀, ∫ s in (0 : ℝ)..L, F 0 s ≤ ∫ s in (0 : ℝ)..L, F ε s) :
    0 ≤ ∫ s in (0 : ℝ)..L, G2 0 s := by
  by_contra hneg'
  have hneg := not_le.mp hneg'
  set m : ℝ := -∫ s in (0 : ℝ)..L, G2 0 s with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  have hL1 : 0 < L + 1 := by linarith
  set η : ℝ := m / (2 * (L + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hu⟩ := uniform_in_second_GE hε₀ hG2 hηpos
  set ε : ℝ := min (δ / 2) ε₀ with hε
  have hεpos : 0 < ε := lt_min (by positivity) hε₀
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεε₀ : ε ≤ ε₀ := min_le_right _ _
  have hmemε : ε ∈ Icc (-ε₀) ε₀ := ⟨by linarith, hεε₀⟩
  have hmemn : -ε ∈ Icc (-ε₀) ε₀ := ⟨by linarith, by linarith⟩
  have hpt : ∀ s ∈ Icc 0 L, F ε s + F (-ε) s - 2 * F 0 s ≤ ε ^ 2 * (G2 0 s + η) := by
    intro s hs
    obtain ⟨ξ, hξ, hξe⟩ := sym_second_diff_GE (F := fun e => F e s) (G1 := fun e => G1 e s)
      (G2 := fun e => G2 e s) hεpos (fun t ht => h1 s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (fun t ht => h2 s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hξabs : |ξ| < δ := by
      rw [abs_lt]
      constructor <;> linarith [hξ.1, hξ.2]
    have hb := hu ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ hξabs s hs
    rw [abs_lt] at hb
    rw [hξe]
    nlinarith [sq_nonneg ε, hb.2]
  have hint : ∀ e ∈ Icc (-ε₀) ε₀, IntervalIntegrable (F e) MeasureTheory.volume 0 L := fun e he =>
    ((hFc e he).intervalIntegrable_of_Icc hL)
  have hG2int : IntervalIntegrable (G2 0) MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable_of_Icc hL
    intro s hs
    have : ContinuousWithinAt (fun p : ℝ × ℝ => G2 p.1 p.2) (Icc (-ε₀) ε₀ ×ˢ Icc 0 L) (0, s) :=
      hG2 (0, s) ⟨⟨by linarith, hε₀.le⟩, hs⟩
    exact this.comp (continuousWithinAt_const.prodMk continuousWithinAt_id) (fun x hx =>
      ⟨⟨by linarith, hε₀.le⟩, hx⟩) |>.mono_of_mem_nhdsWithin self_mem_nhdsWithin
  have hlow : 0 ≤ ∫ s in (0 : ℝ)..L, (F ε s + F (-ε) s - 2 * F 0 s) := by
    rw [intervalIntegral.integral_sub ((hint ε hmemε).add (hint (-ε) hmemn))
      ((hint 0 ⟨by linarith, hε₀.le⟩).const_mul 2),
      intervalIntegral.integral_add (hint ε hmemε) (hint (-ε) hmemn),
      intervalIntegral.integral_const_mul]
    linarith [hmin ε hmemε, hmin (-ε) hmemn]
  have hup : ∫ s in (0 : ℝ)..L, (F ε s + F (-ε) s - 2 * F 0 s) ≤
      ∫ s in (0 : ℝ)..L, ε ^ 2 * (G2 0 s + η) := by
    apply intervalIntegral.integral_mono_on hL
    · exact ((hint ε hmemε).add (hint (-ε) hmemn)).sub ((hint 0 ⟨by linarith, hε₀.le⟩).const_mul 2)
    · exact (hG2int.add intervalIntegrable_const).const_mul _
    · exact hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hG2int
    intervalIntegrable_const] at hup
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hup
  have hηL : η * L ≤ m / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hmpos]
  have hfin : ε ^ 2 * (-m + η * L) < 0 := by
    have : -m + η * L < 0 := by linarith
    exact mul_neg_of_pos_of_neg (by positivity) this
  have hz : ∫ s in (0 : ℝ)..L, G2 0 s = -m := by rw [hm]; ring
  rw [hz] at hup
  nlinarith [hlow, hup, hfin]

/-- 一阶变分为零：`F(0) ≤ F(ε)`（积分意义），`F′ = G1` 联合连续 ⇒ `∫₀ᴸ G1(0, s) ds = 0`。 -/
theorem integral_first_eq_zero_GE {F G1 : ℝ → ℝ → ℝ} {L ε₀ : ℝ} (hL : 0 ≤ L) (hε₀ : 0 < ε₀)
    (h1 : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc (-ε₀) ε₀, HasDerivAt (fun ε => F ε s) (G1 t s) t)
    (hG1 : ContinuousOn (fun p : ℝ × ℝ => G1 p.1 p.2) (Icc (-ε₀) ε₀ ×ˢ Icc 0 L))
    (hFc : ∀ ε ∈ Icc (-ε₀) ε₀, ContinuousOn (F ε) (Icc 0 L))
    (hmin : ∀ ε ∈ Icc (-ε₀) ε₀, ∫ s in (0 : ℝ)..L, F 0 s ≤ ∫ s in (0 : ℝ)..L, F ε s) :
    ∫ s in (0 : ℝ)..L, G1 0 s = 0 := by
  have h00 : (0 : ℝ) ∈ Icc (-ε₀) ε₀ := ⟨by linarith, hε₀.le⟩
  have hG1int : IntervalIntegrable (G1 0) MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable_of_Icc hL
    intro s hs
    have : ContinuousWithinAt (fun p : ℝ × ℝ => G1 p.1 p.2) (Icc (-ε₀) ε₀ ×ˢ Icc 0 L) (0, s) :=
      hG1 (0, s) ⟨h00, hs⟩
    exact this.comp (continuousWithinAt_const.prodMk continuousWithinAt_id) (fun x hx =>
      ⟨h00, hx⟩) |>.mono_of_mem_nhdsWithin self_mem_nhdsWithin
  have hint : ∀ e ∈ Icc (-ε₀) ε₀, IntervalIntegrable (F e) MeasureTheory.volume 0 L := fun e he =>
    ((hFc e he).intervalIntegrable_of_Icc hL)
  have key : ∀ η > 0, |∫ s in (0 : ℝ)..L, G1 0 s| ≤ η * L := by
    intro η hη
    obtain ⟨δ, hδ, hu⟩ := uniform_in_second_GE hε₀ hG1 hη
    set e : ℝ := min (δ / 2) ε₀ with he
    have hepos : 0 < e := lt_min (by positivity) hε₀
    have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have heε₀ : e ≤ ε₀ := min_le_right _ _
    have hmemp : e ∈ Icc (-ε₀) ε₀ := ⟨by linarith, heε₀⟩
    have hmemn : -e ∈ Icc (-ε₀) ε₀ := ⟨by linarith, by linarith⟩
    have hptp : ∀ s ∈ Icc 0 L, F e s - F 0 s ≤ e * (G1 0 s + η) := by
      intro s hs
      obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun t => F t s) (fun t => G1 t s) hepos
        (fun t ht => (h1 s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt
          |>.continuousWithinAt)
        (fun t ht => h1 s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      have hb := hu ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
        (by rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2]) s hs
      rw [abs_lt] at hb
      have : F e s - F 0 s = e * G1 ξ s := by
        have hne : e ≠ 0 := hepos.ne'
        rw [hξe, sub_zero]
        field_simp
      rw [this]
      nlinarith [hb.2]
    have hptn : ∀ s ∈ Icc 0 L, F (-e) s - F 0 s ≤ -e * G1 0 s + e * η := by
      intro s hs
      obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun t => F t s) (fun t => G1 t s)
        (by linarith : -e < 0)
        (fun t ht => (h1 s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt
          |>.continuousWithinAt)
        (fun t ht => h1 s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      have hb := hu ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
        (by rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2]) s hs
      rw [abs_lt] at hb
      have : F (-e) s - F 0 s = -e * G1 ξ s := by
        have hne : e ≠ 0 := hepos.ne'
        have h' : G1 ξ s * e = F 0 s - F (-e) s := by
          rw [hξe, zero_sub, neg_neg]
          field_simp
        linarith
      rw [this]
      nlinarith [hb.1]
    have hup1 : ∫ s in (0 : ℝ)..L, (F e s - F 0 s) ≤ ∫ s in (0 : ℝ)..L, e * (G1 0 s + η) :=
      intervalIntegral.integral_mono_on hL ((hint e hmemp).sub (hint 0 h00))
        ((hG1int.add intervalIntegrable_const).const_mul _) hptp
    have hup2 : ∫ s in (0 : ℝ)..L, (F (-e) s - F 0 s) ≤
        ∫ s in (0 : ℝ)..L, (-e * G1 0 s + e * η) :=
      intervalIntegral.integral_mono_on hL ((hint (-e) hmemn).sub (hint 0 h00))
        ((hG1int.const_mul _).add intervalIntegrable_const) hptn
    rw [intervalIntegral.integral_sub (hint e hmemp) (hint 0 h00)] at hup1
    rw [intervalIntegral.integral_sub (hint (-e) hmemn) (hint 0 h00)] at hup2
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hG1int
      intervalIntegrable_const] at hup1
    rw [intervalIntegral.integral_add (hG1int.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul] at hup2
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hup1 hup2
    have hm1 := hmin e hmemp
    have hm2 := hmin (-e) hmemn
    rw [abs_le]
    constructor
    · nlinarith [hepos]
    · nlinarith [hepos]
  by_contra hne
  have habs : 0 < |∫ s in (0 : ℝ)..L, G1 0 s| := abs_pos.2 hne
  have hk := key (|∫ s in (0 : ℝ)..L, G1 0 s| / (2 * (L + 1))) (by positivity)
  have : |∫ s in (0 : ℝ)..L, G1 0 s| / (2 * (L + 1)) * L < |∫ s in (0 : ℝ)..L, G1 0 s| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end DifferentialGeometry.Analysis
