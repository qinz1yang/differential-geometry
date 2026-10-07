import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.NormalizedUniquenessR5
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# O-MY-R5 G2a：盘的全纯自同构是 Möbius（R5-B(ii) degree-one factor rigidity 的最后一步）

`φ` 在开单位盘 `D°` 上全纯、`MapsTo` / `InjOn` / `SurjOn D° D°` ⇒ `φ = diskMobius_R5 a c`
（`‖a‖ < 1`，`‖c‖ = 1`）。
证明：`φ b = 0`，`ψ := φ ∘ m_{−b}` 固定 0；`ψ` 的逆 `χ` 连续（开映射定理），在 `ψ` 的非临界像处由反函数定理
全纯，临界点孤立 ⇒ 用可去奇点填 ⇒ `χ` 全纯；Schwarz 双向 ⇒ `‖ψ z‖ = ‖z‖` ⇒ `ψ z / z` 模常 1 ⇒ 常数（max modulus）
⇒ identity theorem ⇒ `ψ = c · id`。**不需要**"临界点 ⇒ 非局部单射"的局部结构。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Metric ComplexConjugate
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- `|1 − ā z|² − |z − a|² = (1 − |a|²)(1 − |z|²)`。 -/
theorem normSq_one_sub_conj_mul_sub_normSq_R5 (a z : ℂ) :
    Complex.normSq (1 - conj a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- Möbius 把开盘映进开盘。 -/
theorem norm_diskMobius_lt_one_R5 {a c z : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1) (hz : ‖z‖ < 1) :
    ‖diskMobius_R5 a c z‖ < 1 := by
  have hden := one_sub_conj_mul_ne_zero_R5 ha hz.le
  have hkey := normSq_one_sub_conj_mul_sub_normSq_R5 a z
  have ha2 : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hz2 : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hpos : 0 < Complex.normSq (1 - conj a * z) := Complex.normSq_pos.mpr hden
  have hlt : Complex.normSq (z - a) < Complex.normSq (1 - conj a * z) := by
    nlinarith [mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hz2)]
  have hsq : ‖z - a‖ ^ 2 < ‖1 - conj a * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact hlt
  have hnorm : ‖z - a‖ < ‖1 - conj a * z‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq
  unfold diskMobius_R5
  rw [norm_div, norm_mul, hc, one_mul, div_lt_one (norm_pos_iff.mpr hden)]
  exact hnorm

/-- `m_{−a} ∘ m_a = id` on the closed disk（`m_a := diskMobius_R5 a 1`）。 -/
theorem diskMobius_neg_comp_R5 {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskMobius_R5 (-a) 1 (diskMobius_R5 a 1 z) = z := by
  have hD := one_sub_conj_mul_ne_zero_R5 ha hz
  have h1a : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [Complex.conj_mul']
    intro h
    have hr' : (1 : ℝ) - ‖a‖ ^ 2 = 0 := by exact_mod_cast h
    nlinarith [norm_nonneg a]
  have key : 1 * (z - a) / (1 - conj a * z) * (1 - conj a * z) = z - a := by
    rw [one_mul, div_mul_cancel₀ _ hD]
  unfold diskMobius_R5
  rw [map_neg]
  have hE : 1 - -conj a * (1 * (z - a) / (1 - conj a * z)) =
      (1 - conj a * a) / (1 - conj a * z) := by
    rw [eq_div_iff hD]
    linear_combination (conj a) * key
  have hN : 1 * (1 * (z - a) / (1 - conj a * z) - -a) =
      z * (1 - conj a * a) / (1 - conj a * z) := by
    rw [eq_div_iff hD]
    linear_combination key
  rw [hE, hN, div_div_div_cancel_right₀ hD, mul_div_assoc, div_self h1a, mul_one]

/-- `m_a(a) = 0`。 -/
theorem diskMobius_self_R5 (a c : ℂ) : diskMobius_R5 a c a = 0 := by
  simp [diskMobius_R5]

/-- `m_{−a}(0) = a`。 -/
theorem diskMobius_neg_zero_R5 (a : ℂ) : diskMobius_R5 (-a) 1 0 = a := by
  simp [diskMobius_R5]

/-- Möbius 在开盘上全纯。 -/
theorem differentiableOn_diskMobius_R5 {a : ℂ} (ha : ‖a‖ < 1) (c : ℂ) :
    DifferentiableOn ℂ (diskMobius_R5 a c) (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  apply DifferentiableAt.differentiableWithinAt
  unfold diskMobius_R5
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact one_sub_conj_mul_ne_zero_R5 ha hz'

/-- 固定 0 的盘自同构是旋转：`ψ` 在 `D°` 全纯、双射、`ψ 0 = 0` ⇒ `ψ = c · id`，`‖c‖ = 1`。 -/
theorem eq_const_mul_of_bijOn_ball_of_map_zero_R5 {ψ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ ψ (ball 0 1)) (hmaps : MapsTo ψ (ball 0 1) (ball 0 1))
    (hinj : InjOn ψ (ball 0 1)) (hsurj : SurjOn ψ (ball 0 1) (ball 0 1)) (h0 : ψ 0 = 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, ψ z = c * z := by
  classical
  set B : Set ℂ := ball (0 : ℂ) 1 with hB
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball (0 : ℂ) 1).isPreconnected
  have h0B : (0 : ℂ) ∈ B := mem_ball_self one_pos
  have hhalf : ((1 : ℂ) / 2) ∈ B := by
    rw [hB, mem_ball_zero_iff]
    norm_num
  have han : AnalyticOnNhd ℂ ψ B := hd.analyticOnNhd hBo
  -- 逆映射 `χ`
  let χ : ℂ → ℂ := Function.invFunOn ψ B
  have hχB : ∀ w ∈ B, χ w ∈ B := fun w hw => Function.invFunOn_mem (hsurj hw)
  have hψχ : ∀ w ∈ B, ψ (χ w) = w := fun w hw => Function.invFunOn_eq (hsurj hw)
  have hχψ : ∀ z ∈ B, χ (ψ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  -- 开映射
  have hopen : ∀ s ⊆ B, IsOpen s → IsOpen (ψ '' s) := by
    rcases han.is_constant_or_isOpen hBc with ⟨w, hw⟩ | hopen
    · exfalso
      have h1 := hw 0 h0B
      have h2 := hw _ hhalf
      have : (0 : ℂ) = 1 / 2 := hinj h0B hhalf (h1.trans h2.symm)
      norm_num at this
    · exact hopen
  have hχcont : ContinuousOn χ B := by
    rw [continuousOn_open_iff hBo]
    intro t ht
    have heq : B ∩ χ ⁻¹' t = ψ '' (t ∩ B) := by
      ext w
      constructor
      · rintro ⟨hw, hwt⟩
        exact ⟨χ w, ⟨hwt, hχB w hw⟩, hψχ w hw⟩
      · rintro ⟨z, ⟨hzt, hzB⟩, rfl⟩
        refine ⟨hmaps hzB, ?_⟩
        change χ (ψ z) ∈ t
        rw [hχψ z hzB]
        exact hzt
    rw [heq]
    exact hopen _ inter_subset_right (ht.inter hBo)
  -- 非临界点处 `χ` 可微
  have hreg : ∀ w ∈ B, deriv ψ (χ w) ≠ 0 → DifferentiableAt ℂ χ w := by
    intro w hw hne
    have hψd : HasDerivAt ψ (deriv ψ (χ w)) (χ w) :=
      (hd.differentiableAt (hBo.mem_nhds (hχB w hw))).hasDerivAt
    have hfg : ∀ᶠ y in 𝓝 w, ψ (χ y) = y := by
      filter_upwards [hBo.mem_nhds hw] with y hy
      exact hψχ y hy
    exact (HasDerivAt.of_local_left_inverse (hχcont.continuousAt (hBo.mem_nhds hw)) hψd hne
      hfg).differentiableAt
  -- 临界点孤立
  have hiso : ∀ z ∈ B, ∀ᶠ z' in 𝓝[≠] z, deriv ψ z' ≠ 0 := by
    intro z hz
    rcases ((han z hz).deriv).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
        (Filter.inter_mem hzero (hBo.mem_nhds hz))
      have hconst : ∀ x ∈ ball z ε, ∀ y ∈ ball z ε, ψ x = ψ y := by
        intro x hx y hy
        refine isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z ε).isPreconnected
          (hd.mono fun v hv => (hεsub hv).2) (fun v hv => (hεsub hv).1) hx hy
      have hz2 : z + (ε / 2 : ℝ) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hε)]
        exact half_lt_self hε
      have hzz : z = z + (ε / 2 : ℝ) :=
        hinj hz (hεsub hz2).2 (hconst z (mem_ball_self hε) _ hz2)
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have h' := congrArg (fun v => v - z) hzz
        simpa using h'.symm
      have hε2 : ε / 2 = 0 := by exact_mod_cast this
      linarith
    · exact hne
  -- `χ` 在 `B` 上全纯（可去奇点）
  have hχd : DifferentiableOn ℂ χ B := by
    intro w hw
    have hev : ∀ᶠ w' in 𝓝[≠] w, deriv ψ (χ w') ≠ 0 := by
      have ht : Tendsto χ (𝓝[≠] w) (𝓝[≠] (χ w)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (hχcont.continuousAt (hBo.mem_nhds hw)).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds (hBo.mem_nhds hw), self_mem_nhdsWithin]
            with w' hw' hne
          intro heq
          apply hne
          rw [Set.mem_singleton_iff] at heq ⊢
          rw [← hψχ w' hw', ← hψχ w hw, heq]
      exact ht.eventually (hiso (χ w) (hχB w hw))
    rw [eventually_nhdsWithin_iff] at hev
    let s : Set ℂ := {w' | w' ∈ B ∧ (w' ∈ ({w}ᶜ : Set ℂ) → deriv ψ (χ w') ≠ 0)}
    have hs : s ∈ 𝓝 w := Filter.inter_mem (hBo.mem_nhds hw) hev
    have hds : DifferentiableOn ℂ χ (s \ {w}) := by
      rintro w' ⟨⟨hw'B, hw'd⟩, hw'ne⟩
      exact (hreg w' hw'B (hw'd hw'ne)).differentiableWithinAt
    have hfull := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
      ⟨hds, hχcont.continuousAt (hBo.mem_nhds hw)⟩
    exact (hfull.differentiableAt hs).differentiableWithinAt
  -- Schwarz 双向
  have hχ0 : χ 0 = 0 := by
    have := hχψ 0 h0B
    rwa [h0] at this
  have hnorm : ∀ z ∈ B, ‖ψ z‖ = ‖z‖ := by
    intro z hz
    have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have h1 : ‖ψ z‖ ≤ ‖z‖ := Complex.norm_le_norm_of_mapsTo_ball hd
      (fun v hv => ball_subset_closedBall (hmaps hv)) h0 hzlt
    have hψzB := hmaps hz
    have h2 : ‖χ (ψ z)‖ ≤ ‖ψ z‖ := Complex.norm_le_norm_of_mapsTo_ball hχd
      (fun v hv => ball_subset_closedBall (hχB v hv)) hχ0 (mem_ball_zero_iff.mp hψzB)
    rw [hχψ z hz] at h2
    exact le_antisymm h1 h2
  -- `ψ z / z` 在 `ball (1/2) (1/2)` 上模常 1 ⇒ 常数
  set U : Set ℂ := ball ((1 : ℂ) / 2) (1 / 2) with hU
  have hUB : U ⊆ B := by
    intro v hv
    rw [hU, mem_ball, dist_eq_norm] at hv
    rw [hB, mem_ball_zero_iff]
    calc ‖v‖ = ‖(v - 1 / 2) + 1 / 2‖ := by ring_nf
      _ ≤ ‖v - 1 / 2‖ + ‖(1 : ℂ) / 2‖ := norm_add_le _ _
      _ < 1 / 2 + 1 / 2 := by
        have : ‖(1 : ℂ) / 2‖ = 1 / 2 := by norm_num
        rw [this]
        linarith
      _ = 1 := by norm_num
  have hU0 : ∀ v ∈ U, v ≠ 0 := by
    intro v hv h
    rw [hU, h, mem_ball, dist_eq_norm] at hv
    norm_num at hv
  have hcU : ((1 : ℂ) / 2) ∈ U := mem_ball_self (by norm_num)
  let g : ℂ → ℂ := fun v => ψ v / v
  have hgd : DifferentiableOn ℂ g U := fun v hv =>
    ((hd v (hUB hv)).mono hUB).div differentiableWithinAt_id (hU0 v hv)
  have hgn : ∀ v ∈ U, ‖g v‖ = 1 := by
    intro v hv
    change ‖ψ v / v‖ = 1
    rw [norm_div, hnorm v (hUB hv), div_self (norm_ne_zero_iff.mpr (hU0 v hv))]
  have hmax : IsMaxOn (norm ∘ g) U ((1 : ℂ) / 2) := by
    intro v hv
    change ‖g v‖ ≤ ‖g (1 / 2)‖
    rw [hgn v hv, hgn _ hcU]
  have hgc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball _ _).isPreconnected isOpen_ball hgd hcU hmax
  set c : ℂ := g (1 / 2) with hc
  refine ⟨c, hgn _ hcU, ?_⟩
  have hloc : ψ =ᶠ[𝓝 ((1 : ℂ) / 2)] fun v => c * v := by
    filter_upwards [isOpen_ball.mem_nhds hcU] with v hv
    have h := hgc hv
    change ψ v / v = c at h
    rw [← h, div_mul_cancel₀ _ (hU0 v hv)]
  have hlin : AnalyticOnNhd ℂ (fun v : ℂ => c * v) B := fun v _ => by fun_prop
  intro z hz
  exact han.eqOn_of_preconnected_of_eventuallyEq hlin hBc (hUB hcU) hloc hz

/-- **G2a**：开盘的全纯双射自映射是 Möbius。 -/
theorem diskMobius_of_bijOn_ball_R5 {φ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ φ (ball 0 1)) (hmaps : MapsTo φ (ball 0 1) (ball 0 1))
    (hinj : InjOn φ (ball 0 1)) (hsurj : SurjOn φ (ball 0 1) (ball 0 1)) :
    ∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧ EqOn φ (diskMobius_R5 a c) (ball 0 1) := by
  obtain ⟨b, hbB, hb0⟩ := hsurj (mem_ball_self one_pos)
  have hb : ‖b‖ < 1 := mem_ball_zero_iff.mp hbB
  have hnb : ‖-b‖ < 1 := by rwa [norm_neg]
  let m : ℂ → ℂ := diskMobius_R5 (-b) 1
  let m' : ℂ → ℂ := diskMobius_R5 b 1
  have hmB : MapsTo m (ball 0 1) (ball 0 1) := fun z hz =>
    mem_ball_zero_iff.mpr (norm_diskMobius_lt_one_R5 hnb norm_one (mem_ball_zero_iff.mp hz))
  have hm'B : MapsTo m' (ball 0 1) (ball 0 1) := fun z hz =>
    mem_ball_zero_iff.mpr (norm_diskMobius_lt_one_R5 hb norm_one (mem_ball_zero_iff.mp hz))
  have hmm' : ∀ z ∈ ball (0 : ℂ) 1, m (m' z) = z := fun z hz =>
    diskMobius_neg_comp_R5 hb (mem_ball_zero_iff.mp hz).le
  have hm'm : ∀ z ∈ ball (0 : ℂ) 1, m' (m z) = z := by
    intro z hz
    have h := diskMobius_neg_comp_R5 hnb (mem_ball_zero_iff.mp hz).le
    rwa [neg_neg] at h
  let ψ : ℂ → ℂ := fun z => φ (m z)
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) :=
    hd.comp (differentiableOn_diskMobius_R5 hnb 1) hmB
  have hψmaps : MapsTo ψ (ball 0 1) (ball 0 1) := fun z hz => hmaps (hmB hz)
  have hψinj : InjOn ψ (ball 0 1) := by
    intro x hx y hy hxy
    have h := hinj (hmB hx) (hmB hy) hxy
    rw [← hm'm x hx, ← hm'm y hy, h]
  have hψsurj : SurjOn ψ (ball 0 1) (ball 0 1) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hsurj hw
    exact ⟨m' x, hm'B hx, by change φ (m (m' x)) = φ x; rw [hmm' x hx]⟩
  have hψ0 : ψ 0 = 0 := by
    change φ (diskMobius_R5 (-b) 1 0) = 0
    rw [diskMobius_neg_zero_R5, hb0]
  obtain ⟨c, hc, hψc⟩ :=
    eq_const_mul_of_bijOn_ball_of_map_zero_R5 hψd hψmaps hψinj hψsurj hψ0
  refine ⟨b, c, hb, hc, fun w hw => ?_⟩
  have h := hψc (m' w) (hm'B hw)
  change φ (m (m' w)) = c * m' w at h
  rw [hmm' w hw] at h
  rw [h]
  simp only [m', diskMobius_R5, one_mul, mul_div_assoc]

/-- consumer：恒等映射是盘自同构，G2a 给出 `id = diskMobius_R5 a c`（在开盘上）。 -/
example : ∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧ EqOn id (diskMobius_R5 a c) (ball 0 1) :=
  diskMobius_of_bijOn_ball_R5 differentiableOn_id (fun _ h => h) (injOn_id _)
    (fun w hw => ⟨w, hw, rfl⟩)

end DifferentialGeometry.Geometry
