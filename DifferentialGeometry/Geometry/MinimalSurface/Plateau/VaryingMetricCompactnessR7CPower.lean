import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CBoundaryEventual
import DifferentialGeometry.Analysis.Asymptotics.TruncatedBallPower
import DifferentialGeometry.Analysis.Asymptotics.LimsupDecay
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# R7C L6（一）：截断球 power bound（内部 + 边界，对整列一致）

把 G2（内部 hole-filling）与 G3（边界 dyadic decay）合成
`∫_{D° ∩ B̄_s(x)} e_G(uₙ) ≤ K s^p`（一切 `x ∈ D̄`、`s ≤ δ`、`n ≥ N₀`），常数与 `n` 无关。
组合用树内 `exists_uniform_truncated_ball_power_bound_of_boundary_bound_of_half_contraction`，
施于**对 `n` 取上确界**的集函数 `ν*(S) = sup_{n ≥ N₀} E_G(uₙ, S ∩ D)`——这样树内引理的存在常数自动对
所有 `n` 一致（"sup trick"）。内部 half contraction 需要小能量：深处由内部 dyadic decay
（`interior_decay_of_hole_filling_generic_R7C`），近边界由边界 power bound 给出。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold TopologicalSpace
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

/-- 内部 dyadic decay 的抽象形（R7C）：对任意非负、在 `D` 上可积、总量 `≤ Λ`、满足 hole-filling
（环能量 `< ε` ⇒ `E(B̄_r(b)) ≤ K · E(环)`）的密度 `f`：`E(B̄(b, R/2^{N+k})) ≤ θ^k (ε/2)`，
`N` 只依赖 `(ε, K, Λ)`。 -/
theorem interior_decay_of_hole_filling_generic_R7C {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hΛ : 0 ≤ Λ) :
    ∃ N : ℕ, ∀ f : ℂ → ℝ, (∀ z, 0 ≤ f z) → IntegrableOn f (closedBall (0 : ℂ) 1) →
      (∫ z in closedBall (0 : ℂ) 1, f z) ≤ Λ →
      (∀ (b : ℂ) (r : ℝ), 0 < r → ‖b‖ + 2 * r < 1 →
        (∫ z in {z : ℂ | dist z b ∈ Icc r (2 * r)}, f z) < ε →
        (∫ z in closedBall b r, f z) ≤ K * ∫ z in {z : ℂ | dist z b ∈ Icc r (2 * r)}, f z) →
      ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
        (∫ z in closedBall b (R / 2 ^ (N + k)), f z) ≤ (K / (1 + K)) ^ k * (ε / 2) := by
  obtain ⟨N, hN⟩ := dyadic_decay_of_hole_filling_R7C (half_pos hε) hK hΛ
  refine ⟨N, fun f hf0 hint hΛf hhole b R hR hbR k => ?_⟩
  set e : ℕ → ℝ := fun j => ∫ z in closedBall b (R / 2 ^ j), f z with hedef
  have hrad : ∀ j : ℕ, 0 < R / 2 ^ j := fun j => by positivity
  have hradanti : Antitone fun j : ℕ => R / 2 ^ j := fun i j hij =>
    div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
  have hball : ∀ j : ℕ, closedBall b (R / 2 ^ j) ⊆ closedBall (0 : ℂ) 1 := by
    intro j z hz
    have h1 := mem_closedBall.mp hz
    have h2 : R / 2 ^ j ≤ R := by simpa using hradanti (Nat.zero_le j)
    have h3 : ‖z‖ ≤ dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    exact mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  have he0 : ∀ j, 0 ≤ e j := fun j => integral_nonneg hf0
  have heanti : Antitone e := fun i j hij =>
    setIntegral_mono_set (hint.mono_set (hball i)) (Eventually.of_forall hf0)
      (Eventually.of_forall (closedBall_subset_closedBall (hradanti hij)))
  have heΛ : e 0 ≤ Λ := (setIntegral_mono_set hint (Eventually.of_forall hf0)
    (Eventually.of_forall (hball 0))).trans hΛf
  have hdrop : ∀ j, e j - e (j + 1) < ε / 2 → e (j + 1) ≤ K * (e j - e (j + 1)) := by
    intro j hj
    have hstep : R / 2 ^ j = 2 * (R / 2 ^ (j + 1)) := by
      rw [pow_succ]
      field_simp
    have hann := integral_annulus_eq_sub_closedBall_R7C (b := b)
      (r := R / 2 ^ (j + 1)) (R := 2 * (R / 2 ^ (j + 1))) (by linarith [hrad (j + 1)])
      (by rw [← hstep]; exact hint.mono_set (hball j))
    rw [← hstep] at hann
    have hbr : ‖b‖ + 2 * (R / 2 ^ (j + 1)) < 1 := by
      rw [← hstep]
      linarith [hradanti (Nat.zero_le j), show R / 2 ^ 0 = R by simp]
    have h := hhole b (R / 2 ^ (j + 1)) (hrad _) hbr
      (by rw [← hstep, hann]; linarith)
    rw [← hstep, hann] at h
    exact h
  exact hN e heanti he0 heΛ hdrop k

private theorem dist_normalize_of_norm_le_one_R7C {x : ℂ} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    dist x (NormedSpace.normalize x) = 1 - ‖x‖ := by
  have he : x - NormedSpace.normalize x = (‖x‖ - 1) • NormedSpace.normalize x := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hx,
    mul_one, abs_of_nonpos (by linarith)]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **L6 截断球 power bound**（R7C）：R7 设定下，存在 `p, δ, K, N₀`（与 `n` 无关）使
`∫_{D° ∩ B̄_s(x)} e_G(uₙ) ≤ K s^p` 对一切 `n ≥ N₀`、`x ∈ D̄`、`0 < s ≤ δ` 成立。 -/
theorem eventually_truncated_ball_power_bound_R7C [T3Space M] [SecondCountableTopology M]
    (hdim : Module.finrank ℝ E = 3) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {B C : Set M} (hC : IsCompact C)
    (hCB : C ⊆ interior B)
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (θ : Fin 3 → loopCircle)
    (hθ : Function.Injective θ)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huC : ∀ n, range (u n) ⊆ C) (huθ : ∀ n j, diskTrace (u n) (θ j) = Γ (θ j))
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hA : ∀ n, riemannianDiskArea (Gn n) (u n) ≤ Λ) :
    ∃ (p δ Kp : ℝ) (N₀ : ℕ), 0 < p ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ Kp ∧
      ∀ n, N₀ ≤ n → ∀ x ∈ closedBall (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        (∫ z in ball (0 : ℂ) 1 ∩ closedBall x s,
          diskMapEnergyDensity G (diskExtension (u n)) z) ≤ Kp * s ^ p := by
  set D : Set ℂ := closedBall (0 : ℂ) 1 with hDdef
  set f : ℕ → ℂ → ℝ := fun n => diskMapEnergyDensity G (diskExtension (u n)) with hfdef
  have hf0 : ∀ n z, 0 ≤ f n z := fun n z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg G _ _) (metric_inner_self_nonneg G _ _))
      (by norm_num)
  -- 边界 decay（G3）
  obtain ⟨Kb, θb, εb, sb, hθb0, hθb1, hεb, hsb, hsb8, hbev⟩ :=
    eventually_boundary_dyadic_decay_R7C hdim hC hCB hrel hΓ θ hθ hu huC huθ hΛ0 hA
  -- completion buffer + 内部 hole-filling（G2）
  obtain ⟨W, Ghat, O, _, hCO, hOW, hWB, _, hHR, hGle, hgerm⟩ :=
    exists_completion_buffer_R7C hdim G hC hCB
  have hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x := by
    intro x hx
    have h := (hgerm x hx).self_of_nhds
    rw [h]
    ext v w
    exact SmoothRiemannianMetric.restrictOpen_inner G W x v w
  have hWB' : (W : Set M) ⊆ B := subset_closure.trans (hWB.trans interior_subset)
  obtain ⟨εh, Kh, hεh, hKh, hhole⟩ := interior_hole_filling_R7C W Ghat hHR hOW hagree
  obtain ⟨Ni, hNi⟩ := interior_decay_of_hole_filling_generic_R7C hεh hKh
    (by linarith : (0 : ℝ) ≤ 2 * Λ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hbev.and (hrel (1 / 2) (by norm_num)))
  -- 每个 `n`：可积性
  have hint : ∀ n, IntegrableOn (f n) D := by
    intro n
    have huO : range (u n) ⊆ O := (huC n).trans hCO
    have huW : range (u n) ⊆ (W : Set M) := huO.trans hOW
    obtain ⟨σ, _, htr⟩ := (hu n).trace
    obtain ⟨Q, hQ⟩ := exists_smooth_extension_of_conformal_harmonic_disk (Gn n) hΓ (u n)
      (hu n).smoothInterior (hu n).conformal (hu n).harmonic σ htr
    obtain ⟨V, hV, _⟩ := smoothDiskExtension_liftToOpen_ADP hQ huW
    obtain ⟨L, hL⟩ := hV.lipschitz Ghat
    exact (integrable_diskMapEnergyDensity Ghat hL).congr_fun
      (fun z _ => diskMapEnergyDensity_lift_eq_R7C W Ghat hagree huO _ (fun _ => rfl) z)
      measurableSet_closedBall
  -- `n ≥ N₀`：比较、能量界、hole-filling、内部 decay
  have hcmp : ∀ n, N₀ ≤ n →
      (∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x), (Gn n).inner x v v ≤ 2 * Ghat.inner x v v) ∧
      (∀ x ∈ O, ∀ v : TangentSpace 𝓘(ℝ, E) x, G.inner x v v ≤ 2 * (Gn n).inner x v v) := by
    intro n hn
    have hrn := (hN₀ n hn).2
    refine ⟨fun x v => ?_, fun x hx v => ?_⟩
    · have h1 := (abs_le.mp (hrn x (hWB' x.property) v)).2
      have h2 := hGle x v
      rw [SmoothRiemannianMetric.restrictOpen_inner] at h2
      have h3 := metric_inner_self_nonneg G (x : M) v
      linarith
    · have h1 := (abs_le.mp (hrn x (hWB' (hOW hx)) v)).1
      linarith
  have htot : ∀ n, N₀ ≤ n → (∫ z in D, f n z) ≤ 2 * Λ := by
    intro n hn
    have hrn := (hN₀ n hn).2
    have hpt : ∀ z, f n z ≤ 2 * diskMapEnergyDensity (Gn n) (diskExtension (u n)) z := by
      intro z
      have hx := hrn (diskExtension (u n) z)
        (hWB' (hOW (hCO (huC n ⟨diskRetraction z, rfl⟩))))
      have h1 := (abs_le.mp (hx (diskMapPartial (diskExtension (u n)) z 1))).1
      have h2 := (abs_le.mp (hx (diskMapPartial (diskExtension (u n)) z Complex.I))).1
      change diskMapEnergyDensity G (diskExtension (u n)) z ≤ _
      unfold diskMapEnergyDensity
      linarith
    have hEn : (∫ z in D, diskMapEnergyDensity (Gn n) (diskExtension (u n)) z) =
        riemannianDiskArea (Gn n) (u n) := by
      unfold riemannianDiskArea riemannianArea
      apply integral_congr_ae
      filter_upwards [ae_disk_interior] with z hz
      exact diskMapEnergyDensity_eq_areaDensity_of_conformal_R7A (Gn n) ((hu n).conformal z hz)
    calc (∫ z in D, f n z)
        ≤ ∫ z in D, 2 * diskMapEnergyDensity (Gn n) (diskExtension (u n)) z :=
          integral_mono_of_nonneg (Eventually.of_forall (hf0 n))
            ((hu n).finiteEnergy.const_mul 2) (Eventually.of_forall hpt)
      _ = 2 * riemannianDiskArea (Gn n) (u n) := by rw [integral_const_mul, hEn]
      _ ≤ 2 * Λ := by linarith [hA n]
  have hholen : ∀ n, N₀ ≤ n → ∀ (b : ℂ) (r : ℝ), 0 < r → ‖b‖ + 2 * r < 1 →
      (∫ z in {z : ℂ | dist z b ∈ Icc r (2 * r)}, f n z) < εh →
      (∫ z in closedBall b r, f n z) ≤ Kh * ∫ z in {z : ℂ | dist z b ∈ Icc r (2 * r)}, f n z :=
    fun n hn => hhole (Gn n) (hcmp n hn).1 (hcmp n hn).2 Γ (u n) hΓ (hu n)
      ((huC n).trans hCO)
  have hdecn : ∀ n, N₀ ≤ n → ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
      (∫ z in closedBall b (R / 2 ^ (Ni + k)), f n z) ≤ (Kh / (1 + Kh)) ^ k * (εh / 2) :=
    fun n hn => hNi (f n) (hf0 n) (hint n) (htot n hn) (hholen n hn)
  -- 边界 power（对 `(n, c)` 一致）
  set δb : ℝ := sb / 2 ^ Kb with hδbdef
  have hδb : 0 < δb := by positivity
  obtain ⟨α, Cb, hα, _, hCb, hbpow⟩ := exists_radius_power_bound_of_dyadic_decay
    (ι := {n : ℕ // N₀ ≤ n} × sphere (0 : ℂ) 1)
    (fun nc r => ∫ z in closedBall (nc.2 : ℂ) r ∩ D, f nc.1 z) hδb hθb0 hθb1 hεb.le
    (fun nc a _ b _ hab => setIntegral_mono_set ((hint nc.1).mono_set inter_subset_right)
      (Eventually.of_forall (hf0 nc.1))
      (Eventually.of_forall (inter_subset_inter_left _ (closedBall_subset_closedBall hab))))
    (fun nc k => by
      have h := (hN₀ nc.1.1 nc.1.2).1 nc.2 nc.2.2 k
      have hr : δb / (2 : ℝ) ^ k = sb / 2 ^ (Kb + k) := by
        rw [hδbdef, pow_add, div_div]
      rw [hr]
      exact h)
  -- 选 `δi`
  set q : ℝ := 2 * α with hqdef
  have hq : 0 < q := by positivity
  set t₁ : ℝ := (εh / (2 * (Cb + 1))) ^ q⁻¹ with ht₁def
  have ht₁ : 0 < t₁ := Real.rpow_pos_of_pos (by positivity) _
  have ht₁q : Cb * t₁ ^ q < εh := by
    rw [ht₁def, Real.rpow_inv_rpow (by positivity) hq.ne']
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  set A2 : ℝ := 2 ^ Ni + 1 with hA2
  have hA2pos : 1 ≤ A2 := by rw [hA2]; have := pow_pos (by norm_num : (0 : ℝ) < 2) Ni; linarith
  set δi : ℝ := min δb t₁ / A2 with hδidef
  have hδi : 0 < δi := div_pos (lt_min hδb ht₁) (by linarith)
  have hδiA : ∀ s, s ≤ δi → A2 * s ≤ min δb t₁ := by
    intro s hs
    rw [hδidef, le_div_iff₀ (by linarith)] at hs
    linarith
  -- 小能量
  have hsmall : ∀ n, N₀ ≤ n → ∀ (x : ℂ) (s : ℝ), 0 < s → s ≤ δi → ‖x‖ + s < 1 →
      (∫ z in closedBall x s, f n z) < εh := by
    intro n hn x s hs hsδ hxs
    by_cases hdeep : ‖x‖ + 2 ^ Ni * s < 1
    · have h := hdecn n hn x (2 ^ Ni * s) (by positivity) hdeep 0
      rw [add_zero, mul_div_cancel_left₀ _ (by positivity), pow_zero, one_mul] at h
      linarith
    · push Not at hdeep
      have hAs := hδiA s hsδ
      have hAsb : A2 * s ≤ δb := hAs.trans (min_le_left _ _)
      have hAst : A2 * s ≤ t₁ := hAs.trans (min_le_right _ _)
      have h2s : 2 ^ Ni * s < 1 := by
        have : δb ≤ 1 / 8 := by
          rw [hδbdef]
          exact (div_le_self hsb.le (one_le_pow₀ (by norm_num))).trans hsb8
        rw [hA2] at hAsb
        nlinarith
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hdeep
        linarith
      have hx1 : ‖x‖ ≤ 1 := by linarith
      set c := NormedSpace.normalize x with hc
      have hcs : c ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere, dist_zero_right]
        exact NormedSpace.norm_normalize hx0
      have hxc : dist x c = 1 - ‖x‖ := dist_normalize_of_norm_le_one_R7C hx0 hx1
      have hsub : closedBall x s ⊆ closedBall c (A2 * s) ∩ D := by
        intro z hz
        refine ⟨?_, ?_⟩
        · have h1 := dist_triangle z x c
          have h2 : dist z x ≤ s := hz
          rw [mem_closedBall, hA2]
          nlinarith
        · have h3 : ‖z‖ ≤ dist z x + ‖x‖ := by
            simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
          have h2 : dist z x ≤ s := hz
          rw [hDdef, mem_closedBall, dist_zero_right]
          linarith
      have hle := setIntegral_mono_set ((hint n).mono_set inter_subset_right)
        (Eventually.of_forall (hf0 n)) (Eventually.of_forall hsub)
      have hbp := hbpow (⟨n, hn⟩, ⟨c, hcs⟩) (A2 * s) ⟨by positivity, hAsb⟩
      have hmono : Cb * (A2 * s) ^ q ≤ Cb * t₁ ^ q :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hAst hq.le) hCb
      simp only at hbp
      linarith
  -- half contraction
  have hhalf : ∀ n, N₀ ≤ n → ∀ (x : ℂ) (s : ℝ), 0 < s → s ≤ δi → ‖x‖ + s < 1 →
      (∫ z in closedBall x (s / 2), f n z) ≤ Kh / (1 + Kh) * ∫ z in closedBall x s, f n z := by
    intro n hn x s hs hsδ hxs
    have hxD : closedBall x s ⊆ D := by
      intro z hz
      have h3 : ‖z‖ ≤ dist z x + ‖x‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
      have h2 : dist z x ≤ s := hz
      rw [hDdef, mem_closedBall, dist_zero_right]
      linarith
    have hann := integral_annulus_eq_sub_closedBall_R7C (b := x) (r := s / 2) (R := 2 * (s / 2))
      (by linarith) (by rw [show 2 * (s / 2) = s by ring]; exact (hint n).mono_set hxD)
    rw [show 2 * (s / 2) = s by ring] at hann
    have hsm := hsmall n hn x s hs hsδ hxs
    have hnn : 0 ≤ ∫ z in closedBall x (s / 2), f n z :=
      setIntegral_nonneg measurableSet_closedBall (fun z _ => hf0 n z)
    have hhs := hholen n hn x (s / 2) (by positivity) (by linarith)
      (by rw [show 2 * (s / 2) = s by ring, hann]; linarith)
    rw [show 2 * (s / 2) = s by ring, hann] at hhs
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  -- sup trick
  set ν : Set ℂ → ℝ := fun S => ⨆ k : ℕ, ∫ z in S ∩ D, f (N₀ + k) z with hνdef
  have hbdd : ∀ S : Set ℂ, BddAbove (range fun k : ℕ => ∫ z in S ∩ D, f (N₀ + k) z) := by
    intro S
    refine ⟨2 * Λ, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (setIntegral_mono_set (hint _) (Eventually.of_forall (hf0 _))
      (Eventually.of_forall inter_subset_right)).trans (htot _ (Nat.le_add_right _ _))
  have hball1 : ball (0 : ℂ) 1 ⊆ D := ball_subset_closedBall
  obtain ⟨p, δ, Kp, hp, _, _, hδ, hδ8, hKp, hpow⟩ :=
    exists_uniform_truncated_ball_power_bound_of_boundary_bound_of_half_contraction (V := ℂ) ν
      (fun {S T} hST _ => ciSup_mono (hbdd T) fun k => setIntegral_mono_set
        ((hint _).mono_set inter_subset_right) (Eventually.of_forall (hf0 _))
        (Eventually.of_forall (inter_subset_inter_left _ hST)))
      (le_ciSup_of_le (hbdd _) 0 (integral_nonneg (hf0 _)))
      (β := q) (Kb := Cb) (δb := δb) (δi := δi) (θ := Kh / (1 + Kh)) hq hCb hδb hδi
      (by positivity) (by rw [div_lt_one (by linarith)]; linarith)
      (fun c hc s hs hsb' => ciSup_le fun k => by
        have h := hbpow (⟨N₀ + k, Nat.le_add_right _ _⟩, ⟨c, hc⟩) s ⟨hs, hsb'⟩
        simp only at h
        refine (setIntegral_mono_set ((hint _).mono_set inter_subset_right)
          (Eventually.of_forall (hf0 _)) (Eventually.of_forall ?_)).trans h
        exact inter_subset_inter_left _ inter_subset_right)
      (fun x s hs hsδ hxs => ciSup_le fun k => by
        have hxD : ∀ t, t ≤ s → closedBall x t ∩ D = closedBall x t := by
          intro t ht
          apply inter_eq_left.mpr
          intro z hz
          have h3 : ‖z‖ ≤ dist z x + ‖x‖ := by
            simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
          have h2 : dist z x ≤ t := hz
          rw [hDdef, mem_closedBall, dist_zero_right]
          linarith
        rw [hxD (s / 2) (by linarith)]
        refine (hhalf (N₀ + k) (Nat.le_add_right _ _) x s hs hsδ hxs).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (∫ z in closedBall x s, f (N₀ + k) z)
            = ∫ z in closedBall x s ∩ D, f (N₀ + k) z := by rw [hxD s le_rfl]
          _ ≤ ν (closedBall x s) := le_ciSup (hbdd _) k)
  refine ⟨p, δ, Kp, N₀, hp, hδ, hδ8, hKp, ?_⟩
  intro n hn x hx s hs hsδ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := hpow x hx s hs hsδ
  refine le_trans ?_ h
  have heq : ball (0 : ℂ) 1 ∩ closedBall x s ∩ D = ball (0 : ℂ) 1 ∩ closedBall x s :=
    inter_eq_left.mpr (inter_subset_left.trans hball1)
  calc (∫ z in ball (0 : ℂ) 1 ∩ closedBall x s, f (N₀ + k) z)
      = ∫ z in ball (0 : ℂ) 1 ∩ closedBall x s ∩ D, f (N₀ + k) z := by rw [heq]
    _ ≤ ν (ball (0 : ℂ) 1 ∩ closedBall x s) := le_ciSup (hbdd _) k

end DifferentialGeometry.Geometry
