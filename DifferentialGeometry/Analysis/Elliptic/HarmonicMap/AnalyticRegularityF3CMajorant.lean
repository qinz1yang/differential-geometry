import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Data.Nat.Choose.Sum

/-!
# F3-c (c2)：truncated-jet composition majorant lemma（O-MY-F3C G3，后缀 `_F3C`）

D-R-MY3-22 (c2)：对**有限阶** jets 工作，不先假设 `u` 的 analytic Banach norm 有限。
* `risingF_F3C s n = s(s+1)⋯(s+n−1)`（递归定义）与 rising-factorial Vandermonde
  `risingF_F3C_add`：`rf(a+b, n) = Σ C(n,i) rf(a,i) rf(b,n−i)`（factorial-weighted convolution）。
* **大引理** `norm_iteratedFDeriv_comp_le_risingF_F3C`：`‖D^m g (f x)‖ ≤ A m! S^m`（`m ≤ n`，`S = 1/R`）、
  `‖D^j f x‖ ≤ λ H^j rf(½, j−1)/2`（`1 ≤ j ≤ n`）、`λ S ≤ 1` ⇒ `‖D^n (g∘f) x‖ ≤ A H^n rf(½, n)`。
  证明：Mathlib `norm_iteratedFDerivWithin_comp_le_aux` 的归纳（`D^{n+1}(g∘f) = D^n(g'∘f · f')` + 双线性
  Leibniz），归纳量换成 super-solution `P ℓ n = A ℓ! S^ℓ H^n rf((ℓ+1)/2, n)`：递推右端恰为
  `(λS) · P ℓ (n+1)`（Vandermonde + `rf(s, n+1) = s·rf(s+1, n)`）。
* `exists_cauchy_bound_F3C`：`Γ` 在紧集 `K` 的每点 analytic ⇒ `∃ A S ≥ 0, ∀ y ∈ K, ∀ m,
  ‖D^m Γ y‖ ≤ A m! S^m`（`HasFPowerSeriesOnBall.changeOrigin` 的一致界 + 有限覆盖）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Finset
open scoped Topology ENNReal NNReal Nat ContDiff

namespace DifferentialGeometry.Analysis.Elliptic.HarmonicMap

/-! ## rising factorial 与 Vandermonde -/

/-- rising factorial `s (s+1) ⋯ (s+n−1)`。 -/
def risingF_F3C (s : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => risingF_F3C s n * (s + n)

@[simp] theorem risingF_F3C_zero (s : ℝ) : risingF_F3C s 0 = 1 := rfl

theorem risingF_F3C_succ (s : ℝ) (n : ℕ) :
    risingF_F3C s (n + 1) = risingF_F3C s n * (s + n) := rfl

theorem risingF_F3C_succ_left (s : ℝ) (n : ℕ) :
    risingF_F3C s (n + 1) = s * risingF_F3C (s + 1) n := by
  induction n with
  | zero => simp [risingF_F3C_succ]
  | succ n ih =>
      rw [risingF_F3C_succ, ih, risingF_F3C_succ]
      push_cast
      ring

theorem risingF_F3C_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ risingF_F3C s n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [risingF_F3C_succ]
      exact mul_nonneg ih (by positivity)

theorem risingF_F3C_mono {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') (n : ℕ) :
    risingF_F3C s n ≤ risingF_F3C s' n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [risingF_F3C_succ, risingF_F3C_succ]
      exact mul_le_mul ih (by linarith) (by positivity) (risingF_F3C_nonneg (hs.trans hss') n)

theorem risingF_F3C_one (n : ℕ) : risingF_F3C 1 n = n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [risingF_F3C_succ, ih, Nat.factorial_succ]
      push_cast
      ring

theorem risingF_F3C_half_le_factorial (n : ℕ) : risingF_F3C (1 / 2) n ≤ n ! := by
  rw [← risingF_F3C_one]
  exact risingF_F3C_mono (by norm_num) (by norm_num) n

/-- `rf(3/2, k) = (2k+1) rf(½, k)`。 -/
theorem risingF_F3C_three_halves (k : ℕ) :
    risingF_F3C (3 / 2) k = (2 * k + 1) * risingF_F3C (1 / 2) k := by
  have h1 := risingF_F3C_succ_left (1 / 2) k
  have h2 := risingF_F3C_succ (1 / 2) k
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at h1
  linarith

/-- rising-factorial Vandermonde（antidiagonal 形）。 -/
theorem risingF_F3C_add_antidiagonal (a b : ℝ) (n : ℕ) :
    risingF_F3C (a + b) n =
      ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℝ) * (risingF_F3C a ij.1 * risingF_F3C b ij.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_antidiagonal_choose_succ_mul (fun i j => risingF_F3C a i * risingF_F3C b j) n,
        ← sum_add_distrib, risingF_F3C_succ, ih, sum_mul]
      refine sum_congr rfl fun ij hij => ?_
      have hij' : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
      have hch : n.choose ij.2 = n.choose ij.1 := (Nat.choose_symm_of_eq_add hij'.symm).symm
      rw [hch, risingF_F3C_succ, risingF_F3C_succ]
      have hc : (n : ℝ) = ij.1 + ij.2 := by exact_mod_cast hij'.symm
      rw [hc]
      ring

/-- **rising-factorial Vandermonde**（range 形）。 -/
theorem risingF_F3C_add (a b : ℝ) (n : ℕ) :
    risingF_F3C (a + b) n =
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * risingF_F3C a i * risingF_F3C b (n - i) := by
  rw [risingF_F3C_add_antidiagonal, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (n.choose i : ℝ) * (risingF_F3C a i * risingF_F3C b j)) n]
  refine sum_congr rfl fun i _ => ?_
  ring

/-! ## composition majorant -/

/-- 递推右端的代数恒等式：`Σ C(n,i) P(ℓ+1, i) â(n−i+1) = (λ S) · P(ℓ, n+1)`。 -/
theorem sum_majorant_eq_F3C (A S H lam : ℝ) (ℓ n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
        (A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * H ^ i *
          risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i) *
        (lam * H ^ (n - i + 1) * risingF_F3C (1 / 2) (n - i) / 2) =
      (lam * S) * (A * (ℓ ! : ℝ) * S ^ ℓ * H ^ (n + 1) *
        risingF_F3C (((ℓ : ℝ) + 1) / 2) (n + 1)) := by
  have hterm : ∀ i ∈ range (n + 1), (n.choose i : ℝ) *
        (A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * H ^ i *
          risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i) *
        (lam * H ^ (n - i + 1) * risingF_F3C (1 / 2) (n - i) / 2) =
      (A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * H ^ (n + 1) * lam / 2) *
        ((n.choose i : ℝ) * risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i *
          risingF_F3C (1 / 2) (n - i)) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hp : H ^ i * H ^ (n - i + 1) = H ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc (n.choose i : ℝ) *
          (A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * H ^ i *
            risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i) *
          (lam * H ^ (n - i + 1) * risingF_F3C (1 / 2) (n - i) / 2)
        = (A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * (H ^ i * H ^ (n - i + 1)) * lam / 2) *
          ((n.choose i : ℝ) * risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i *
            risingF_F3C (1 / 2) (n - i)) := by ring
      _ = _ := by rw [hp]
  rw [sum_congr rfl hterm, ← mul_sum, ← risingF_F3C_add, risingF_F3C_succ_left,
    Nat.factorial_succ]
  have harg : (((ℓ + 1 : ℕ) : ℝ) + 1) / 2 + 1 / 2 = ((ℓ : ℝ) + 1) / 2 + 1 := by
    push_cast
    ring
  rw [harg]
  push_cast
  ring

/-- 归纳本体（`Fu`、`Gu` 同 universe，照 Mathlib `norm_iteratedFDerivWithin_comp_le_aux`）。 -/
theorem norm_iteratedFDerivWithin_comp_le_risingF_aux_F3C.{u} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Fu Gu : Type u} [NormedAddCommGroup Fu]
    [NormedSpace ℝ Fu] [NormedAddCommGroup Gu] [NormedSpace ℝ Gu] {g : Fu → Gu} {f : E → Fu}
    {n : ℕ} {s : Set E} {t : Set Fu} {x : E} (hg : ContDiffOn ℝ n g t) (hf : ContDiffOn ℝ n f s)
    (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s) (hst : MapsTo f s t) (hx : x ∈ s)
    {A S H lam : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hH : 0 ≤ H) (hlamS : lam * S ≤ 1)
    (ℓ : ℕ)
    (hC : ∀ m, m ≤ n → ‖iteratedFDerivWithin ℝ m g t (f x)‖ ≤ A * ((ℓ + m)! : ℝ) * S ^ (ℓ + m))
    (hD : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDerivWithin ℝ j f s x‖ ≤ lam * H ^ j * risingF_F3C (1 / 2) (j - 1) / 2) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x‖ ≤
      A * (ℓ ! : ℝ) * S ^ ℓ * H ^ n * risingF_F3C (((ℓ : ℝ) + 1) / 2) n := by
  induction n using Nat.case_strong_induction_on generalizing Gu ℓ with
  | hz =>
    have h := hC 0 le_rfl
    simp only [add_zero, norm_iteratedFDerivWithin_zero] at h
    simpa [norm_iteratedFDerivWithin_zero] using h
  | hi n IH =>
  have M : (n : ℕ∞ω) < n.succ := Nat.cast_lt.2 n.lt_succ_self
  have I : ∀ i ∈ Finset.range (n + 1),
      ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ g t ∘ f) s x‖ ≤
        A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * H ^ i *
          risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i := by
    intro i hi
    simp only [Finset.mem_range_succ_iff] at hi
    apply IH i hi
    · apply hg.fderivWithin ht
      grw [Nat.cast_succ, hi]
    · exact hf.of_le (Nat.cast_le.2 (hi.trans n.le_succ))
    · intro j hj
      have : ‖iteratedFDerivWithin ℝ j (fderivWithin ℝ g t) t (f x)‖ =
          ‖iteratedFDerivWithin ℝ (j + 1) g t (f x)‖ := by
        rw [iteratedFDerivWithin_succ_eq_comp_right ht (hst hx), Function.comp_apply,
          LinearIsometryEquiv.norm_map]
      rw [this]
      have h := hC (j + 1) (add_le_add (hj.trans hi) le_rfl)
      rwa [show ℓ + (j + 1) = ℓ + 1 + j by ring] at h
    · intro j hj h'j
      exact hD j hj (h'j.trans (hi.trans n.le_succ))
  have J : ∀ i, ‖iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ f s) s x‖ ≤
      lam * H ^ (n - i + 1) * risingF_F3C (1 / 2) (n - i) / 2 := by
    intro i
    have h := hD (n - i + 1) (by simp) (Nat.succ_le_succ tsub_le_self)
    simp only [Nat.add_sub_cancel] at h
    simpa [iteratedFDerivWithin_succ_eq_comp_right hs hx] using h
  have hP : 0 ≤ A * (ℓ ! : ℝ) * S ^ ℓ * H ^ (n + 1) *
      risingF_F3C (((ℓ : ℝ) + 1) / 2) (n + 1) := by
    have := risingF_F3C_nonneg (s := ((ℓ : ℝ) + 1) / 2) (by positivity) (n + 1)
    positivity
  calc
    ‖iteratedFDerivWithin ℝ (n + 1) (g ∘ f) s x‖ =
        ‖iteratedFDerivWithin ℝ n (fun y : E => fderivWithin ℝ (g ∘ f) s y) s x‖ := by
      rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, Function.comp_apply,
        LinearIsometryEquiv.norm_map]
    _ = ‖iteratedFDerivWithin ℝ n (fun y : E => ContinuousLinearMap.compL ℝ E Fu Gu
        (fderivWithin ℝ g t (f y)) (fderivWithin ℝ f s y)) s x‖ := by
      congr 1
      refine iteratedFDerivWithin_congr (fun y hy => ?_) hx _
      apply fderivWithin_comp _ _ _ hst (hs y hy)
      · exact hg.differentiableOn (by positivity) _ (hst hy)
      · exact hf.differentiableOn (by positivity) _ hy
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ g t ∘ f) s x‖ *
          ‖iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ f s) s x‖ := by
      exact (ContinuousLinearMap.compL ℝ E Fu Gu).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
        ((hg.fderivWithin ht (by simp)).comp (hf.of_le M.le) hst) (hf.fderivWithin hs (by simp))
        hs hx le_rfl (ContinuousLinearMap.norm_compL_le ℝ E Fu Gu)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (A * ((ℓ + 1 : ℕ)! : ℝ) * S ^ (ℓ + 1) * H ^ i *
          risingF_F3C ((((ℓ + 1 : ℕ) : ℝ) + 1) / 2) i) *
        (lam * H ^ (n - i + 1) * risingF_F3C (1 / 2) (n - i) / 2) := by
      gcongr with i hi
      · have := risingF_F3C_nonneg (s := (((ℓ + 1 : ℕ) : ℝ) + 1) / 2) (by positivity) i
        positivity
      · exact I i hi
      · exact J i
    _ = (lam * S) * (A * (ℓ ! : ℝ) * S ^ ℓ * H ^ (n + 1) *
        risingF_F3C (((ℓ : ℝ) + 1) / 2) (n + 1)) := sum_majorant_eq_F3C A S H lam ℓ n
    _ ≤ 1 * (A * (ℓ ! : ℝ) * S ^ ℓ * H ^ (n + 1) *
        risingF_F3C (((ℓ : ℝ) + 1) / 2) (n + 1)) := mul_le_mul_of_nonneg_right hlamS hP
    _ = _ := one_mul _

/-- **(c2) truncated-jet composition majorant lemma**（开集、`iteratedFDeriv` 版，`ℓ = 0`）：
`‖D^m g (f x)‖ ≤ A m! S^m`（`m ≤ n`）、`‖D^j f x‖ ≤ λ H^j rf(½, j−1)/2`（`1 ≤ j ≤ n`）、`λ S ≤ 1`
⇒ `‖D^n (g ∘ f) x‖ ≤ A H^n rf(½, n)`。只用 `n` 阶以内的 jets。 -/
theorem norm_iteratedFDeriv_comp_le_risingF_F3C.{u} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Fu Gu : Type u} [NormedAddCommGroup Fu]
    [NormedSpace ℝ Fu] [NormedAddCommGroup Gu] [NormedSpace ℝ Gu] {g : Fu → Gu} {f : E → Fu}
    {n : ℕ} {s : Set E} {t : Set Fu} {x : E} (hg : ContDiffOn ℝ n g t) (hf : ContDiffOn ℝ n f s)
    (ht : IsOpen t) (hs : IsOpen s) (hst : MapsTo f s t) (hx : x ∈ s)
    {A S H lam : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hH : 0 ≤ H) (hlamS : lam * S ≤ 1)
    (hC : ∀ m, m ≤ n → ‖iteratedFDeriv ℝ m g (f x)‖ ≤ A * (m ! : ℝ) * S ^ m)
    (hD : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ lam * H ^ j * risingF_F3C (1 / 2) (j - 1) / 2) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ A * H ^ n * risingF_F3C (1 / 2) n := by
  have h := norm_iteratedFDerivWithin_comp_le_risingF_aux_F3C hg hf ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx hA hS hH hlamS 0
    (fun m hm => by
      rw [iteratedFDerivWithin_of_isOpen m ht (hst hx), zero_add]
      exact hC m hm)
    (fun j hj hjn => by
      rw [iteratedFDerivWithin_of_isOpen j hs hx]
      exact hD j hj hjn)
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at h
  simpa using h

/-! ## analytic 函数在紧集上的一致 Cauchy 界 -/

section Cauchy

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- 幂级数中心处：`‖D^m Γ y‖ ≤ m! ‖p m‖`（`D^m Γ y = Σ_σ p m ∘ σ`）。 -/
theorem norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall_F3C {Γ : F → G}
    {p : FormalMultilinearSeries ℝ F G} {y : F} {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall Γ p y r)
    (m : ℕ) : ‖iteratedFDeriv ℝ m Γ y‖ ≤ (m ! : ℝ) * ‖p m‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace]
  calc ‖∑ σ : Equiv.Perm (Fin m), p m (fun i => v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin m), ‖p m‖ * ∏ i, ‖v i‖ := by
        refine norm_sum_le_of_le _ fun σ _ => ?_
        refine ((p m).le_opNorm _).trans_eq ?_
        rw [Equiv.prod_comp σ (fun i => ‖v i‖)]
    _ = (m ! : ℝ) * ‖p m‖ * ∏ i, ‖v i‖ := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- 局部一致 Cauchy 界：`AnalyticAt` ⇒ 某球内 `‖D^m Γ y‖ ≤ A m! S^m`。 -/
theorem exists_local_cauchy_bound_F3C {Γ : F → G} {y₀ : F} (h : AnalyticAt ℝ Γ y₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ A S : ℝ, 0 ≤ A ∧ 0 ≤ S ∧
      ∀ y ∈ ball y₀ ρ, ∀ m : ℕ, ‖iteratedFDeriv ℝ m Γ y‖ ≤ A * (m ! : ℝ) * S ^ m := by
  obtain ⟨p, r, hp⟩ := h
  obtain ⟨r₁, hr₁0, hr₁r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hr₁0' : (0 : ℝ≥0) < r₁ := by exact_mod_cast hr₁0
  set r₀ : ℝ≥0 := r₁ / 2 with hr₀def
  have hr₀ : 0 < r₀ := by rw [hr₀def]; positivity
  have hr₀r₁ : r₀ + r₀ = r₁ := by rw [hr₀def]; exact add_halves r₁
  have hrad : ((r₀ : ℝ≥0∞) + (r₀ : ℝ≥0∞)) < p.radius := by
    rw [← ENNReal.coe_add, hr₀r₁]
    exact hr₁r.trans_le hp.r_le
  have hsumm := p.changeOriginSeries_summable_aux₁ hrad
  set T : ℝ≥0 := ∑' s : Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l },
    ‖p (s.1 + s.2.1)‖₊ * r₀ ^ s.2.1 * r₀ ^ s.1 with hT
  refine ⟨r₀, by exact_mod_cast hr₀, T, (r₀ : ℝ)⁻¹, T.coe_nonneg, by positivity, ?_⟩
  intro y hy m
  set x : F := y - y₀ with hxdef
  have hx : ‖x‖₊ < r₀ := by
    have : dist y y₀ < r₀ := hy
    rw [dist_eq_norm] at this
    exact_mod_cast this
  have hr₀r : (r₀ : ℝ≥0∞) < r := by
    refine lt_of_le_of_lt ?_ hr₁r
    have : r₀ ≤ r₁ := by
      rw [← hr₀r₁]
      exact le_add_of_nonneg_left (by positivity)
    exact_mod_cast this
  have hxr : (‖x‖₊ : ℝ≥0∞) < r := (ENNReal.coe_lt_coe.mpr hx).trans hr₀r
  have hq := hp.changeOrigin hxr
  rw [show y₀ + x = y by rw [hxdef]; abel] at hq
  have h1 := norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall_F3C hq m
  have hxrad : (‖x‖₊ : ℝ≥0∞) < p.radius := hxr.trans_le hp.r_le
  have hco := p.nnnorm_changeOrigin_le m hxrad
  have hsm : Summable fun s : Σ l : ℕ, { s : Finset (Fin (m + l)) // s.card = l } =>
      ‖p (m + s.1)‖₊ * r₀ ^ s.1 * r₀ ^ m :=
    (NNReal.summable_sigma.1 hsumm).1 m
  have hle : ∀ s : Σ l : ℕ, { s : Finset (Fin (m + l)) // s.card = l },
      ‖p (m + s.1)‖₊ * ‖x‖₊ ^ s.1 * r₀ ^ m ≤ ‖p (m + s.1)‖₊ * r₀ ^ s.1 * r₀ ^ m := by
    intro s
    gcongr
  have h2 : ‖p.changeOrigin x m‖₊ * r₀ ^ m ≤ T := by
    calc ‖p.changeOrigin x m‖₊ * r₀ ^ m
        ≤ (∑' s : Σ l : ℕ, { s : Finset (Fin (m + l)) // s.card = l },
            ‖p (m + s.1)‖₊ * ‖x‖₊ ^ s.1) * r₀ ^ m := by gcongr
      _ = ∑' s : Σ l : ℕ, { s : Finset (Fin (m + l)) // s.card = l },
            ‖p (m + s.1)‖₊ * ‖x‖₊ ^ s.1 * r₀ ^ m := (NNReal.tsum_mul_right _ _).symm
      _ ≤ ∑' s : Σ l : ℕ, { s : Finset (Fin (m + l)) // s.card = l },
            ‖p (m + s.1)‖₊ * r₀ ^ s.1 * r₀ ^ m :=
          Summable.tsum_le_tsum hle (NNReal.summable_of_le hle hsm) hsm
      _ ≤ T := by
          have hinj := NNReal.tsum_comp_le_tsum_of_inj hsumm
            (sigma_mk_injective (i := m) (β := fun k => Σ l : ℕ,
              { s : Finset (Fin (k + l)) // s.card = l }))
          exact hinj
  have h2' : ‖p.changeOrigin x m‖ * (r₀ : ℝ) ^ m ≤ T := by exact_mod_cast h2
  have hr₀' : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
  have h3 : ‖p.changeOrigin x m‖ ≤ (T : ℝ) * ((r₀ : ℝ)⁻¹) ^ m := by
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hr₀' m)]
    exact h2'
  calc ‖iteratedFDeriv ℝ m Γ y‖ ≤ (m ! : ℝ) * ‖p.changeOrigin x m‖ := h1
    _ ≤ (m ! : ℝ) * ((T : ℝ) * ((r₀ : ℝ)⁻¹) ^ m) := by gcongr
    _ = (T : ℝ) * (m ! : ℝ) * ((r₀ : ℝ)⁻¹) ^ m := by ring

/-- **紧集上的一致 Cauchy 界**：`Γ` 在紧集 `K` 每点 analytic ⇒
`∃ A S ≥ 0, ∀ y ∈ K, ∀ m, ‖D^m Γ y‖ ≤ A m! S^m`（D-R-MY3-22 (c2) 的 `‖DᵐΓ‖/m! ≤ A R⁻ᵐ`）。 -/
theorem exists_cauchy_bound_F3C {Γ : F → G} {K : Set F} (hK : IsCompact K)
    (hΓ : ∀ y ∈ K, AnalyticAt ℝ Γ y) :
    ∃ A S : ℝ, 0 ≤ A ∧ 0 ≤ S ∧
      ∀ y ∈ K, ∀ m : ℕ, ‖iteratedFDeriv ℝ m Γ y‖ ≤ A * (m ! : ℝ) * S ^ m := by
  have hloc : ∀ y₀ ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ ∃ A : ℝ, ∃ S : ℝ, 0 ≤ A ∧ 0 ≤ S ∧
      ∀ y ∈ ball y₀ ρ, ∀ m : ℕ, ‖iteratedFDeriv ℝ m Γ y‖ ≤ A * (m ! : ℝ) * S ^ m :=
    fun y₀ hy₀ => exists_local_cauchy_bound_F3C (hΓ y₀ hy₀)
  choose! ρ hρ A S hA hS hb using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun y₀ => ball y₀ (ρ y₀))
    (fun y₀ hy₀ => ball_mem_nhds y₀ (hρ y₀ hy₀))
  refine ⟨∑ y₀ ∈ t, A y₀, ∑ y₀ ∈ t, S y₀, sum_nonneg fun i hi => hA i (htK i hi),
    sum_nonneg fun i hi => hS i (htK i hi), ?_⟩
  intro y hy m
  obtain ⟨y₀, hy₀t, hyb⟩ := mem_iUnion₂.mp (hcover hy)
  refine (hb y₀ (htK y₀ hy₀t) y hyb m).trans ?_
  have hA' : A y₀ ≤ ∑ y₀ ∈ t, A y₀ :=
    single_le_sum (fun i hi => hA i (htK i hi)) hy₀t
  have hS' : S y₀ ≤ ∑ y₀ ∈ t, S y₀ :=
    single_le_sum (fun i hi => hS i (htK i hi)) hy₀t
  have hSy := hS y₀ (htK y₀ hy₀t)
  have hAy := hA y₀ (htK y₀ hy₀t)
  have hsA : 0 ≤ ∑ y₀ ∈ t, A y₀ := hAy.trans hA'
  gcongr

end Cauchy

end DifferentialGeometry.Analysis.Elliptic.HarmonicMap

/-! ## consumer（G3）-/

open DifferentialGeometry.Analysis.Elliptic.HarmonicMap in
/-- 紧集上的一致 Cauchy 界接 composition majorant：`Γ` 在 `univ` 上 analytic、`v` 的 jets 有
rising-factorial 界 ⇒ `Γ ∘ v` 的 `n` 阶导数有同型界（只用到 `n` 阶以内的 jets）。 -/
example {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {Γ : F → G} (hΓ : ContDiff ℝ ω Γ) {v : ℝ → F}
    (hv : ContDiff ℝ ∞ v) {x : ℝ} (n : ℕ) {H lam : ℝ} (hH : 0 ≤ H) :
    ∃ A S : ℝ, 0 ≤ A ∧ 0 ≤ S ∧ (lam * S ≤ 1 →
      (∀ j, 1 ≤ j → j ≤ n →
        ‖iteratedFDeriv ℝ j v x‖ ≤ lam * H ^ j * risingF_F3C (1 / 2) (j - 1) / 2) →
      ‖iteratedFDeriv ℝ n (Γ ∘ v) x‖ ≤ A * H ^ n * risingF_F3C (1 / 2) n) := by
  obtain ⟨A, S, hA, hS, hb⟩ := exists_cauchy_bound_F3C (isCompact_singleton (x := v x))
    (fun y _ => hΓ.contDiffAt.analyticAt)
  refine ⟨A, S, hA, hS, fun hlamS hD => ?_⟩
  exact norm_iteratedFDeriv_comp_le_risingF_F3C (hΓ.of_le le_top).contDiffOn
    (hv.of_le (by exact_mod_cast le_top)).contDiffOn isOpen_univ isOpen_univ (mapsTo_univ _ _)
    (mem_univ x) hA hS hH hlamS (fun m _ => hb (v x) rfl m) hD
