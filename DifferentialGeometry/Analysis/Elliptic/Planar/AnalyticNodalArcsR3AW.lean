import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalPrincipalR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalPolarR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalArcPointR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalRootR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarBlowup

/-!
# R3a-ω（`_R3AW`）F4c：notion `IsNodalHalfArcsAt_R3AW` 与 G3（half-arcs）

* `IsNodalHalfArcsAt_R3AW`：`MYD3/R03R05.lean:36` 的修正版——`V = p + T (ball 0 ρ)`（开集），
  `2k` 条 embedded `C¹` half-arcs `Γ_m : [0, ρ] → ℂ`，`MapsTo` 与零集覆盖改用 `Ico 0 ρ`
  （原陈述的 `Icc 0 ρ` 使外端点仍在开集 `V` 内却是 regular zero，零曲线必须继续延伸，不可满足；
  修正 (i) 让外端点落在 `∂V` 上）。其余条款不变：方向 `T e^{i(θ₀ + mπ/k)}`（正规化坐标等角），
  两两只在 `p` 相交，`V` 内中心外零点 `dw ≠ 0`。
* `nodal_half_arcs_R3AW`（G3）：角函数形 `A₀ sin (k t)` + 正规化 `T` ⇒ 弧（极坐标 blow-up + IFT）。
* `exists_regular_zero_near_of_nodal_R3AW`（G3 consumer）：切点任意近处存在 regular 零点。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- R3a-ω 的结论（修正版，D-R-MY2-3 + R-MY3）：`V = p + T (ball 0 ρ)`，`2k` 条 embedded `C¹` half-arcs
`Γ_m` 在 `Icc 0 ρ` 上正则，`MapsTo` 与零集覆盖改用 `Ico 0 ρ`（外端点落在 `∂V` 上）。 -/
def IsNodalHalfArcsAt_R3AW (O : Set ℂ) (a : Fin 2 → Fin 2 → ℂ → ℝ) (w : ℂ → ℝ) (p : ℂ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (∀ j < k, iteratedFDeriv ℝ j w p = 0) ∧ iteratedFDeriv ℝ k w p ≠ 0 ∧
    ∃ (V : Set ℂ) (T : ℂ ≃L[ℝ] ℂ) (lam θ₀ ρ : ℝ) (Γ : Fin (2 * k) → ℝ → ℂ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧ 0 < lam ∧ 0 < ρ ∧
      (∀ k' l : Fin 2, ∑ i, ∑ j, a i j p *
        ![Complex.re, Complex.im] k' (T.symm (![1, Complex.I] i)) *
        ![Complex.re, Complex.im] l (T.symm (![1, Complex.I] j)) = if k' = l then lam else 0) ∧
      (∀ m, Γ m 0 = p ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧
        (∀ r ∈ Icc 0 ρ, derivWithin (Γ m) (Icc 0 ρ) r ≠ 0) ∧
        HasDerivWithinAt (Γ m)
          (T (Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)))
          (Icc 0 ρ) 0 ∧
        MapsTo (Γ m) (Ico 0 ρ) V) ∧
      (∀ m m', m ≠ m' → ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
      (∀ z ∈ V, w z = 0 ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z = Γ m r) ∧
      ∀ z ∈ V, w z = 0 → z ≠ p → fderiv ℝ w z ≠ 0

/-- G3：已知 `k` 阶 jet 的角函数形 `A₀ sin (k t)`（G2 的结论）与正规化 `T`，
由极坐标 blow-up + IFT 得到 `2k` 条 embedded `C¹` half-arcs。 -/
theorem nodal_half_arcs_R3AW {O : Set ℂ} (hO : IsOpen O) {w : ℂ → ℝ}
    (hwa : AnalyticOnNhd ℝ w O) {a : Fin 2 → Fin 2 → ℂ → ℝ} {p : ℂ} (hp : p ∈ O) {k : ℕ}
    (hk : 1 ≤ k) (hjet : ∀ j < k, iteratedFDeriv ℝ j w p = 0)
    (hjk : iteratedFDeriv ℝ k w p ≠ 0) (T : ℂ ≃L[ℝ] ℂ)
    (hnorm : ∀ k' l : Fin 2, ∑ i, ∑ j, a i j p *
        ![Complex.re, Complex.im] k' (T.symm (![1, Complex.I] i)) *
        ![Complex.re, Complex.im] l (T.symm (![1, Complex.I] j)) = if k' = l then 1 else 0)
    {θ₀ A₀ : ℝ} (hA₀ : 0 < A₀)
    (hsin : ∀ t : ℝ, iteratedFDeriv ℝ k w p
      (fun _ => T (Complex.exp (((θ₀ + t : ℝ) : ℂ) * Complex.I))) = A₀ * Real.sin (k * t)) :
    IsNodalHalfArcsAt_R3AW O a w p := by
  classical
  let u : ℂ → ℝ := fun y => w (p + T y)
  let Ω : Set ℂ := {y | p + T y ∈ O}
  have hΩ : IsOpen Ω := hO.preimage (continuous_const.add T.continuous)
  have h0Ω : (0 : ℂ) ∈ Ω := by
    change p + T 0 ∈ O
    simpa using hp
  have hwc : ContDiffOn ℝ ∞ w O := hwa.contDiffOn hO.uniqueDiffOn
  have hu : ContDiffOn ℝ ∞ u Ω :=
    hwc.comp (contDiff_const.add T.contDiff).contDiffOn (fun y hy => hy)
  have hjetu : ∀ j < k, iteratedFDeriv ℝ j u 0 = 0 := by
    intro j hj
    ext m
    rw [iteratedFDeriv_affine_comp_R3AW, hjet j hj]
    simp
  obtain ⟨ε, W, hε, hcb, hWd, hpolar, hWzero, hper⟩ :=
    exists_smooth_polar_blowup_of_vanishing_jets hΩ h0Ω hk hu hjetu
  have hkfac : ((k.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hc : (k.factorial : ℝ)⁻¹ * A₀ ≠ 0 := mul_ne_zero (inv_ne_zero hkfac) hA₀.ne'
  have hW0 : ∀ θ : ℝ, W (0, θ) = (k.factorial : ℝ)⁻¹ * A₀ * Real.sin (k * (θ - θ₀)) := by
    intro θ
    rw [hWzero θ, smul_eq_mul, iteratedFDeriv_affine_comp_R3AW]
    have := hsin (θ - θ₀)
    simp only [add_sub_cancel] at this
    rw [this]
    ring
  obtain ⟨ρ₁, hρ₁, hρ₁ε, ϑ, hϑ0, hϑC, hϑW, hsep, hcov⟩ :=
    polar_root_arcs_R3AW hε hWd hper hk hc hW0
  have hbl : ∀ r θ : ℝ, |r| < ε → w (arcPointR3AW T p r θ) = r ^ k * W (r, θ) := by
    intro r θ hr
    have := hpolar r θ hr
    simp only [u, zero_add, Complex.real_smul] at this
    exact this
  set ρ : ℝ := ρ₁ / 2 with hρ
  have hρpos : 0 < ρ := half_pos hρ₁
  have hρρ₁ : ρ < ρ₁ := half_lt_self hρ₁
  let Γ : Fin (2 * k) → ℝ → ℂ := fun m r => arcPointR3AW T p r (ϑ m r)
  let V : Set ℂ := {z | ‖T.symm (z - p)‖ < ρ}
  have hVo : IsOpen V :=
    isOpen_lt (continuous_norm.comp (T.symm.continuous.comp
      (continuous_id.sub continuous_const))) continuous_const
  have hpV : p ∈ V := by
    change ‖T.symm (p - p)‖ < ρ
    simpa using hρpos
  have hVO : V ⊆ O := by
    intro z hz
    have hyε : T.symm (z - p) ∈ closedBall (0 : ℂ) ε := by
      rw [mem_closedBall, dist_zero_right]
      exact (le_of_lt hz).trans (hρρ₁.le.trans hρ₁ε)
    have h2 : p + T (T.symm (z - p)) ∈ O := hcb hyε
    rwa [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel] at h2
  have hIccρ : ∀ r ∈ Icc (0 : ℝ) ρ, |r| < ρ₁ := fun r hr => by
    rw [abs_of_nonneg hr.1]
    exact hr.2.trans_lt hρρ₁
  have hϑat : ∀ m r, |r| < ρ₁ → HasDerivAt (ϑ m) (deriv (ϑ m) r) r := by
    intro m r hr
    have hmem := abs_lt.mp hr
    have hca : ContDiffAt ℝ ∞ (ϑ m) r := (hϑC m).contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
    exact (hca.differentiableAt (by simp)).hasDerivAt
  have hΓd : ∀ m r, |r| < ρ₁ → HasDerivAt (Γ m) (T (Complex.exp (((ϑ m r : ℝ) : ℂ) *
      Complex.I) * (1 + ((r * deriv (ϑ m) r : ℝ) : ℂ) * Complex.I))) r :=
    fun m r hr => hasDerivAt_arcPoint_R3AW T p (hϑat m r hr)
  have hΓnorm : ∀ m r, ‖T.symm (Γ m r - p)‖ = |r| := fun m r => norm_symm_arcPoint_R3AW T p r _
  have hΓ0 : ∀ m, Γ m 0 = p := fun m => arcPoint_zero_R3AW T p _
  -- 零点的弧分解
  have hdecomp : ∀ z ∈ V, w z = 0 → z ≠ p → ∃ m, ∃ r ∈ Ioo 0 ρ, z = Γ m r := by
    intro z hz hwz hzp
    set y : ℂ := T.symm (z - p) with hy
    have hzy : z = arcPointR3AW T p ‖y‖ y.arg := by
      have h1 : ((‖y‖ : ℝ) : ℂ) * Complex.exp ((y.arg : ℂ) * Complex.I) = y :=
        Complex.norm_mul_exp_arg_mul_I y
      unfold arcPointR3AW
      rw [h1, hy, ContinuousLinearEquiv.apply_symm_apply]
      abel
    have hy0 : y ≠ 0 := by
      intro h0
      apply hzp
      have : z - p = 0 := by
        have := congrArg T h0
        simpa [hy] using this
      exact sub_eq_zero.mp this
    have hrpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hrρ : ‖y‖ < ρ := hz
    have hrρ₁ : ‖y‖ < ρ₁ := hrρ.trans hρρ₁
    have habs : |‖y‖| < ε := by
      rw [abs_of_nonneg (norm_nonneg y)]
      exact hrρ₁.trans_le hρ₁ε
    have hWz : W (‖y‖, y.arg) = 0 := by
      have h1 := hbl ‖y‖ y.arg habs
      rw [← hzy, hwz] at h1
      have hpow : ‖y‖ ^ k ≠ 0 := pow_ne_zero _ hrpos.ne'
      exact (mul_eq_zero.mp h1.symm).resolve_left hpow
    obtain ⟨m, n, hmn⟩ := hcov ‖y‖ (norm_nonneg y) hrρ₁ y.arg hWz
    refine ⟨m, ‖y‖, ⟨hrpos, hrρ⟩, ?_⟩
    rw [hzy]
    simp only [Γ, arcPointR3AW]
    congr 3
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨n, ?_⟩
    rw [hmn]
    push_cast
    ring
  have hGw : ∀ m r, |r| < ρ₁ → w (Γ m r) = 0 := by
    intro m r hr
    have := hbl r (ϑ m r) (hr.trans_le hρ₁ε)
    rw [(hϑW m r hr).1, mul_zero] at this
    exact this
  have hWopen : IsOpen {q : ℝ × ℝ | |q.1| < ε} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  refine ⟨k, hk, hjet, hjk, V, T, 1, θ₀, ρ, Γ, hVo, hpV, hVO, one_pos, hρpos, hnorm,
    ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨hΓ0 m, ?_, ?_, ?_, ?_, ?_⟩
    · have hmul : ContDiffOn ℝ ∞ (fun r : ℝ =>
          ((r : ℂ) * Complex.exp (((ϑ m r : ℝ) : ℂ) * Complex.I))) (Ioo (-ρ₁) ρ₁) :=
        (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_id).mul
          (Complex.contDiff_exp.comp_contDiffOn
            ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hϑC m)).mul contDiffOn_const))
      have hI : ContDiffOn ℝ ∞ (Γ m) (Ioo (-ρ₁) ρ₁) :=
        contDiffOn_const.add (T.contDiff.comp_contDiffOn hmul)
      refine (hI.mono ?_).of_le (by exact_mod_cast le_top)
      intro r hr
      have := hIccρ r hr
      exact abs_lt.mp this
    · intro r hr r' hr' h
      have := congrArg (fun z => ‖T.symm (z - p)‖) h
      simp only [hΓnorm, abs_of_nonneg hr.1, abs_of_nonneg hr'.1] at this
      exact this
    · intro r hr
      have hd := (hΓd m r (hIccρ r hr)).hasDerivWithinAt (s := Icc 0 ρ)
      rw [hd.derivWithin (uniqueDiffOn_Icc hρpos r hr)]
      exact arcDeriv_ne_zero_R3AW T _ _
    · have hd := (hΓd m 0 (by simpa using hρ₁)).hasDerivWithinAt (s := Icc 0 ρ)
      convert hd using 2
      rw [hϑ0 m]
      simp
    · intro r hr
      change ‖T.symm (Γ m r - p)‖ < ρ
      rw [hΓnorm, abs_of_nonneg hr.1]
      exact hr.2
  · intro m m' hmm r hr r' hr' h
    have hnr : r = r' := by
      have := congrArg (fun z => ‖T.symm (z - p)‖) h
      simp only [hΓnorm, abs_of_nonneg hr.1, abs_of_nonneg hr'.1] at this
      exact this
    subst hnr
    have hr0 : r = 0 := by
      by_contra hne
      have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hne)
      have h1 : T ((r : ℂ) * Complex.exp (((ϑ m r : ℝ) : ℂ) * Complex.I)) =
          T ((r : ℂ) * Complex.exp (((ϑ m' r : ℝ) : ℂ) * Complex.I)) := by
        have := h
        simp only [Γ, arcPointR3AW] at this
        exact add_left_cancel this
      have h2 := T.injective h1
      have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
      have h3 := mul_left_cancel₀ hr' h2
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h3
      apply hsep m m' hmm r (hIccρ r hr) n
      have h4 : ((ϑ m r : ℝ) : ℂ) = ((ϑ m' r + 2 * Real.pi * n : ℝ) : ℂ) := by
        have h5 : (((ϑ m r : ℝ) : ℂ) - ((ϑ m' r + 2 * Real.pi * n : ℝ) : ℂ)) * Complex.I = 0 := by
          push_cast
          rw [sub_mul]
          linear_combination hn
        have := (mul_eq_zero.mp h5).resolve_right Complex.I_ne_zero
        exact sub_eq_zero.mp this
      exact_mod_cast h4
    exact ⟨hr0, hr0⟩
  · intro z hz
    constructor
    · intro hwz
      by_cases hzp : z = p
      · exact ⟨⟨0, by omega⟩, 0, ⟨le_rfl, hρpos⟩, by rw [hΓ0]; exact hzp⟩
      · obtain ⟨m, r, hr, hzr⟩ := hdecomp z hz hwz hzp
        exact ⟨m, r, ⟨hr.1.le, hr.2⟩, hzr⟩
    · rintro ⟨m, r, hr, rfl⟩
      exact hGw m r (hIccρ r ⟨hr.1, hr.2.le⟩)
  · intro z hz hwz hzp
    obtain ⟨m, r, hr, rfl⟩ := hdecomp z hz hwz hzp
    have hrρ₁ : |r| < ρ₁ := hIccρ r ⟨hr.1.le, hr.2.le⟩
    have hrε : |r| < ε := hrρ₁.trans_le hρ₁ε
    have hwdiff : DifferentiableAt ℝ w (Γ m r) := (hwa _ (hVO hz)).differentiableAt
    have hcurve := hasDerivAt_arcPoint_angle_R3AW T p r (ϑ m r)
    have hwc := hwdiff.hasFDerivAt.comp_hasDerivAt (ϑ m r) hcurve
    have hfun : (w ∘ fun s : ℝ => arcPointR3AW T p r s) = fun s => r ^ k * W (r, s) :=
      funext fun s => hbl r s hrε
    rw [hfun] at hwc
    have hWdiff : DifferentiableAt ℝ W (r, ϑ m r) :=
      (hWd.contDiffAt (hWopen.mem_nhds hrε)).differentiableAt (by simp)
    have hl : HasDerivAt (fun s : ℝ => (r, s)) ((0 : ℝ), (1 : ℝ)) (ϑ m r) :=
      HasDerivAt.prodMk (hasDerivAt_const (ϑ m r) r) (hasDerivAt_id (ϑ m r))
    have hWc := (hWdiff.hasFDerivAt.comp_hasDerivAt (ϑ m r) hl).const_mul (r ^ k)
    have huniq := hwc.unique hWc
    intro hf
    have hndeg := (hϑW m r hrρ₁).2
    rw [hf] at huniq
    simp only [zero_apply] at huniq
    exact mul_ne_zero (pow_ne_zero _ hr.1.ne') hndeg huniq.symm

/-- consumer：`IsNodalHalfArcsAt_R3AW` ⇒ 切点任意近处存在 regular（transverse）零点——R10.4 / R14 要用的推论。 -/
theorem exists_regular_zero_near_of_nodal_R3AW {O : Set ℂ} {a : Fin 2 → Fin 2 → ℂ → ℝ}
    {w : ℂ → ℝ} {p : ℂ} (h : IsNodalHalfArcsAt_R3AW O a w p) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ O, z ≠ p ∧ dist z p < ε ∧ w z = 0 ∧ fderiv ℝ w z ≠ 0 := by
  obtain ⟨k, hk, -, -, V, T, lam, θ₀, ρ, Γ, hV, hpV, hVO, -, hρ, -, harc, -, hiff, hreg⟩ := h
  have m0 : Fin (2 * k) := ⟨0, by omega⟩
  obtain ⟨h0, hC, hinj, -, -, hmaps⟩ := harc m0
  have hcont : ContinuousWithinAt (Γ m0) (Icc 0 ρ) 0 :=
    (hC.continuousOn) 0 ⟨le_rfl, hρ.le⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp hcont ε hε
  set r : ℝ := min (δ / 2) (ρ / 2) with hr
  have hrpos : 0 < r := lt_min (half_pos hδ) (half_pos hρ)
  have hrρ : r < ρ := (min_le_right _ _).trans_lt (half_lt_self hρ)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hrI : r ∈ Ico 0 ρ := ⟨hrpos.le, hrρ⟩
  have hzV : Γ m0 r ∈ V := hmaps hrI
  have hw0 : w (Γ m0 r) = 0 := (hiff _ hzV).mpr ⟨m0, r, hrI, rfl⟩
  have hne : Γ m0 r ≠ p := by
    intro heq
    have := hinj ⟨hrpos.le, hrρ.le⟩ ⟨le_rfl, hρ.le⟩ (heq.trans h0.symm)
    exact hrpos.ne' this
  refine ⟨Γ m0 r, hVO hzV, hne, ?_, hw0, hreg _ hzV hw0 hne⟩
  have := hδ' ⟨hrpos.le, hrρ.le⟩ (by simpa [Real.dist_eq, abs_of_pos hrpos] using hrδ)
  simpa [h0] using this

end DifferentialGeometry.Analysis

end
