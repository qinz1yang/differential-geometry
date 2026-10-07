import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Interpolation_S66
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InterpIter_S66

set_option autoImplicit false

/-!
# CH12-S66 / G3: Landau–Kolmogorov interpolation for `iteratedFDeriv` on a ball

`landau_step_S66`: one step along line segments `s ↦ x + s • v`, `‖v‖ ≤ 1`, `|s| ≤ r`.
`landau_ball_S66`: with the weights `δ(x) = ρ - dist x x₀` (distance to the boundary of the ball),
the weighted sups `a_j = sup δ^j ‖D^j f‖` satisfy the recursion of `iterate_interp_S66`.
-/

noncomputable section
open Set Metric
namespace GC.LongTime.Ch12

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- one Landau step for `‖D^{n+1} f‖` from `‖D^n f‖` and `‖D^{n+2} f‖` on `closedBall x r ⊆ U`. -/
theorem landau_step_S66 {f : E → F} {U : Set E} (hU : IsOpen U) {n : ℕ}
    (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) {x : E} {r M0 M2 : ℝ} (hr : 0 < r)
    (hseg : ∀ y, dist y x ≤ r → y ∈ U)
    (h0 : ∀ y, dist y x ≤ r → ‖iteratedFDeriv ℝ n f y‖ ≤ M0)
    (h2 : ∀ y, dist y x ≤ r → ‖iteratedFDeriv ℝ (n + 2) f y‖ ≤ M2) :
    ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ 4 * (√(M0 * M2) + M0 / (2 * r)) := by
  set G : E → (E [×n]→L[ℝ] F) := iteratedFDeriv ℝ n f with hG
  have hCD : ∀ y ∈ U, ContDiffAt ℝ 2 G y := fun y hy =>
    (hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (m := 2) (by exact_mod_cast (show 2 + n ≤ n + 2 by omega))
  have hG1 : ∀ y ∈ U, DifferentiableAt ℝ G y := fun y hy =>
    (hCD y hy).differentiableAt (by norm_num)
  have hFG : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
    ((hCD y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx0 : x ∈ U := hseg x (by simp [hr.le])
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans (h0 x (by simp [hr.le]))
  have hM2 : 0 ≤ M2 := (norm_nonneg _).trans (h2 x (by simp [hr.le]))
  -- second derivative of `G` in terms of `D^{n+2} f`
  set Λ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F with hΛ
  have hfd : fderiv ℝ G = fun y => Λ (iteratedFDeriv ℝ (n + 1) f y) := by
    funext y
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp [hΛ, hG]
  have hfd2 : ∀ y, fderiv ℝ (fderiv ℝ G) y =
      (Λ : _ →L[ℝ] _).comp (fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) y) := by
    intro y
    rw [hfd]
    exact LinearIsometryEquiv.comp_fderiv Λ
  have hn2 : ∀ y (v : E), ‖fderiv ℝ (fderiv ℝ G) y v v‖ ≤ ‖iteratedFDeriv ℝ (n + 2) f y‖ * ‖v‖ * ‖v‖ := by
    intro y v
    rw [hfd2 y]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    calc ‖(Λ (fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) y v)) v‖
        ≤ ‖Λ (fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) y v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) y v‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ (‖fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) y‖ * ‖v‖) * ‖v‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (n + 2) f y‖ * ‖v‖ * ‖v‖ := by rw [norm_fderiv_iteratedFDeriv]
  -- the one-dimensional estimate along `x + s • v`
  have hline : ∀ v : E, ‖v‖ ≤ 1 → ‖fderiv ℝ G x v‖ ≤ 4 * (√(M0 * M2) + M0 / (2 * r)) := by
    intro v hv
    have hd : ∀ s ∈ Icc (-r) r, dist (x + s • v) x ≤ r := by
      intro s hs
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have : |s| ≤ r := abs_le.2 ⟨hs.1, hs.2⟩
      calc |s| * ‖v‖ ≤ r * 1 := by gcongr
        _ = r := mul_one r
    have hl : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := by
      intro s
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have hφ : ∀ s ∈ Icc (-r) r, HasDerivWithinAt (fun s : ℝ => G (x + s • v))
        (fderiv ℝ G (x + s • v) v) (Icc (-r) r) s := fun s hs =>
      (((hG1 _ (hseg _ (hd s hs))).hasFDerivAt.comp_hasDerivAt s (hl s))).hasDerivWithinAt
    have hφ' : ∀ s ∈ Icc (-r) r, HasDerivWithinAt (fun s : ℝ => fderiv ℝ G (x + s • v) v)
        (fderiv ℝ (fderiv ℝ G) (x + s • v) v v) (Icc (-r) r) s := by
      intro s hs
      have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ G (x + s • v))
          (fderiv ℝ (fderiv ℝ G) (x + s • v) v) s :=
        (hFG _ (hseg _ (hd s hs))).hasFDerivAt.comp_hasDerivAt s (hl s)
      simpa using (h1.clm_apply (hasDerivAt_const s v)).hasDerivWithinAt
    have h2' : ∀ s ∈ Icc (-r) r, ‖fderiv ℝ (fderiv ℝ G) (x + s • v) v v‖ ≤ M2 := by
      intro s hs
      refine (hn2 _ v).trans ?_
      have a1 := h2 _ (hd s hs)
      have a2 : ‖v‖ * ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v]
      calc ‖iteratedFDeriv ℝ (n + 2) f (x + s • v)‖ * ‖v‖ * ‖v‖
          = ‖iteratedFDeriv ℝ (n + 2) f (x + s • v)‖ * (‖v‖ * ‖v‖) := by ring
        _ ≤ M2 * 1 := by
            gcongr
        _ = M2 := mul_one _
    have := landau_1d_S66 (a := -r) (b := r) (by linarith) hφ hφ' (fun s hs => h0 _ (hd s hs)) h2'
      0 ⟨by linarith, hr.le⟩
    have e : r - -r = 2 * r := by ring
    rw [e] at this
    simpa using this
  have hK : 0 ≤ 4 * (√(M0 * M2) + M0 / (2 * r)) := by positivity
  rw [← norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := n)]
  refine ContinuousLinearMap.opNorm_le_bound _ hK (fun v => ?_)
  by_cases hv : v = 0
  · simp [hv]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
    have := hline _ hu
    rw [map_smul, norm_smul, norm_inv, norm_norm] at this
    have e : ‖fderiv ℝ G x v‖ = ‖v‖ * (‖v‖⁻¹ * ‖fderiv ℝ G x v‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hvn.ne', one_mul]
    have h3 : ‖fderiv ℝ G x v‖ ≤ 4 * (√(M0 * M2) + M0 / (2 * r)) * ‖v‖ := by
      rw [e, mul_comm (4 * (√(M0 * M2) + M0 / (2 * r)))]
      exact mul_le_mul_of_nonneg_left this hvn.le
    exact h3

/-- **G3** Landau–Kolmogorov on a ball (weighted-by-distance-to-the-boundary form). -/
theorem landau_ball_S66 (N : ℕ) {f : E → F} {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ (N + 1) f (ball x₀ ρ)) {A : ℕ → ℝ}
    (hA : ∀ j ≤ N + 1, ∀ y ∈ ball x₀ ρ, ‖iteratedFDeriv ℝ j f y‖ ≤ A j)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (h0 : ∀ y ∈ ball x₀ ρ, ‖f y‖ ≤ ε) :
    ∀ j ≤ N + 1, ∀ x ∈ ball x₀ (ρ / 2), ‖iteratedFDeriv ℝ j f x‖ ≤
      (2 / ρ) ^ j * (max 1 (ρ ^ (N + 1) * A (N + 1)) * (2 * 2 ^ (N + 3) + 1) ^ ((N + 1) * (N + 2))) *
        ε ^ (1 - (j : ℝ) / (N + 1)) := by
  have : Nonempty (ball x₀ ρ) := ⟨⟨x₀, mem_ball_self hρ⟩⟩
  set a : ℕ → ℝ := fun j => ⨆ x : ball x₀ ρ, (ρ - dist (x : E) x₀) ^ j * ‖iteratedFDeriv ℝ j f x‖
    with ha_def
  have hδ : ∀ x : E, x ∈ ball x₀ ρ → 0 < ρ - dist x x₀ := fun x hx => sub_pos.2 (mem_ball.1 hx)
  have hδle : ∀ x : E, ρ - dist x x₀ ≤ ρ := fun x => by linarith [dist_nonneg (x := x) (y := x₀)]
  have hbdd : ∀ j ≤ N + 1, BddAbove (range fun x : ball x₀ ρ =>
      (ρ - dist (x : E) x₀) ^ j * ‖iteratedFDeriv ℝ j f x‖) := by
    intro j hj
    refine ⟨ρ ^ j * A j, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact mul_le_mul (pow_le_pow_left₀ (hδ x x.2).le (hδle x) j) (hA j hj x x.2)
      (norm_nonneg _) (by positivity)
  have hle : ∀ j ≤ N + 1, ∀ x ∈ ball x₀ ρ,
      (ρ - dist x x₀) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ a j := fun j hj x hx =>
    le_ciSup (hbdd j hj) (⟨x, hx⟩ : ball x₀ ρ)
  have ha0 : ∀ j, 0 ≤ a j := fun j =>
    Real.iSup_nonneg (fun x => mul_nonneg (pow_nonneg (hδ x x.2).le _) (norm_nonneg _))
  have hsup_le : ∀ j (K : ℝ), (∀ x ∈ ball x₀ ρ,
      (ρ - dist x x₀) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ K) → a j ≤ K :=
    fun j K h => ciSup_le (fun x => h x x.2)
  have hinv : ∀ j ≤ N + 1, ∀ x ∈ ball x₀ ρ, ∀ s : ℝ, 0 < s → s ≤ ρ - dist x x₀ →
      ‖iteratedFDeriv ℝ j f x‖ ≤ a j * (1 / s) ^ j := by
    intro j hj x hx s hs hsδ
    have h1 : s ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ a j :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hsδ j) (norm_nonneg _)).trans
        (hle j hj x hx)
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hs j)]
    linarith [mul_comm (s ^ j) ‖iteratedFDeriv ℝ j f x‖]
  have hrec : ∀ j, 1 ≤ j → j ≤ N →
      a j ≤ 2 ^ (N + 3) * (√(a (j - 1) * a (j + 1)) + a (j - 1)) := by
    intro j hj1 hjN
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    apply hsup_le
    intro x hx
    set δ := ρ - dist x x₀ with hδdef
    have hδpos : 0 < δ := hδ x hx
    have hcd : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f (ball x₀ ρ) :=
      hf.of_le (by exact_mod_cast (by omega : n + 2 ≤ N + 1))
    have hdist : ∀ y, dist y x ≤ δ / 2 → y ∈ ball x₀ ρ ∧ δ / 2 ≤ ρ - dist y x₀ := by
      intro y hy
      have := dist_triangle y x x₀
      exact ⟨by rw [mem_ball]; linarith, by linarith⟩
    set t : ℝ := 2 / δ with ht
    have hdt : 1 / (δ / 2) = t := by rw [one_div_div]
    have step := landau_step_S66 isOpen_ball hcd (x := x) (r := δ / 2)
      (M0 := a n * t ^ n) (M2 := a (n + 2) * t ^ (n + 2)) (by positivity)
      (fun y hy => (hdist y hy).1)
      (fun y hy => by
        have := hinv n (by omega) y (hdist y hy).1 (δ / 2) (by positivity) (hdist y hy).2
        rwa [hdt] at this)
      (fun y hy => by
        have := hinv (n + 2) (by omega) y (hdist y hy).1 (δ / 2) (by positivity) (hdist y hy).2
        rwa [hdt] at this)
    have hu : 0 ≤ √(a n * a (n + 2)) := Real.sqrt_nonneg _
    have han : 0 ≤ a n := ha0 n
    have htpos : 0 < t := by positivity
    have hδt : δ * t = 2 := by rw [ht]; field_simp
    have h1 : δ ^ (n + 1) * t ^ (n + 1) = 2 ^ (n + 1) := by rw [← mul_pow, hδt]
    have h2 : δ ^ n * t ^ n = 2 ^ n := by rw [← mul_pow, hδt]
    have hsq : √(a n * t ^ n * (a (n + 2) * t ^ (n + 2))) = t ^ (n + 1) * √(a n * a (n + 2)) := by
      have : a n * t ^ n * (a (n + 2) * t ^ (n + 2)) = (t ^ (n + 1)) ^ 2 * (a n * a (n + 2)) := by
        ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg htpos.le _)]
    rw [hsq] at step
    have e1 : δ ^ (n + 1) * (4 * (t ^ (n + 1) * √(a n * a (n + 2)) +
        a n * t ^ n / (2 * (δ / 2)))) =
        4 * ((δ ^ (n + 1) * t ^ (n + 1)) * √(a n * a (n + 2)) + a n * (δ ^ n * t ^ n)) := by
      have : 2 * (δ / 2) = δ := by ring
      rw [this]
      field_simp
      ring
    have hp : (8 : ℝ) * 2 ^ n ≤ 2 ^ (N + 3) := by
      have : (2 : ℝ) ^ (n + 3) ≤ 2 ^ (N + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (8 : ℝ) * 2 ^ n = 2 ^ (n + 3) := by ring
        _ ≤ _ := this
    calc δ ^ (n + 1) * ‖iteratedFDeriv ℝ (n + 1) f x‖
        ≤ δ ^ (n + 1) * (4 * (t ^ (n + 1) * √(a n * a (n + 2)) +
            a n * t ^ n / (2 * (δ / 2)))) := by gcongr
      _ = 4 * (2 ^ (n + 1) * √(a n * a (n + 2)) + a n * 2 ^ n) := by rw [e1, h1, h2]
      _ ≤ 8 * 2 ^ n * (√(a n * a (n + 2)) + a n) := by
          have : (0 : ℝ) ≤ 2 ^ n := by positivity
          have e2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
          rw [e2]
          nlinarith [mul_nonneg this hu, mul_nonneg this han]
      _ ≤ 2 ^ (N + 3) * (√(a n * a (n + 2)) + a n) := by gcongr
  have h0' : a 0 ≤ ε := hsup_le 0 ε (fun x hx => by
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero]; exact h0 x hx)
  have hN' : a (N + 1) ≤ ρ ^ (N + 1) * A (N + 1) := hsup_le _ _ (fun x hx =>
    mul_le_mul (pow_le_pow_left₀ (hδ x hx).le (hδle x) _) (hA _ le_rfl x hx)
      (norm_nonneg _) (by positivity))
  have key := iterate_interp_S66 N a (C := 2 ^ (N + 3)) (B := ρ ^ (N + 1) * A (N + 1))
    (by positivity) hε hε1 (fun j _ => ha0 j) hrec h0' hN'
  intro j hj x hx
  have hxb : x ∈ ball x₀ ρ := ball_subset_ball (by linarith) hx
  have hxd : ρ / 2 ≤ ρ - dist x x₀ := by have := mem_ball.1 hx; linarith
  have h1 := hinv j hj x hxb (ρ / 2) (by positivity) hxd
  have e : 1 / (ρ / 2) = 2 / ρ := by rw [one_div_div]
  rw [e] at h1
  calc ‖iteratedFDeriv ℝ j f x‖ ≤ a j * (2 / ρ) ^ j := h1
    _ ≤ (max 1 (ρ ^ (N + 1) * A (N + 1)) * (2 * 2 ^ (N + 3) + 1) ^ ((N + 1) * (N + 2)) *
          ε ^ (1 - (j : ℝ) / (N + 1))) * (2 / ρ) ^ j := by
        gcongr
        exact key j hj
    _ = _ := by ring

end GC.LongTime.Ch12
