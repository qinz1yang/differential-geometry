import Mathlib

set_option autoImplicit false

/-!
# CH12-S66 / G2: iteration of the Landau–Kolmogorov recursion

`a_j ≤ C (√(a_{j-1} a_{j+1}) + a_{j-1})` for `1 ≤ j ≤ N`, `a_0 ≤ ε ≤ 1`, `a_{N+1} ≤ B`
implies `a_j ≤ max 1 B * (2C+1)^((N+1)(N+2)) * ε^(1 - j/(N+1))`.

Proof: max-ratio principle against the barrier `W_j = λ D^{q_j} ε^{θ_j}` with `D = 2C+1`,
`q_j = j (2N+3-j)` (second difference `-2`), `θ_j = 1 - j/(N+1)` (affine).
-/

namespace GC.LongTime.Ch12

theorem iterate_interp_S66 (N : ℕ) (a : ℕ → ℝ) {C B ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ha : ∀ j ≤ N + 1, 0 ≤ a j)
    (hrec : ∀ j, 1 ≤ j → j ≤ N → a j ≤ C * (√(a (j - 1) * a (j + 1)) + a (j - 1)))
    (h0 : a 0 ≤ ε) (hN : a (N + 1) ≤ B) :
    ∀ j ≤ N + 1, a j ≤ max 1 B * (2 * C + 1) ^ ((N + 1) * (N + 2)) *
      ε ^ (1 - (j : ℝ) / (N + 1)) := by
  set lam : ℝ := max 1 B with hlam
  set D : ℝ := 2 * C + 1 with hD
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlamB : B ≤ lam := le_max_right _ _
  have hlampos : 0 < lam := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  set q : ℕ → ℝ := fun j => (j : ℝ) * (2 * N + 3 - j) with hq
  set θ : ℕ → ℝ := fun j => 1 - (j : ℝ) / (N + 1) with hθ
  set W : ℕ → ℝ := fun j => lam * D ^ (q j) * ε ^ (θ j) with hW
  have hWpos : ∀ j, 0 < W j := fun j => by simp only [hW]; positivity
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have key : ∀ j ≤ N + 1, a j ≤ W j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀, hj₀'⟩ := hcon
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (N + 2))
      (fun j => a j / W j) ⟨j₀, by simp; omega⟩
    simp only [Finset.mem_range] at hm hmax
    set R := a m / W m with hR
    have hR1 : 1 < R := by
      have := hmax j₀ (by omega)
      have h1 : 1 < a j₀ / W j₀ := (one_lt_div (hWpos j₀)).2 hj₀'
      linarith
    have hRpos : 0 < R := by linarith
    have hratio : ∀ j ≤ N + 1, a j ≤ R * W j := fun j hj =>
      (div_le_iff₀ (hWpos j)).1 (hmax j (by omega))
    have ham : a m = R * W m := by rw [hR]; exact (div_mul_cancel₀ _ (hWpos m).ne').symm
    have hm' : m ≤ N + 1 := by omega
    by_cases hm0 : m = 0
    · subst hm0
      have hW0 : ε ≤ W 0 := by
        simp only [hW, hq, hθ]
        simp
        nlinarith
      have : a 0 ≤ W 0 := h0.trans hW0
      have h2 : R ≤ 1 := by
        rw [hR, div_le_one (hWpos 0)]; exact this
      linarith
    by_cases hmN : m = N + 1
    · subst hmN
      have hWN : B ≤ W (N + 1) := by
        have hq0 : (0 : ℝ) ≤ q (N + 1) := by
          simp only [hq]; push_cast; nlinarith
        have h1 : 1 ≤ D ^ (q (N + 1)) := Real.one_le_rpow hD1 hq0
        have h2 : θ (N + 1) = 0 := by simp only [hθ]; push_cast; field_simp; ring
        simp only [hW, h2, Real.rpow_zero, mul_one]
        calc B ≤ lam := hlamB
          _ = lam * 1 := (mul_one _).symm
          _ ≤ lam * D ^ (q (N + 1)) := by gcongr
      have : a (N + 1) ≤ W (N + 1) := hN.trans hWN
      have h2 : R ≤ 1 := by
        rw [hR, div_le_one (hWpos _)]; exact this
      linarith
    -- interior index m = k + 1, 1 ≤ m ≤ N
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hkN : k + 1 ≤ N := by omega
    have hr := hrec (k + 1) (by omega) hkN
    simp only [Nat.add_sub_cancel] at hr
    have hak := hratio k (by omega)
    have hak2 := hratio (k + 2) (by omega)
    have hak0 := ha k (by omega)
    have hak20 := ha (k + 2) (by omega)
    set X : ℝ := D ^ (q (k + 1) - 1) with hX
    set Y : ℝ := ε ^ (θ (k + 1)) with hY
    have hXpos : 0 < X := by simp only [hX]; positivity
    have hYpos : 0 < Y := by simp only [hY]; positivity
    have hkf : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkN
    -- exponent identities
    have hq1 : q k + q (k + 2) = (q (k + 1) - 1) + (q (k + 1) - 1) := by
      simp only [hq]; push_cast; ring
    have hθ1 : θ k + θ (k + 2) = θ (k + 1) + θ (k + 1) := by
      simp only [hθ]; push_cast; ring
    have hWW : W k * W (k + 2) = (lam * X * Y) ^ 2 := by
      have e1 : D ^ (q k) * D ^ (q (k + 2)) = X * X := by
        rw [← Real.rpow_add hDpos, hq1, Real.rpow_add hDpos]
      have e2 : ε ^ (θ k) * ε ^ (θ (k + 2)) = Y * Y := by
        rw [← Real.rpow_add hε, hθ1, Real.rpow_add hε]
      simp only [hW]
      calc lam * D ^ q k * ε ^ θ k * (lam * D ^ q (k + 2) * ε ^ θ (k + 2))
          = lam * lam * (D ^ (q k) * D ^ (q (k + 2))) * (ε ^ (θ k) * ε ^ (θ (k + 2))) := by ring
        _ = (lam * X * Y) ^ 2 := by rw [e1, e2]; ring
    have hsq : √(a k * a (k + 2)) ≤ R * (lam * X * Y) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc a k * a (k + 2) ≤ (R * W k) * (R * W (k + 2)) := by gcongr
        _ = R ^ 2 * (W k * W (k + 2)) := by ring
        _ = (R * (lam * X * Y)) ^ 2 := by rw [hWW]; ring
    have hWk : W k ≤ lam * X * Y := by
      have e1 : D ^ (q k) ≤ X :=
        Real.rpow_le_rpow_of_exponent_le hD1 (by simp only [hq]; push_cast; nlinarith)
      have e2 : ε ^ (θ k) ≤ Y :=
        Real.rpow_le_rpow_of_exponent_ge hε hε1 (by simp only [hθ]; push_cast; apply le_of_sub_nonneg; field_simp; linarith)
      simp only [hW]
      gcongr
    have hWm : W (k + 1) = lam * (D * X) * Y := by
      have e : D ^ (q (k + 1)) = D * X := by
        have h1 := Real.rpow_add hDpos (q (k + 1) - 1) 1
        rw [Real.rpow_one] at h1
        calc D ^ (q (k + 1)) = D ^ ((q (k + 1) - 1) + 1) := by congr 1; ring
          _ = D * X := by rw [h1, mul_comm]
      simp only [hW]; rw [e]
    have hr' : a (k + 1) ≤ C * (√(a k * a (k + 2)) + a k) := hr
    have hak' : a k ≤ R * (lam * X * Y) := hak.trans (mul_le_mul_of_nonneg_left hWk hRpos.le)
    have h3 : a (k + 1) ≤ C * (R * (lam * X * Y) + R * (lam * X * Y)) :=
      hr'.trans (by gcongr)
    have hT : 0 < R * (lam * X * Y) := by positivity
    rw [ham, hWm] at h3
    have h4 : R * (lam * (D * X) * Y) = D * (R * (lam * X * Y)) := by ring
    rw [h4] at h3
    have hD' : D = 2 * C + 1 := hD
    nlinarith
  intro j hj
  have hqle : q j ≤ (((N + 1) * (N + 2) : ℕ) : ℝ) := by
    have hjf : (j : ℝ) ≤ N + 1 := by exact_mod_cast hj
    simp only [hq]; push_cast; nlinarith
  have : D ^ (q j) ≤ D ^ (((N + 1) * (N + 2) : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 hqle
  rw [Real.rpow_natCast] at this
  calc a j ≤ W j := key j hj
    _ = lam * D ^ (q j) * ε ^ (1 - (j : ℝ) / (N + 1)) := rfl
    _ ≤ lam * D ^ ((N + 1) * (N + 2)) * ε ^ (1 - (j : ℝ) / (N + 1)) := by gcongr

end GC.LongTime.Ch12
