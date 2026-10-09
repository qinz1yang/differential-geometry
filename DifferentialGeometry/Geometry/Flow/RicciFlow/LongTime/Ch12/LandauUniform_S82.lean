import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DefectJetsLandau_S67

set_option autoImplicit false

/-!
# CH12-S82 / G2: the Landau chain with an explicit, `d`-independent threshold

`landau_small_all_S67` has the quantifier order `∀ d … ∃ η₀`; the `hWB` shape needs `η₀` BEFORE the
window data `(t, U, f, S')`.  The constants of the chain of S67 are explicit
(`D₀ = 1`, `D_{j+1} = C (√(D_j B) + D_j)`), so we restate it with the closed formula
`landauEta_S82 C B η N` (depends only on `C B η N`).
-/

noncomputable section
namespace GC.LongTime.Ch12

/-- the constants `D_j` of the Landau chain. -/
def landauD_S82 (C B : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => C * (Real.sqrt (landauD_S82 C B j * B) + landauD_S82 C B j)

theorem one_le_landauD_S82 {C B : ℝ} (hC : 1 ≤ C) : ∀ j, 1 ≤ landauD_S82 C B j := by
  intro j
  induction j with
  | zero => simp [landauD_S82]
  | succ j ih =>
    have h1 : 0 ≤ Real.sqrt (landauD_S82 C B j * B) := Real.sqrt_nonneg _
    simp only [landauD_S82]
    nlinarith

/-- the explicit threshold. -/
def landauEta_S82 (C B η : ℝ) (N : ℕ) : ℝ :=
  min 1 ((η / ∑ j ∈ Finset.range (N + 1), landauD_S82 C B j) ^ (2 ^ N))

variable {M : Type*}

theorem landau_induction_uniform_S82 (d : ℕ → ℝ → M → ℝ) (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, d j r x ≤ α) → (∀ x ∈ K j, d (j + 2) r x ≤ β) →
      ∀ x ∈ K (j + 1), d (j + 1) r x ≤ C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0, d j r x ≤ B * r) :
    ∀ j ≤ N, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ ε * r) →
      ∀ r ∈ R, ∀ x ∈ K j, d j r x ≤ landauD_S82 C B j * ε ^ ((1 / 2 : ℝ) ^ j) * r := by
  have hanti : ∀ j, K j ⊆ K 0 := by
    intro j
    induction j with
    | zero => exact subset_rfl
    | succ n ih => exact (hKm n).trans ih
  intro j
  induction j with
  | zero =>
    intro _ ε hε hε1 h0 r hr x hx
    have := h0 r hr x hx
    simpa [Real.rpow_one, landauD_S82] using this
  | succ j ih =>
    intro hj ε hε hε1 h0 r hr x hx
    have hD1 := one_le_landauD_S82 (B := B) hC j
    set D := landauD_S82 C B j with hDdef
    have hD : ∀ r ∈ R, ∀ x ∈ K j, d j r x ≤ D * ε ^ ((1 / 2 : ℝ) ^ j) * r :=
      fun r hr x hx => ih (by omega) ε hε hε1 h0 r hr x hx
    have hr0 := hR r hr
    set q : ℝ := (1 / 2 : ℝ) ^ j with hq
    have hq1 : (1 / 2 : ℝ) ^ (j + 1) = q / 2 := by rw [pow_succ]; ring
    have hα : ∀ y ∈ K j, d j r y ≤ D * ε ^ q * r := fun y hy => hD r hr y hy
    have hβ : ∀ y ∈ K j, d (j + 2) r y ≤ B * r :=
      fun y hy => hcrude (j + 2) (by omega) r hr y (hanti j hy)
    have hα0 : 0 ≤ D * ε ^ q * r := by positivity
    have hβ0 : 0 ≤ B * r := by positivity
    have key := hstep j (by omega) r hr _ _ hα0 hβ0 hα hβ x hx
    have hsq : Real.sqrt (D * ε ^ q * r * (B * r)) = Real.sqrt (D * B) * ε ^ (q / 2) * r := by
      have e1 : D * ε ^ q * r * (B * r) = (D * B) * (ε ^ q) * r ^ 2 := by ring
      rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hr0.le, Real.sqrt_eq_rpow (ε ^ q), ← Real.rpow_mul hε.le]
      congr 3
    have hle : ε ^ q ≤ ε ^ (q / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 (by
        have : 0 ≤ q := by positivity
        linarith)
    rw [hq1]
    change d (j + 1) r x ≤ C * (Real.sqrt (D * B) + D) * ε ^ (q / 2) * r
    calc d (j + 1) r x ≤ C * (Real.sqrt (D * ε ^ q * r * (B * r)) + D * ε ^ q * r) := key
      _ ≤ C * (Real.sqrt (D * B) * ε ^ (q / 2) * r + D * ε ^ (q / 2) * r) := by
        rw [hsq]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have : D * ε ^ q * r ≤ D * ε ^ (q / 2) * r := by
          apply mul_le_mul_of_nonneg_right _ hr0.le
          exact mul_le_mul_of_nonneg_left hle (by linarith)
        linarith
      _ = C * (Real.sqrt (D * B) + D) * ε ^ (q / 2) * r := by ring

theorem landauEta_pos_S82 {C B : ℝ} (hC : 1 ≤ C) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    0 < landauEta_S82 C B η N := by
  have hs : 0 < ∑ j ∈ Finset.range (N + 1), landauD_S82 C B j :=
    Finset.sum_pos (fun j _ => lt_of_lt_of_le one_pos (one_le_landauD_S82 (B := B) hC j))
      ⟨0, by simp⟩
  exact lt_min one_pos (pow_pos (div_pos hη hs) _)

/-- **uniform Landau chain**: threshold `landauEta_S82 C B η N` independent of `d, R, K`. -/
theorem landau_small_uniform_S82 (d : ℕ → ℝ → M → ℝ) (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, d j r x ≤ α) → (∀ x ∈ K j, d (j + 2) r x ≤ β) →
      ∀ x ∈ K (j + 1), d (j + 1) r x ≤ C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0, d j r x ≤ B * r) {η : ℝ} (hη : 0 < η) :
    (∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ landauEta_S82 C B η N * r) →
      ∀ j ≤ N, ∀ x ∈ K N, ∀ r ∈ R, d j r x ≤ η * r := by
  intro h0 j hj x hx r hr
  have hanti : ∀ i j, i ≤ j → K j ⊆ K i := fun i j hij => antitone_nat_of_succ_le hKm hij
  have hε := landauEta_pos_S82 (B := B) hC hη N
  have hε1 : landauEta_S82 C B η N ≤ 1 := min_le_left _ _
  have h1 := landau_induction_uniform_S82 d R hR K hKm N hC hB hstep hcrude j hj _ hε hε1 h0 r hr x
    (hanti j N hj hx)
  set Dm := ∑ i ∈ Finset.range (N + 1), landauD_S82 C B i with hDm
  have hD1 := one_le_landauD_S82 (B := B) hC
  have hDmpos : 0 < Dm := Finset.sum_pos (fun i _ => lt_of_lt_of_le one_pos (hD1 i)) ⟨0, by simp⟩
  have hDj : landauD_S82 C B j ≤ Dm :=
    Finset.single_le_sum (f := fun i => landauD_S82 C B i) (fun i _ => by linarith [hD1 i])
      (Finset.mem_range.2 (by omega))
  set ε := landauEta_S82 C B η N with hεdef
  have hexp : ε ^ ((1 / 2 : ℝ) ^ j) ≤ ε ^ ((1 / 2 : ℝ) ^ N) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)
  have hpow : ε ^ ((1 / 2 : ℝ) ^ N) ≤ η / Dm := by
    have h2 : ε ≤ (η / Dm) ^ (2 ^ N) := min_le_right _ _
    calc ε ^ ((1 / 2 : ℝ) ^ N) ≤ ((η / Dm) ^ (2 ^ N)) ^ ((1 / 2 : ℝ) ^ N) :=
          Real.rpow_le_rpow hε.le h2 (by positivity)
      _ = η / Dm := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hη hDmpos).le]
          have : ((2 ^ N : ℕ) : ℝ) * (1 / 2 : ℝ) ^ N = 1 := by
            push_cast
            rw [← mul_pow]; norm_num
          rw [this, Real.rpow_one]
  have hr0 := hR r hr
  calc d j r x ≤ landauD_S82 C B j * ε ^ ((1 / 2 : ℝ) ^ j) * r := h1
    _ ≤ Dm * (η / Dm) * r := by
        apply mul_le_mul_of_nonneg_right _ hr0.le
        exact mul_le_mul hDj (hexp.trans hpow) (by positivity) hDmpos.le
    _ = η * r := by field_simp

end GC.LongTime.Ch12
