import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DuhamelWindow_S57

set_option autoImplicit false

/-!
# CH12-S67 / G2a: W-B2 reduced to a one-step interpolation (iteration + choice of `η₀`)

The defect jets `d j r x := sqrt normSq0S h x (j+2) (defectJet_S57 S h j r x)` are small at every order `≤ N`
once the `C⁰` defect is `≤ η₀ r` and (i) all orders `≤ N+1` are crudely bounded by `B r` (`hcrude`),
(ii) the one-step Landau-Kolmogorov inequality `hstep` (order `j+1` from orders `j`, `j+2`, losing a neighbourhood
`K j ⊇ K (j+1)`) holds.  This file is the *pure real* part: induction on the order with exponent `(1/2)^j`
(`landau_induction_S67`), then the choice of `η₀` (`defectJet_small_of_landau_S67`).  `hstep` (the
manifold Landau inequality for `∇_h`-derivatives of the tensor `g_r + 2 r Ric g_r`) and `hcrude`
(Shi + `ric_bound_field_on`) are the geometric inputs (see `[FROZEN] CH12-S67 W-B2`).
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

section Pure

variable {M : Type*}

/-- chain induction: `d 0 ≤ ε r` and the one-step inequality give `d j ≤ D_j ε^{(1/2)^j} r` on `K j`. -/
theorem landau_induction_S67 (d : ℕ → ℝ → M → ℝ) (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, d j r x ≤ α) → (∀ x ∈ K j, d (j + 2) r x ≤ β) →
      ∀ x ∈ K (j + 1), d (j + 1) r x ≤ C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0, d j r x ≤ B * r) :
    ∀ j ≤ N, ∃ D : ℝ, 1 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ ε * r) →
      ∀ r ∈ R, ∀ x ∈ K j, d j r x ≤ D * ε ^ ((1 / 2 : ℝ) ^ j) * r := by
  have hanti : ∀ j, K j ⊆ K 0 := by
    intro j
    induction j with
    | zero => exact subset_rfl
    | succ n ih => exact (hKm n).trans ih
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨1, le_rfl, fun ε hε hε1 h0 r hr x hx => ?_⟩
    have := h0 r hr x hx
    simpa [Real.rpow_one] using this
  | succ j ih =>
    intro hj
    obtain ⟨D, hD1, hD⟩ := ih (by omega)
    refine ⟨C * (Real.sqrt (D * B) + D), ?_, fun ε hε hε1 h0 r hr x hx => ?_⟩
    · have h1 : 0 ≤ Real.sqrt (D * B) := Real.sqrt_nonneg _
      nlinarith
    · have hr0 := hR r hr
      set q : ℝ := (1 / 2 : ℝ) ^ j with hq
      have hq1 : (1 / 2 : ℝ) ^ (j + 1) = q / 2 := by rw [pow_succ]; ring
      have hα : ∀ y ∈ K j, d j r y ≤ D * ε ^ q * r := fun y hy => hD ε hε hε1 h0 r hr y hy
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
      calc d (j + 1) r x ≤ C * (Real.sqrt (D * ε ^ q * r * (B * r)) + D * ε ^ q * r) := key
        _ ≤ C * (Real.sqrt (D * B) * ε ^ (q / 2) * r + D * ε ^ (q / 2) * r) := by
          rw [hsq]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have : D * ε ^ q * r ≤ D * ε ^ (q / 2) * r := by
            apply mul_le_mul_of_nonneg_right _ hr0.le
            exact mul_le_mul_of_nonneg_left hle (by linarith)
          linarith
        _ = C * (Real.sqrt (D * B) + D) * ε ^ (q / 2) * r := by ring

/-- the choice of `η₀`: for every `η > 0` there is `η₀ > 0` with `d 0 ≤ η₀ r ⇒ d N ≤ η r`. -/
theorem landau_small_S67 (d : ℕ → ℝ → M → ℝ) (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, d j r x ≤ α) → (∀ x ∈ K j, d (j + 2) r x ≤ β) →
      ∀ x ∈ K (j + 1), d (j + 1) r x ≤ C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0, d j r x ≤ B * r) (η : ℝ) (hη : 0 < η) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ((∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ η₀ * r) →
      ∀ x ∈ K N, ∀ r ∈ R, d N r x ≤ η * r) := by
  obtain ⟨D, hD1, hD⟩ := landau_induction_S67 d R hR K hKm N hC hB hstep hcrude N le_rfl
  have hq : 0 < (1 / 2 : ℝ) ^ N := by positivity
  have hD0 : 0 < D := by linarith
  set q : ℝ := (1 / 2 : ℝ) ^ N with hqdef
  refine ⟨min 1 ((η / D) ^ (1 / q)), lt_min one_pos (by positivity), fun h0 x hx r hr => ?_⟩
  have hε0 : 0 < min 1 ((η / D) ^ (1 / q)) := lt_min one_pos (by positivity)
  have := hD _ hε0 (min_le_left _ _) h0 r hr x hx
  have hr0 := hR r hr
  have hpow : (min 1 ((η / D) ^ (1 / q))) ^ q ≤ η / D := by
    calc (min 1 ((η / D) ^ (1 / q))) ^ q ≤ ((η / D) ^ (1 / q)) ^ q :=
          Real.rpow_le_rpow hε0.le (min_le_right _ _) hq.le
      _ = η / D := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hq.ne', Real.rpow_one]
  calc d N r x ≤ D * (min 1 ((η / D) ^ (1 / q))) ^ q * r := this
    _ ≤ D * (η / D) * r := by
        apply mul_le_mul_of_nonneg_right _ hr0.le
        exact mul_le_mul_of_nonneg_left hpow hD0.le
    _ = η * r := by field_simp

end Pure

section Concrete

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
/-- **W-B2 reduced** (the shape consumed by `rescaled_metricDerivNorm_duhamel_S57` as `hdef`).
Inputs: `hstep` (one-step manifold Landau inequality for the defect tensor `g_r + 2 r Ric g_r`),
`hcrude` (all defect jets of order `≤ N+1` are `≤ B r`); `hC0` (C⁰ defect `≤ η₀ r`) is the antecedent. -/
theorem defectJet_small_of_landau_S67 {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (h : SmoothRiemannianMetric I M)
    (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ)
    {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ α) →
      (∀ x ∈ K j, Real.sqrt (normSq0S h x (j + 2 + 2) (defectJet_S57 S h (j + 2) r x)) ≤ β) →
      ∀ x ∈ K (j + 1),
        Real.sqrt (normSq0S h x (j + 1 + 2) (defectJet_S57 S h (j + 1) r x)) ≤
          C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0,
      Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ B * r)
    (η : ℝ) (hη : 0 < η) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ((∀ r ∈ R, ∀ x ∈ K 0, Real.sqrt (normSq0S h x (0 + 2) (defectJet_S57 S h 0 r x)) ≤ η₀ * r) →
      ∀ x ∈ K N, ∀ r ∈ R, Real.sqrt (normSq0S h x (N + 2) (defectJet_S57 S h N r x)) ≤ η * r) :=
  landau_small_S67 (fun j r x => Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)))
    R hR K hKm N hC hB hstep hcrude η hη

end Concrete

end GC.LongTime.Ch12
