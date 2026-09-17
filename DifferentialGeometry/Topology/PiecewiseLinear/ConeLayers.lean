import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineCover

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coneCoeffSet (a b : E) (σ' σ : ℝ) : Set E :=
  {z | ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ σ' ≤ α + β ∧ α + β ≤ σ ∧ z = α • a + β • b}

theorem convexHull_zero_pair (a b : E) :
    convexHull ℝ ({0, a, b} : Set E) = coneCoeffSet a b 0 1 := by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · rintro z (rfl | rfl | rfl)
    · exact ⟨0, 0, le_rfl, le_rfl, by norm_num, by norm_num, by simp⟩
    · exact ⟨1, 0, zero_le_one, le_rfl, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, le_rfl, zero_le_one, by norm_num, by norm_num, by simp⟩
  · rintro z ⟨α, β, hα, hβ, -, hs, rfl⟩ w ⟨α', β', hα', hβ', -, hs', rfl⟩ p q hp hq hpq
    refine ⟨p * α + q * α', p * β + q * β', by positivity, by positivity, by positivity, ?_, ?_⟩
    · nlinarith
    · module
  · rintro z ⟨α, β, hα, hβ, -, hs, rfl⟩
    have h0 : (0 : E) ∈ ({0, a, b} : Set E) := mem_insert _ _
    have ha : a ∈ ({0, a, b} : Set E) := mem_insert_of_mem _ (mem_insert _ _)
    have hb : b ∈ ({0, a, b} : Set E) := mem_insert_of_mem _ (mem_insert_of_mem _ rfl)
    have hsum : α • a + β • b
        = ∑ i : Fin 3, ![1 - α - β, α, β] i • ![(0 : E), a, b] i := by
      simp [Fin.sum_univ_three]
    rw [hsum]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
    · fin_cases i <;> simp <;> linarith
    · rw [Fin.sum_univ_three]
      change (1 - α - β) + α + β = (1 : ℝ)
      ring
    · fin_cases i
      · exact subset_convexHull ℝ _ h0
      · exact subset_convexHull ℝ _ ha
      · exact subset_convexHull ℝ _ hb

theorem convex_coneCoeffSet (a b : E) (σ' σ : ℝ) : Convex ℝ (coneCoeffSet a b σ' σ) := by
  rintro z ⟨α, β, hα, hβ, h1, h2, rfl⟩ w ⟨α', β', hα', hβ', h1', h2', rfl⟩ p q hp hq hpq
  refine ⟨p * α + q * α', p * β + q * β', by positivity, by positivity, ?_, ?_, by module⟩
  · nlinarith
  · nlinarith

theorem mem_coneCoeffSet_smul (a b : E) {σ' σ t : ℝ} (ht' : σ' ≤ t) (ht : t ≤ σ) (hσ' : 0 ≤ σ') :
    t • a ∈ coneCoeffSet a b σ' σ ∧ t • b ∈ coneCoeffSet a b σ' σ := by
  have ht0 : 0 ≤ t := le_trans hσ' ht'
  exact ⟨⟨t, 0, ht0, le_rfl, by linarith, by linarith, by simp⟩,
    ⟨0, t, le_rfl, ht0, by linarith, by linarith, by simp⟩⟩

theorem coneCoeffSet_subset_convexHull (a b : E) {σ' σ : ℝ} (hσ' : 0 ≤ σ') (hσ : σ' ≤ σ) :
    coneCoeffSet a b σ' σ ⊆ convexHull ℝ ({σ' • a, σ' • b, σ • a, σ • b} : Set E) := by
  rintro z ⟨α, β, hα, hβ, h1, h2, rfl⟩
  have hS : ∀ x ∈ ({σ' • a, σ' • b, σ • a, σ • b} : Set E),
      x ∈ convexHull ℝ ({σ' • a, σ' • b, σ • a, σ • b} : Set E) := fun x hx =>
    subset_convexHull ℝ _ hx
  rcases eq_or_lt_of_le (le_trans hσ' h1) with hτ | hτ
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    have hσ'0 : σ' = 0 := le_antisymm (by linarith) hσ'
    rw [hα0, hβ0]
    have : (0 : ℝ) • a + (0 : ℝ) • b = σ' • a := by rw [hσ'0]; simp
    rw [this]
    exact hS _ (mem_insert _ _)
  · set τ := α + β with hτdef
    set μ : ℝ := if σ = σ' then 0 else (τ - σ') / (σ - σ') with hμdef
    have hμ0 : 0 ≤ μ := by
      rw [hμdef]
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (by linarith) (by cases lt_or_eq_of_le hσ with
          | inl hl => linarith
          | inr hr => exact absurd hr.symm h)
    have hμ1 : μ ≤ 1 := by
      rw [hμdef]
      split_ifs with h
      · exact zero_le_one
      · rw [div_le_one (by cases lt_or_eq_of_le hσ with
          | inl hl => linarith
          | inr hr => exact absurd hr.symm h)]
        linarith
    have hkey : (1 - μ) * σ' + μ * σ = τ := by
      rw [hμdef]
      split_ifs with h
      · have hτσ : τ = σ' := le_antisymm (h ▸ h2) h1
        rw [hτσ]
        ring
      · have hne : σ - σ' ≠ 0 := by
          cases lt_or_eq_of_le hσ with
          | inl hl => exact sub_ne_zero.mpr (ne_of_gt hl)
          | inr hr => exact absurd hr.symm h
        field_simp
        ring
    have hτ0 : τ ≠ 0 := ne_of_gt hτ
    have e1 : (1 - μ) * α / τ * σ' + μ * α / τ * σ = α := by
      field_simp
      nlinarith [hkey]
    have e2 : (1 - μ) * β / τ * σ' + μ * β / τ * σ = β := by
      field_simp
      nlinarith [hkey]
    have hsum : α • a + β • b
        = ∑ i : Fin 4, ![(1 - μ) * α / τ, (1 - μ) * β / τ, μ * α / τ, μ * β / τ] i •
            ![σ' • a, σ' • b, σ • a, σ • b] i := by
      rw [Fin.sum_univ_four]
      have hexp : ((1 - μ) * α / τ) • (σ' • a) + ((1 - μ) * β / τ) • (σ' • b)
          + (μ * α / τ) • (σ • a) + (μ * β / τ) • (σ • b)
          = ((1 - μ) * α / τ * σ' + μ * α / τ * σ) • a
            + ((1 - μ) * β / τ * σ' + μ * β / τ * σ) • b := by module
      change α • a + β • b = ((1 - μ) * α / τ) • (σ' • a) + ((1 - μ) * β / τ) • (σ' • b)
        + (μ * α / τ) • (σ • a) + (μ * β / τ) • (σ • b)
      rw [hexp, e1, e2]
    rw [hsum]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
    · fin_cases i <;>
        first
        | positivity
        | exact div_nonneg (by nlinarith) hτ.le
    · rw [Fin.sum_univ_four]
      change (1 - μ) * α / τ + (1 - μ) * β / τ + μ * α / τ + μ * β / τ = (1 : ℝ)
      field_simp
      ring
    · fin_cases i
      · exact hS _ (mem_insert _ _)
      · exact hS _ (mem_insert_of_mem _ (mem_insert _ _))
      · exact hS _ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert _ _)))
      · exact hS _ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert_of_mem _ rfl)))

theorem coneCoeffSet_eq_convexHull (a b : E) {σ' σ : ℝ} (hσ' : 0 ≤ σ') (hσ : σ' ≤ σ) :
    coneCoeffSet a b σ' σ = convexHull ℝ ({σ' • a, σ' • b, σ • a, σ • b} : Set E) := by
  refine Subset.antisymm (coneCoeffSet_subset_convexHull a b hσ' hσ) ?_
  refine convexHull_min ?_ (convex_coneCoeffSet a b σ' σ)
  rintro x (rfl | rfl | rfl | rfl)
  · exact (mem_coneCoeffSet_smul a b le_rfl hσ hσ').1
  · exact (mem_coneCoeffSet_smul a b le_rfl hσ hσ').2
  · exact (mem_coneCoeffSet_smul a b hσ le_rfl hσ').1
  · exact (mem_coneCoeffSet_smul a b hσ le_rfl hσ').2

theorem coneCoeffSet_union (a b : E) {σ₀ σ₁ σ₂ : ℝ} (h01 : σ₀ ≤ σ₁) (h12 : σ₁ ≤ σ₂) :
    coneCoeffSet a b σ₀ σ₁ ∪ coneCoeffSet a b σ₁ σ₂ = coneCoeffSet a b σ₀ σ₂ := by
  refine Subset.antisymm ?_ ?_
  · rintro z (⟨α, β, hα, hβ, h1, h2, rfl⟩ | ⟨α, β, hα, hβ, h1, h2, rfl⟩)
    · exact ⟨α, β, hα, hβ, h1, by linarith, rfl⟩
    · exact ⟨α, β, hα, hβ, by linarith, h2, rfl⟩
  · rintro z ⟨α, β, hα, hβ, h1, h2, rfl⟩
    rcases le_total (α + β) σ₁ with h | h
    · exact Or.inl ⟨α, β, hα, hβ, h1, h, rfl⟩
    · exact Or.inr ⟨α, β, hα, hβ, h, h2, rfl⟩

theorem le_of_chain {σ : ℕ → ℝ} {N : ℕ} (hmono : ∀ k ≤ N, σ k ≤ σ (k + 1)) :
    ∀ j ≤ N + 1, ∀ i ≤ j, σ i ≤ σ j := by
  intro j
  induction j with
  | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
  | succ j ih =>
    intro hj i hi
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact (ih (by omega) i (by omega)).trans (hmono j (by omega))
    · rw [Nat.le_antisymm hi hge]

theorem coneCoeffSet_biUnion (a b : E) (σ : ℕ → ℝ) (N : ℕ)
    (hmono : ∀ k ≤ N, σ k ≤ σ (k + 1)) :
    ⋃ k ∈ Finset.range (N + 1), coneCoeffSet a b (σ k) (σ (k + 1))
      = coneCoeffSet a b (σ 0) (σ (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert,
      ih (fun k hk => hmono k (by omega)), union_comm]
    exact coneCoeffSet_union a b (le_of_chain (fun k hk => hmono k (by omega)) (N + 1)
      le_rfl 0 (Nat.zero_le _)) (hmono (N + 1) le_rfl)

end DifferentialGeometry.Topology.PiecewiseLinear


